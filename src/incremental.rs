use crate::Compressor;
use LastInput::*;
use Requisite::*;

#[derive(Debug)]
pub struct CapacityExceededError;

/// A fixed-height append-only hash tree that can generate membership proofs for its latest element.
pub trait IncrementalTree<H: Compressor, const HEIGHT: u32> {
    type Membership: MembershipProof<H::T>;

    fn push(&mut self, val: H::T) -> Result<(), CapacityExceededError>;
    fn root(&self) -> H::T;
    fn auth_path(&self) -> Option<Self::Membership>;
}

pub trait MembershipProof<T> {
    fn root(&self) -> T;
}

/// A proof that an element is a member of an ABR.
pub struct AbrMembership<H: Compressor> {
    /// The value whose membership is being proven.
    val: H::T,

    /// The value(s) required to calculate the output of the value's node.
    requisite: Requisite<H::T>,

    /// The position of the element.
    pos: (usize, u32),

    /// A path of values required to calculate the root.
    /// The first tuple member is the sibling, whereas the second is the inner input
    path: Vec<(H::T, H::T)>,
}

impl<H: Compressor> MembershipProof<H::T> for AbrMembership<H> {
    fn root(&self) -> H::T {
        let mut x = self.pos.0;
        let mut acc = match &self.requisite {
            Sibling(sibling) => {
                if x % 2 == 0 {
                    H::compress(&self.val, sibling)
                } else {
                    H::compress(sibling, &self.val)
                }
            }
            Parents(left, right) => H::combine(left, right, &self.val),
        };

        // Account for leaf case; 4 inputs are needed to move to the next layer rather than 2
        if self.pos.1 == 0 {
            x /= 2
        };

        // Traverse from the previous input towards the root
        for (sibling, inner) in &self.path {
            if x % 2 == 0 {
                acc = H::combine(&acc, sibling, inner);
            } else {
                acc = H::combine(sibling, &acc, inner);
            }
            x /= 2;
        }
        acc
    }
}

/// The further values an input needs to calculate the output of its node.
/// For a leaf this is its sibling, for an inner input the parents.
enum Requisite<T> {
    Sibling(T),
    Parents(T, T),
}

/// The last input to an ABR, bundled with the required values to generate a proof of membership.
#[derive(Clone)]
enum LastInput<T> {
    LeftLeaf(T),
    RightLeaf(T, T),
    Inner(T, T, T),
}

impl<T: Default + Clone> LastInput<T> {
    /// Get the value of the previous input
    fn value(&self) -> &T {
        match self {
            LeftLeaf(l) => l,
            RightLeaf(_, r) => r,
            Inner(_, _, i) => i,
        }
    }

    fn requisite(&self) -> Requisite<T> {
        match self {
            LeftLeaf(_) => Sibling(T::default()),
            RightLeaf(l, _) => Sibling(l.clone()),
            Inner(l, r, _) => Parents(l.clone(), r.clone()),
        }
    }
}

struct AbrPosition<const HEIGHT: u32> {
    x: usize,
    y: u32,
}

impl<const HEIGHT: u32> AbrPosition<HEIGHT> {
    fn is_leaf(&self) -> bool {
        self.y == 0
    }

    fn is_left(&self) -> bool {
        self.x % 2 == 0
    }

    fn is_last(&self) -> bool {
        self.y >= HEIGHT - 1
    }

    fn new() -> Self {
        AbrPosition { x: 0, y: 0 }
    }

    // Insertion order goes top to leaves to root if all preqrequisite hashes have been calculated
    // Otherwise necessary inputs closer to the leaves will be inserted first
    fn increment(&mut self) -> Result<(), CapacityExceededError> {
        if self.is_last() {
            return Err(CapacityExceededError);
        }

        if self.is_leaf() {
            if self.x % 4 != 3 {
                self.x += 1
            // Every four leaves we can insert an input one level above
            } else {
                self.x /= 4;
                self.y = 1;
            }
        } else {
            // Return to leaves on even index
            if self.is_left() {
                self.x = (1 + self.x) * 2_usize.pow(1 + self.y);
                self.y = 0;
            // Every second element at an altitude, we can insert the element above
            } else {
                self.x /= 2;
                self.y += 1;
            }
        }
        Ok(())
    }
}

pub struct IncrementalAbr<H: Compressor, const HEIGHT: u32> {
    /// The position of the last added element
    pos: AbrPosition<HEIGHT>,
    /// Last value that was added
    prev: Option<LastInput<H::T>>,
    /// Stack of the partial roots required to calculate the final root
    stack: Vec<H::T>,
}

impl<H: Compressor, const HEIGHT: u32> IncrementalAbr<H, HEIGHT> {
    /// Calculates the root of abr trees up to and including `height`
    /// where all inputs the the input type's default.
    ///
    /// The default root of height 1 is at index 0, height 2 at 1, etc.
    fn default_roots(height: u32) -> Vec<H::T> {
        let mut out = Vec::with_capacity(height as usize);
        let default = H::T::default();
        let mut acc = H::compress(&default, &default);
        out.push(acc.clone());

        for _ in 1..height {
            acc = H::combine(&acc, &acc, &default);
            out.push(acc.clone());
        }
        out
    }

    pub fn new() -> IncrementalAbr<H, HEIGHT> {
        IncrementalAbr {
            pos: AbrPosition::new(),
            prev: None,
            stack: Vec::with_capacity(HEIGHT as usize - 1),
        }
    }
}

impl<H: Compressor, const HEIGHT: u32> IncrementalTree<H, HEIGHT> for IncrementalAbr<H, HEIGHT> {
    type Membership = AbrMembership<H>;

    fn push(&mut self, input: H::T) -> Result<(), CapacityExceededError> {
        if let Some(prev) = &self.prev {
            self.pos.increment()?;
            let carry = match prev {
                LeftLeaf(l) => {
                    self.prev = Some(RightLeaf(l.clone(), input));
                    return Ok(());
                }
                RightLeaf(l, r) => H::compress(&l, &r),
                Inner(l, r, i) => H::combine(&l, &r, &i),
            };

            self.prev = if self.pos.is_leaf() {
                self.stack.push(carry);
                Some(LeftLeaf(input))
            } else {
                Some(Inner(self.stack.pop().expect("Empty stack."), carry, input))
            };
        } else {
            self.prev = Some(LeftLeaf(input));
        }

        Ok(())
    }

    fn auth_path(&self) -> Option<AbrMembership<H>> {
        self.prev.as_ref().and_then(|prev| {
            let defaults = Self::default_roots(HEIGHT);
            let mut path = Vec::with_capacity((HEIGHT - self.pos.y - 1) as usize);
            let mut x = self.pos.x;
            let mut stack_pos = 1;

            // Account for leaf case; 4 inputs are needed to move to the next layer rather than 2
            if self.pos.is_leaf() {
                x /= 2
            };

            // Traverse from the previous input towards the root
            for altitude in self.pos.y + 1..HEIGHT {
                if x % 2 == 0 {
                    // Current node is a left input to its parent.
                    // Due to the insertion order no right sibling exists, so we the default root
                    path.push((defaults[altitude as usize - 1].clone(), H::T::default()));
                } else {
                    // Current node is a right input to its parent.
                    // Use partial root from the stack.
                    path.push((
                        self.stack[self.stack.len() - stack_pos].clone(),
                        H::T::default(),
                    ));
                    stack_pos += 1;
                }
                x /= 2;
            }

            Some(AbrMembership::<H> {
                val: prev.value().clone(),
                requisite: prev.requisite(),
                pos: (self.pos.x, self.pos.y),
                path,
            })
        })
    }

    fn root(&self) -> H::T {
        if let Some(path) = self.auth_path() {
            path.root()
        } else {
            Self::default_roots(HEIGHT).last().unwrap().clone()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use sha2::Sha256;

    #[test]
    fn sha256_height_2() {
        let mut tree = IncrementalAbr::<Sha256, 2>::new();
        let input = [161_u8; 32];
        let default = <Sha256 as Compressor>::T::default();
        let default_comp = Sha256::compress(&default, &default);
        let left_comp = Sha256::compress(&input, &default);
        let input_comp = Sha256::compress(&input, &input);

        assert_eq!(tree.root(), Sha256::combine(&default_comp, &default_comp, &default));
        tree.push(input).unwrap();
        assert_eq!(tree.root(), Sha256::combine(&left_comp, &default_comp, &default));
        tree.push(input).unwrap();
        assert_eq!(tree.root(), Sha256::combine(&input_comp, &default_comp, &default));
        tree.push(input).unwrap();
        assert_eq!(tree.root(), Sha256::combine(&input_comp, &left_comp, &default));
        tree.push(input).unwrap();
        assert_eq!(tree.root(), Sha256::combine(&input_comp, &input_comp, &default));
        tree.push(input).unwrap();
        assert_eq!(tree.root(), Sha256::combine(&input_comp, &input_comp, &input));

        assert!(tree.push(input).is_err());
    }
}
