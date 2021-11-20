pub mod hashes;
mod incremental;
mod inputs;
mod util;

pub use incremental::{AbrMembership, IncrementalAbr, IncrementalTree, MembershipProof};
pub use inputs::*;

use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use ff::PrimeField;

pub trait AbrInput: Clone {
    fn mix(&self, right: &Self) -> Self;
}

pub trait AbrCircuitInput<Scalar: PrimeField>: AbrInput {
    type P: AbrCircuitValue<Scalar>;

    fn alloc<CS>(cs: CS, from: Option<Self>) -> Result<Self::P, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>;
}

pub trait AbrCircuitValue<Scalar: PrimeField>: Clone {
    fn mix_circuit<CS>(&self, cs: CS, right: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>;

    fn inputize<CS>(&self, cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>;
}

pub trait Compressor {
    type T: AbrInput + Default;
    fn compress(a: &Self::T, b: &Self::T) -> Self::T;
    fn combine(left: &Self::T, right: &Self::T, inner: &Self::T) -> Self::T {
        let l = left.mix(inner);
        let r = right.mix(inner);
        Self::compress(&l, &r).mix(right)
    }
}

pub trait CompressorCircuit<Scalar: PrimeField> {
    type I: AbrCircuitInput<Scalar>;

    fn compress_circuit<CS>(
        cs: CS,
        left: &<<Self as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P,
        right: &<<Self as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P,
    ) -> Result<
        <<Self as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P,
        SynthesisError,
    >
    where
        CS: ConstraintSystem<Scalar>;

    fn combine_circuit<CS>(
        mut cs: CS,
        left: &<<Self as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P,
        right: &<<Self as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P,
        inner: &<<Self as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P,
    ) -> Result<
        <<Self as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P,
        SynthesisError,
    >
    where
        CS: ConstraintSystem<Scalar>,
    {
        let l = left.mix_circuit(cs.namespace(|| "mix left and inner"), inner)?;
        let r = right.mix_circuit(cs.namespace(|| "mix right and inner"), inner)?;
        Self::compress_circuit(cs.namespace(|| "compress"), &l, &r)?
            .mix_circuit(cs.namespace(|| "mix output with right parent"), right)
    }
}

// const generic is not necessary, but plays well with the circuit implementation.
pub fn abr<H: Compressor, const HEIGHT: u32>(data: &[H::T]) -> H::T {
    assert!(HEIGHT > 0);
    assert_eq!(3 * 2_usize.pow(HEIGHT - 1) - 1, data.len());

    let mut stack = Vec::with_capacity(HEIGHT as usize - 1);
    let mut inputs = data.iter();
    let mut acc = H::T::default();
    // Iterate outputs of leaf layer
    for i in 0..2_usize.pow(HEIGHT - 1) {
        acc = H::compress(inputs.next().unwrap(), inputs.next().unwrap());
        // Traverse towards root as long as we are looking at a right input.
        for _ in std::iter::successors(Some(i), |prev| Some(prev / 2)).take_while(|n| n % 2 == 1) {
            acc = H::combine(
                &stack.pop().expect("Empty stack"),
                &acc,
                inputs.next().unwrap(),
            );
        }
        stack.push(acc.clone());
    }
    acc
}

pub struct AbrCircuit<Scalar: PrimeField, H: CompressorCircuit<Scalar>, const HEIGHT: u32> {
    preimage: Option<Vec<H::I>>,
}

impl<Scalar: PrimeField, H: CompressorCircuit<Scalar>, const HEIGHT: u32>
    AbrCircuit<Scalar, H, HEIGHT>
{
    fn alloc<CS>(
        self,
        mut cs: CS,
    ) -> Result<
        Vec<<<H as CompressorCircuit<Scalar>>::I as AbrCircuitInput<Scalar>>::P>,
        SynthesisError,
    >
    where
        CS: ConstraintSystem<Scalar>,
    {
        // Allocate the values of the preimage. When verifying a proof,
        // we might still need to create constraints (e.g. for bits),
        // so we use an equivalent-size Vec of None.
        let pre = self
            .preimage
            .map_or(vec![None; 3 * 2_usize.pow(HEIGHT - 1) - 1], |preimage| {
                preimage.into_iter().map(|x| Some(x)).collect()
            });
        assert_eq!(pre.len(), 3 * 2_usize.pow(HEIGHT - 1) - 1);
        pre.into_iter()
            .enumerate()
            .map(|(i, input)| H::I::alloc(cs.namespace(|| format!("alloc input {}", i)), input))
            .collect::<Result<Vec<_>, _>>()
    }
}

impl<Scalar: PrimeField, H: CompressorCircuit<Scalar>, const HEIGHT: u32> Circuit<Scalar>
    for AbrCircuit<Scalar, H, HEIGHT>
{
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let alloced = self.alloc(cs.namespace(|| "alloc input"))?;
        let mut inputs = alloced.iter();
        // Store interim results, index signifies height of result
        let mut stack = Vec::with_capacity(HEIGHT as usize - 1);
        // Initialization value is unused
        let mut acc = alloced[0].clone();

        // Iterate outputs of leaf layer
        for i in 0..2_usize.pow(HEIGHT - 1) {
            acc = H::compress_circuit(
                cs.namespace(|| format!("compress leaf pair {}", i)),
                inputs.next().unwrap(),
                inputs.next().unwrap(),
            )?;
            // Traverse towards root as long as there are interim results to combine with
            for h in
                std::iter::successors(Some(i), |prev| Some(prev / 2)).take_while(|n| n % 2 == 1)
            {
                acc = H::combine_circuit(
                    cs.namespace(|| format!("combine {}th node at height {}", i, h)),
                    &stack.pop().expect("Empty stack"),
                    &acc,
                    inputs.next().unwrap(),
                )?;
            }
            stack.push(acc.clone());
        }

        acc.inputize(cs.namespace(|| "expose hash"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellperson::{gadgets::multipack, gadgets::test::TestConstraintSystem};
    use bls12_381::Scalar;
    use neptune::Poseidon;
    use sha2::{digest::Digest, Sha256};

    #[test]
    fn sha256_height_2() {
        const BLOCK_SIZE: usize = 32;
        const BYTE_VAL: u8 = 161;
        const HEIGHT: u32 = 2;

        let h0 = Sha256::digest(&[BYTE_VAL; BLOCK_SIZE * 2]);
        let expected = Sha256::combine(&h0.into(), &h0.into(), &[BYTE_VAL; BLOCK_SIZE]);

        let input = [[BYTE_VAL; BLOCK_SIZE]; 3 * 2_usize.pow(HEIGHT - 1) - 1];
        let actual = abr::<Sha256, 2>(&input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn sha256_height_12() {
        const BLOCK_SIZE: usize = 32;
        const BYTE_VAL: u8 = 161;
        const HEIGHT: u32 = 12;

        // Calculation becomes trivial if all input blocks are the same
        // We use this to test the more complex algorithm
        let h0 = Sha256::digest(&[BYTE_VAL; BLOCK_SIZE * 2]);
        let mut expected = Sha256::combine(&h0.into(), &h0.into(), &[BYTE_VAL; BLOCK_SIZE]);
        for _ in 2..HEIGHT {
            expected = Sha256::combine(&expected, &expected, &[BYTE_VAL; BLOCK_SIZE]);
        }

        let input = vec![[BYTE_VAL; BLOCK_SIZE]; 3 * 2_usize.pow(HEIGHT - 1) - 1];
        let actual = abr::<Sha256, HEIGHT>(&input);
        assert_eq!(expected, actual);
    }

    #[test]
    fn sha256_height_4_proof() {
        const BLOCK_SIZE: usize = 32;
        const BYTE_VAL: u8 = 161;
        const HEIGHT: u32 = 4;
        let preimage = vec![[BYTE_VAL; BLOCK_SIZE]; 3 * 2_usize.pow(HEIGHT - 1) - 1];

        let hash = abr::<Sha256, HEIGHT>(&preimage);

        let c = AbrCircuit::<Scalar, Sha256, HEIGHT> {
            preimage: Some(preimage),
        };
        // Pack the hash as inputs for proof verification.
        let hash_bits = multipack::bytes_to_bits_le(&hash);
        let inputs = multipack::compute_multipacking(&hash_bits);

        let mut cs = TestConstraintSystem::new();
        c.synthesize(&mut cs).expect("failed synthesis");
        if let Some(s) = cs.which_is_unsatisfied() {
            panic!("failed to satisfy: {:?}", s);
        }

        // Check the proof!
        assert!(cs.verify(&inputs), "verification failed");
    }

    #[test]
    fn poseidon_height_4_proof() {
        const VAL: NumericInput<Scalar> = NumericInput(Scalar::one().double().double());
        const HEIGHT: u32 = 4;
        let preimage = vec![VAL; 3 * 2_usize.pow(HEIGHT - 1) - 1];

        let hash = abr::<Poseidon<_>, HEIGHT>(&preimage).0;
        let inputs = [hash];

        let c = AbrCircuit::<Scalar, Poseidon<_>, HEIGHT> {
            preimage: Some(preimage),
        };

        let mut cs = TestConstraintSystem::new();
        c.synthesize(&mut cs).expect("failed synthesis");
        if let Some(s) = cs.which_is_unsatisfied() {
            panic!("failed to satisfy: {:?}", s);
        }

        // Check the proof!
        assert!(cs.verify(&inputs), "verification failed");
    }
}
