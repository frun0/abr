pub mod hashes;
mod incremental;
mod inputs;
mod util;

pub use incremental::{AbrMembership, IncrementalAbr, IncrementalTree, MembershipProof};
pub use inputs::*;

use bellman::{Circuit, ConstraintSystem, SynthesisError};
use ff::PrimeField;

pub trait AbrInput: Clone {
    fn mix(&self, right: &Self) -> Self;
}

pub trait AbrCircuitInput: AbrInput {
    type P: AbrCircuitValue;

    fn alloc<Scalar, CS>(cs: CS, from: Option<Self>) -> Result<Self::P, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>;
}

pub trait AbrCircuitValue: Clone {
    fn mix_circuit<Scalar, CS>(&self, cs: CS, right: &Self) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>;

    fn inputize<Scalar, CS>(&self, cs: CS) -> Result<(), SynthesisError>
    where
        Scalar: PrimeField,
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

pub trait CompressorCircuit {
    type I: AbrCircuitInput;

    fn compress_circuit<Scalar, CS>(
        cs: CS,
        left: &<<Self as CompressorCircuit>::I as AbrCircuitInput>::P,
        right: &<<Self as CompressorCircuit>::I as AbrCircuitInput>::P,
    ) -> Result<<<Self as CompressorCircuit>::I as AbrCircuitInput>::P, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>;

    fn combine_circuit<Scalar, CS>(
        mut cs: CS,
        left: &<<Self as CompressorCircuit>::I as AbrCircuitInput>::P,
        right: &<<Self as CompressorCircuit>::I as AbrCircuitInput>::P,
        inner: &<<Self as CompressorCircuit>::I as AbrCircuitInput>::P,
    ) -> Result<<<Self as CompressorCircuit>::I as AbrCircuitInput>::P, SynthesisError>
    where
        Scalar: PrimeField,
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

pub struct AbrCircuit<H: CompressorCircuit, const HEIGHT: u32> {
    preimage: Option<Vec<H::I>>,
}

impl<H: CompressorCircuit, const HEIGHT: u32> AbrCircuit<H, HEIGHT> {
    fn alloc<CS, Scalar>(
        self,
        mut cs: CS,
    ) -> Result<Vec<<<H as CompressorCircuit>::I as AbrCircuitInput>::P>, SynthesisError>
    where
        Scalar: PrimeField,
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

impl<Scalar: PrimeField, H: CompressorCircuit, const HEIGHT: u32> Circuit<Scalar>
    for AbrCircuit<H, HEIGHT>
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

        // Expose the vector of boolean variables as input
        acc.inputize(cs.namespace(|| "pack hash"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellman::{gadgets::multipack, groth16};
    use bls12_381::Bls12;
    use rand::rngs::OsRng;
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
        let params = {
            let c = AbrCircuit::<Sha256, HEIGHT> { preimage: None };
            groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
        };

        // Prepare the verification key (for proof verification).
        let pvk = groth16::prepare_verifying_key(&params.vk);

        // Pick a preimage and compute its hash.
        let hash = abr::<Sha256, HEIGHT>(&preimage);

        // Create an instance of our circuit (with the preimage as a witness).
        let c = AbrCircuit::<Sha256, HEIGHT> {
            preimage: Some(preimage),
        };

        // Create a Groth16 proof with our parameters.
        let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();

        // Pack the hash as inputs for proof verification.
        let hash_bits = multipack::bytes_to_bits_le(&hash);
        let inputs = multipack::compute_multipacking(&hash_bits);

        // Check the proof!
        assert!(groth16::verify_proof(&pvk, &proof, &inputs).is_ok());
    }
}
