use crate::{util::flip_endian, Compressor, CompressorCircuit};
use bellperson::{gadgets::boolean::Boolean, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use sha2::{digest::Digest, Sha256};

impl Compressor for Sha256 {
    type T = [u8; 32];

    fn compress(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
        let digest = Sha256::new().chain(a).chain(b).finalize();
        From::from(digest)
    }
}

impl<Scalar: PrimeField> CompressorCircuit<Scalar> for Sha256 {
    type I = [u8; 32];

    fn compress_circuit<CS>(
        mut cs: CS,
        left: &Vec<Boolean>,
        right: &Vec<Boolean>,
    ) -> Result<Vec<Boolean>, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        assert_eq!(left.len(), 256);
        assert_eq!(right.len(), 256);
        let concat: Vec<Boolean> = left.iter().cloned().chain(right.iter().cloned()).collect();
        let digest =
            bellperson::gadgets::sha256::sha256(cs.namespace(|| "sha256"), &flip_endian(&concat))?;
        Ok(flip_endian(&digest))
    }
}
