use crate::{AbrCircuitInput, AbrCircuitValue, AbrInput};
use bellman::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        multipack,
    },
    ConstraintSystem, SynthesisError,
};
use ff::PrimeField;

impl<const LEN: usize> AbrInput for [u8; LEN] {
    fn mix(&self, right: &[u8; LEN]) -> [u8; LEN] {
        let mut out = [0_u8; LEN];
        for i in 0..LEN {
            out[i] = self[i] ^ right[i];
        }
        out
    }
}

impl<const LEN: usize> AbrCircuitInput for [u8; LEN] {
    type P = Vec<Boolean>;

    fn alloc<Scalar, CS>(mut cs: CS, from: Option<Self>) -> Result<Self::P, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        let bits = if let Some(data) = from {
            data.iter()
                // Convert bytes to bits
                .map(|byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8))
                .flatten()
                .map(|b| Some(b))
                .collect()
        } else {
            vec![None; LEN * 8]
        };
        bits.into_iter()
            .enumerate()
            // Allocate each bit.
            .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {}", i)), b))
            .map(|b| b.map(Boolean::from))
            .collect::<Result<Vec<_>, _>>()
    }
}

impl AbrCircuitValue for Vec<Boolean> {
    fn mix_circuit<Scalar, CS>(&self, mut cs: CS, right: &Self) -> Result<Self, SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        assert_eq!(self.len(), right.len());
        self.iter()
            .zip(right)
            .enumerate()
            .map(|(i, (l, r))| Boolean::xor(cs.namespace(|| format!("XOR bit {}", i)), l, r))
            .collect()
    }
    fn inputize<Scalar, CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        Scalar: PrimeField,
        CS: ConstraintSystem<Scalar>,
    {
        multipack::pack_into_inputs(cs.namespace(|| "pack hash"), self)
    }
}
