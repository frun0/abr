use crate::{AbrCircuitInput, AbrCircuitValue, AbrInput};
use bellperson::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
        multipack,
        num::AllocatedNum,
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

impl<Scalar: PrimeField, const LEN: usize> AbrCircuitInput<Scalar> for [u8; LEN] {
    type P = Vec<Boolean>;

    fn alloc<CS>(mut cs: CS, from: Option<Self>) -> Result<Self::P, SynthesisError>
    where
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

impl<Scalar: PrimeField> AbrCircuitValue<Scalar> for Vec<Boolean> {
    fn mix_circuit<CS>(&self, mut cs: CS, right: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        assert_eq!(self.len(), right.len());
        self.iter()
            .zip(right)
            .enumerate()
            .map(|(i, (l, r))| Boolean::xor(cs.namespace(|| format!("XOR bit {}", i)), l, r))
            .collect()
    }
    fn inputize<CS: ConstraintSystem<Scalar>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
        multipack::pack_into_inputs(cs.namespace(|| "pack hash"), self)
    }
}

#[derive(Debug, Clone)]
pub struct NumericInput<Scalar>(pub Scalar);

impl<Scalar: PrimeField> Default for NumericInput<Scalar> {
    fn default() -> Self {
        NumericInput(Scalar::zero())
    }
}

impl<Scalar: PrimeField> AbrInput for NumericInput<Scalar> {
    fn mix(&self, right: &NumericInput<Scalar>) -> NumericInput<Scalar> {
        NumericInput(self.0 + right.0)
    }
}

impl<Scalar: PrimeField> AbrCircuitInput<Scalar> for NumericInput<Scalar> {
    type P = AllocatedNum<Scalar>;

    fn alloc<CS>(mut cs: CS, from: Option<Self>) -> Result<Self::P, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        AllocatedNum::alloc(cs.namespace(|| "alloc num"), || {
            Ok(from.ok_or(SynthesisError::AssignmentMissing)?.0)
        })
    }
}

impl<Scalar: PrimeField> AbrCircuitValue<Scalar> for AllocatedNum<Scalar> {
    fn mix_circuit<CS: ConstraintSystem<Scalar>>(
        &self,
        mut cs: CS,
        right: &Self,
    ) -> Result<Self, SynthesisError> {
        let new = AllocatedNum::alloc(cs.namespace(|| "sum num"), || {
            let mut tmp = self.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            tmp.add_assign(right.get_value().ok_or(SynthesisError::AssignmentMissing)?);

            Ok(tmp)
        })?;

        // Constrain: a + b = a + b
        cs.enforce(
            || "addition constraint",
            |lc| lc + self.get_variable() + right.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + new.get_variable(),
        );

        Ok(new)
    }
    fn inputize<CS: ConstraintSystem<Scalar>>(&self, mut cs: CS) -> Result<(), SynthesisError> {
        self.inputize(cs.namespace(|| "inputize hash"))
    }
}
