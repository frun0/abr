use crate::{Compressor, CompressorCircuit, NumericInput};
use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use neptune::{circuit::poseidon_hash, poseidon::PoseidonConstants, Poseidon};
use typenum::U2;

impl<Scalar: PrimeField> Compressor for Poseidon<'_, Scalar> {
    type T = NumericInput<Scalar>;

    fn compress(a: &NumericInput<Scalar>, b: &NumericInput<Scalar>) -> NumericInput<Scalar> {
        let constants = PoseidonConstants::<Scalar, U2>::new();
        NumericInput(Poseidon::new_with_preimage(&[a.0, b.0], &constants).hash())
    }
}

impl<Scalar: PrimeField> CompressorCircuit<Scalar> for Poseidon<'_, Scalar> {
    type I = NumericInput<Scalar>;

    fn compress_circuit<CS: ConstraintSystem<Scalar>>(
        mut cs: CS,
        left: &AllocatedNum<Scalar>,
        right: &AllocatedNum<Scalar>,
    ) -> Result<AllocatedNum<Scalar>, SynthesisError> {
        let constants = PoseidonConstants::<Scalar, U2>::new();
        poseidon_hash(
            cs.namespace(|| "poseidon hash"),
            vec![left.clone(), right.clone()],
            &constants,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::NumericInput;
    use crate::{Compressor, CompressorCircuit};
    use bellperson::{
        gadgets::num::AllocatedNum, gadgets::test::TestConstraintSystem, ConstraintSystem,
        SynthesisError,
    };
    use bls12_381::Scalar;
    use neptune::Poseidon;

    #[test]
    fn poseidon_gadget_test() {
        let preimage = [
            NumericInput(Scalar::one().double().double()),
            NumericInput(Scalar::zero()),
        ];
        let expected = Poseidon::compress(&preimage[0], &preimage[1]).0;
        let mut cs = TestConstraintSystem::new();
        let preimage_alloc = {
            let mut cs = cs.namespace(|| "alloc");
            preimage
                .iter()
                .enumerate()
                .map(|(i, n)| AllocatedNum::alloc(cs.namespace(|| format!("{}", i)), || Ok(n.0)))
                .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()
        }
        .expect("Synthesis error in allocation");

        let out = Poseidon::compress_circuit(&mut cs, &preimage_alloc[0], &preimage_alloc[1])
            .expect("Synthesis error in hash");

        assert!(cs.is_satisfied(), "constraints not satisfied!");
        assert_eq!(
            expected,
            out.get_value().expect("could not get value from hash"),
            "hashes do not match"
        );
    }

    #[test]
    fn poseidon_gadget_test_failure() {
        let mut preimage = [
            NumericInput(Scalar::one().double().double()),
            NumericInput(Scalar::zero()),
        ];
        let expected = Poseidon::compress(&preimage[0], &preimage[1]).0;
        preimage[0] = NumericInput(Scalar::one());
        let mut cs = TestConstraintSystem::new();
        let preimage_alloc = {
            let mut cs = cs.namespace(|| "alloc");
            preimage
                .iter()
                .enumerate()
                .map(|(i, n)| AllocatedNum::alloc(cs.namespace(|| format!("{}", i)), || Ok(n.0)))
                .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()
        }
        .expect("Synthesis error in allocation");

        let out = Poseidon::compress_circuit(&mut cs, &preimage_alloc[0], &preimage_alloc[1])
            .expect("Synthesis error in hash");

        assert!(cs.is_satisfied(), "constraints not satisfied!");
        assert_ne!(
            expected,
            out.get_value().expect("could not get value from hash"),
            "hashes do not match"
        );
    }
}
