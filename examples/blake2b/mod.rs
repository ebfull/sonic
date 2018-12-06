use pairing::{Engine, Field};
use sonic::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};

trait OptionExt<T> {
    fn get(self) -> Result<T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn get(self) -> Result<T, SynthesisError> {
        match self {
            Some(v) => Ok(v),
            None => Err(SynthesisError::AssignmentMissing),
        }
    }
}

pub struct AllocatedBit<E: Engine> {
    value: Option<bool>,
    variable: LinearCombination<E>,
}

impl<E: Engine> AllocatedBit<E> {
    fn alloc<CS>(cs: &mut CS, value: Option<bool>) -> Result<AllocatedBit<E>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let (a, b, c) = cs.multiply(|| {
            if value.get()? {
                Ok((E::Fr::one(), E::Fr::one(), E::Fr::one()))
            } else {
                Ok((E::Fr::zero(), E::Fr::zero(), E::Fr::zero()))
            }
        })?;

        let b = LinearCombination::from(b);
        let c = LinearCombination::from(c);

        cs.enforce_zero(b - a);
        cs.enforce_zero(c - a);

        Ok(AllocatedBit {
            value,
            variable: LinearCombination::from(a),
        })
    }

    fn xor<CS>(cs: &mut CS, a: &Self, b: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let result_value = match (a.value, b.value) {
            (Some(a), Some(b)) => Some(a ^ b),
            _ => None
        };
        // (a + a) * (b) = (a + b - c)

    }
}
