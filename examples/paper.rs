extern crate bellman;
extern crate pairing;
extern crate rand;
extern crate sapling_crypto;
extern crate sonic;

use pairing::{Engine, Field, PrimeField};
use sonic::protocol::{create_proof, Batch, Precomp, Proof};
use sonic::srs::SRS;
use sonic::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use std::marker::PhantomData;

struct Adaptor<'a, E: Engine, CS: ConstraintSystem<E> + 'a> {
    cs: &'a mut CS,
    _marker: PhantomData<E>,
}

impl<'a, E: Engine, CS: ConstraintSystem<E> + 'a> bellman::ConstraintSystem<E>
    for Adaptor<'a, E, CS>
{
    type Root = Self;

    fn one() -> bellman::Variable {
        bellman::Variable::new_unchecked(bellman::Index::Input(0))
    }

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<bellman::Variable, bellman::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, bellman::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let (a, _, _) = self
            .cs
            .multiply(|| {
                Ok((
                    f().map_err(|_| SynthesisError::AssignmentMissing)?,
                    E::Fr::zero(),
                    E::Fr::zero(),
                ))
            })
            .map_err(|_| bellman::SynthesisError::AssignmentMissing)?;

        Ok(match a {
            Variable::A(index) => bellman::Variable::new_unchecked(bellman::Index::Aux(index)),
            _ => unreachable!(),
        })
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        f: F,
    ) -> Result<bellman::Variable, bellman::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, bellman::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let a = self
            .cs
            .alloc_input(|| Ok(f().map_err(|_| SynthesisError::AssignmentMissing)?))
            .map_err(|_| bellman::SynthesisError::AssignmentMissing)?;

        Ok(match a {
            Variable::A(index) => bellman::Variable::new_unchecked(bellman::Index::Aux(index)),
            _ => unreachable!(),
        })
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(bellman::LinearCombination<E>) -> bellman::LinearCombination<E>,
        LB: FnOnce(bellman::LinearCombination<E>) -> bellman::LinearCombination<E>,
        LC: FnOnce(bellman::LinearCombination<E>) -> bellman::LinearCombination<E>,
    {
        fn convert<E: Engine>(lc: bellman::LinearCombination<E>) -> LinearCombination<E> {
            let mut ret = LinearCombination::zero();

            for &(v, coeff) in lc.as_ref().iter() {
                let index = match v.get_unchecked() {
                    bellman::Index::Input(i) => i,
                    bellman::Index::Aux(i) => i,
                };

                ret = ret + (coeff, Variable::A(index));
            }

            ret
        }

        fn eval<E: Engine, CS: ConstraintSystem<E>>(
            lc: &LinearCombination<E>,
            cs: &CS,
        ) -> Option<E::Fr> {
            let mut ret = E::Fr::zero();

            for &(v, coeff) in lc.as_ref().iter() {
                let mut tmp = match cs.get_value(v) {
                    Ok(tmp) => tmp,
                    Err(_) => return None,
                };
                tmp.mul_assign(&coeff);
                ret.add_assign(&tmp);
            }

            Some(ret)
        }

        let a_lc = convert(a(bellman::LinearCombination::zero()));
        let a_value = eval(&a_lc, &*self.cs);
        let b_lc = convert(b(bellman::LinearCombination::zero()));
        let b_value = eval(&b_lc, &*self.cs);
        let c_lc = convert(c(bellman::LinearCombination::zero()));
        let c_value = eval(&c_lc, &*self.cs);

        let (a, b, c) = self
            .cs
            .multiply(|| Ok((a_value.unwrap(), b_value.unwrap(), c_value.unwrap())))
            .unwrap();

        self.cs.enforce(a_lc - a);
        self.cs.enforce(b_lc - b);
        self.cs.enforce(c_lc - c);
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

struct AdaptorCircuit<T>(T);

impl<'a, E: Engine, C: bellman::Circuit<E> + Clone> Circuit<E> for AdaptorCircuit<C> {
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut adaptor = Adaptor {
            cs: cs,
            _marker: PhantomData,
        };

        match self.0.clone().synthesize(&mut adaptor) {
            Err(_) => return Err(SynthesisError::AssignmentMissing),
            Ok(_) => {}
        };

        Ok(())
    }
}

pub fn create_proof_r1cs<E: Engine, C: bellman::Circuit<E> + Clone>(
    r1cs_circuit: C,
    srs: &SRS<E>,
) -> Result<Proof<E>, SynthesisError> {
    create_proof(&AdaptorCircuit(r1cs_circuit), &srs)
}

fn create_r1cs_precomp<'a, E: Engine, C: bellman::Circuit<E> + Clone>(
    r1cs_circuit: C,
    srs: &'a SRS<E>,
) -> Result<Precomp<'a, E, AdaptorCircuit<C>>, SynthesisError> {
    Precomp::new(AdaptorCircuit(r1cs_circuit), &srs)
}

fn main() {
    use pairing::bls12_381::{Bls12, Fr};
    use std::time::{Duration, Instant};

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

    #[derive(Clone)]
    struct SHA256PreimageCircuit {
        preimage: Vec<Option<bool>>,
    }

    impl<E: Engine> bellman::Circuit<E> for SHA256PreimageCircuit {
        fn synthesize<CS: bellman::ConstraintSystem<E>>(
            self,
            cs: &mut CS,
        ) -> Result<(), bellman::SynthesisError> {
            //use bellman::ConstraintSystem;
            use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
            use sapling_crypto::circuit::sha256::sha256_block_no_padding;

            let mut preimage = vec![];

            for &bit in self.preimage.iter() {
                preimage.push(Boolean::from(AllocatedBit::alloc(&mut *cs, bit)?));
            }

            sha256_block_no_padding(&mut *cs, &preimage)?;
            sha256_block_no_padding(&mut *cs, &preimage)?;
            sha256_block_no_padding(&mut *cs, &preimage)?;
            sha256_block_no_padding(&mut *cs, &preimage)?;

            Ok(())
        }
    }

    {
        let samples: usize = 2;

        let circuit = SHA256PreimageCircuit {
            preimage: vec![None; 512],
        };

        let precomp = create_r1cs_precomp(circuit, &srs).unwrap();

        println!("making proof");
        let start = Instant::now();
        let proof = create_proof_r1cs::<Bls12, _>(
            SHA256PreimageCircuit {
                preimage: vec![Some(true); 512],
            },
            &srs,
        ).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("verifying 1 proof without advice");
        let start = Instant::now();
        {
            let mut batch = precomp.new_batch(false);
            assert_eq!(batch.add_proof(&proof, &[]).unwrap(), true);
            assert!(batch.check_all(None));
        }
        println!("done in {:?}", start.elapsed());

        println!("verifying {} proofs without advice", samples);
        let start = Instant::now();
        {
            let mut batch = precomp.new_batch(false);
            for _ in 0..samples {
                assert_eq!(batch.add_proof(&proof, &[]).unwrap(), true);
            }
            assert!(batch.check_all(None));
        }
        println!("done in {:?}", start.elapsed());

        {
            let mut batch = precomp.new_batch(true);
            for _ in 0..samples {
                assert_eq!(batch.add_proof(&proof, &[]).unwrap(), true);
            }
            let advice = batch.create_advice();
            drop(batch);

            let start = Instant::now();

            println!("verifying {} proofs with advice", samples);
            {
                let mut batch = precomp.new_batch(true);
                for _ in 0..samples {
                    assert_eq!(batch.add_proof(&proof, &[]).unwrap(), true);
                }
                assert!(batch.check_all(Some(&advice)));
            }
            println!("done in {:?}", start.elapsed());
        }
    }

    /* 
    struct PedersenHashPreimageCircuit<'a, E: sapling_crypto::jubjub::JubjubEngine + 'a> {
        preimage: Vec<Option<bool>>,
        params: &'a E::Params,
    }

    impl<'a, E: sapling_crypto::jubjub::JubjubEngine + 'a> Clone for PedersenHashPreimageCircuit<'a, E> {
        fn clone(&self) -> Self {
            PedersenHashPreimageCircuit {
                preimage: self.preimage.clone(),
                params: self.params
            }
        }
    }

    impl<'a, E: sapling_crypto::jubjub::JubjubEngine> bellman::Circuit<E> for PedersenHashPreimageCircuit<'a, E> {
        fn synthesize<CS: bellman::ConstraintSystem<E>>(
            self,
            cs: &mut CS
        ) -> Result<(), bellman::SynthesisError>
        {
            //use bellman::ConstraintSystem;
            use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
            use sapling_crypto::circuit::pedersen_hash;

            let mut preimage = vec![];

            for &bit in self.preimage.iter() {
                preimage.push(Boolean::from(AllocatedBit::alloc(&mut* cs, bit)?));
            }

            pedersen_hash::pedersen_hash(
                &mut* cs, pedersen_hash::Personalization::NoteCommitment, &preimage, self.params)?;

            Ok(())
        }
    }

    {
        const NUM_BITS: usize = 768;

        let params = sapling_crypto::jubjub::JubjubBls12::new();
        let pubinput: &[Fr] = &[];
        let circuit = PedersenHashPreimageCircuit {
            preimage: vec![None; NUM_BITS],
            params: &params
        };

        let precomp = Precomp::new::<Bls12, _>(&AdaptorCircuit(circuit.clone(), pubinput)).unwrap();

        println!("making proof");
        let start = Instant::now();
        let proof = create_proof_r1cs::<Bls12, _>(PedersenHashPreimageCircuit {
            preimage: vec![Some(true); NUM_BITS],
            params: &params
        }, &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("verifying proof (without s(x, y) computation)");
        let start = Instant::now();
        verify_proof_r1cs::<Bls12, _>(circuit.clone(), &srs, &proof, pubinput, &precomp, false).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("verifying proof (with s(x, y) computation)");
        let start = Instant::now();
        verify_proof_r1cs::<Bls12, _>(circuit.clone(), &srs, &proof, pubinput, &precomp, true).unwrap();
        println!("done in {:?}", start.elapsed());
    }
    */
}
