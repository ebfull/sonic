extern crate bellman;
extern crate pairing;
extern crate rand;
extern crate sapling_crypto;
extern crate sonic;

use pairing::{Engine, Field, PrimeField, CurveProjective};
use sonic::protocol::*;
use sonic::srs::SRS;
use sonic::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable, Coeff};
use sonic::synthesis::*;
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
        bellman::Variable::new_unchecked(bellman::Index::Input(1))
    }

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<bellman::Variable, bellman::SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, bellman::SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let var = self.cs.alloc(|| {
            f().map_err(|_| SynthesisError::AssignmentMissing)
        }).map_err(|_| bellman::SynthesisError::AssignmentMissing)?;

        Ok(match var {
            Variable::A(index) => bellman::Variable::new_unchecked(bellman::Index::Input(index)),
            Variable::B(index) => bellman::Variable::new_unchecked(bellman::Index::Aux(index)),
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
        let var = self.cs.alloc_input(|| {
            f().map_err(|_| SynthesisError::AssignmentMissing)
        }).map_err(|_| bellman::SynthesisError::AssignmentMissing)?;

        Ok(match var {
            Variable::A(index) => bellman::Variable::new_unchecked(bellman::Index::Input(index)),
            Variable::B(index) => bellman::Variable::new_unchecked(bellman::Index::Aux(index)),
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
                let var = match v.get_unchecked() {
                    bellman::Index::Input(i) => Variable::A(i),
                    bellman::Index::Aux(i) => Variable::B(i),
                };

                ret = ret + (Coeff::Full(coeff), var);
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
                coeff.multiply(&mut tmp);
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

        self.cs.enforce_zero(a_lc - a);
        self.cs.enforce_zero(b_lc - b);
        self.cs.enforce_zero(c_lc - c);
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

fn main() {
    use pairing::bls12_381::{Bls12, Fr};
    use std::time::{Instant};

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    println!("making srs");
    let start = Instant::now();
    let srs = SRS::<Bls12>::dummy(830564, srs_x, srs_alpha);
    println!("done in {:?}", start.elapsed());

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
            // sha256_block_no_padding(&mut *cs, &preimage)?;
            // sha256_block_no_padding(&mut *cs, &preimage)?;
            // sha256_block_no_padding(&mut *cs, &preimage)?;

            Ok(())
        }
    }

    {
        use pairing::{CurveAffine};
        use pairing::bls12_381::{G1Affine, G2Affine};
        let a = G1Affine::one();
        let b = G2Affine::one();
        let c = G1Affine::one();

        let alpha = G1Affine::one();
        let beta = G2Affine::one();
        let iv = G1Affine::one();
        let gamma = G2Affine::one().prepare();
        let delta = G2Affine::one().prepare();

        let alphabeta = <Bls12 as Engine>::pairing(alpha, beta);

        println!("verifying an idealized groth16 proof");
        let start = Instant::now();
        assert!(<Bls12 as Engine>::final_exponentiation(
            &<Bls12 as Engine>::miller_loop([
                (&a.prepare(), &b.prepare()),
                (&iv.prepare(), &gamma),
                (&c.prepare(), &delta),
            ].into_iter())
        ).unwrap() != alphabeta);
        println!("done in {:?}", start.elapsed());
    }

    {
        use sonic::util::multiexp;
        use pairing::{CurveAffine};
        use pairing::bls12_381::{G1Affine, G2Affine};
        // e([\alpha G], [\beta H]) = e(A, B) e(IV, [\gamma] H) e(C, [\delta] H)
        let a = G1Affine::one();
        let b = G2Affine::one();
        let c = vec![G1Affine::one(); 100];
        let mut tmp = Fr::one();
        tmp.double();
        tmp = tmp.inverse().unwrap();
        let cscalars = (0..100).map(|_| {tmp.square(); tmp}).collect::<Vec<_>>();

        let alpha = G1Affine::one();
        let beta = G2Affine::one();
        let iv = G1Affine::one();
        let gamma = G2Affine::one().prepare();
        let delta = G2Affine::one().prepare();

        let alphabeta = <Bls12 as Engine>::pairing(alpha, beta);

        println!("verifying 100 idealized groth16 proofs");
        let start = Instant::now();
        let c = multiexp(
            c.iter(),
            cscalars.iter(),
        ).into_affine();
        assert!(<Bls12 as Engine>::final_exponentiation(
            &<Bls12 as Engine>::miller_loop([
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&a.prepare(), &b.prepare()),
                (&iv.prepare(), &gamma),
                (&c.prepare(), &delta),
            ].into_iter())
        ).unwrap() != alphabeta);
        println!("done in {:?}", start.elapsed());
    }

    {
        type ChosenBackend = Permutation3;

        let samples: usize = 5;

        // const NUM_BITS: usize = 384;
        // let params = sapling_crypto::jubjub::JubjubBls12::new();
        // let circuit = PedersenHashPreimageCircuit {
        //     preimage: vec![Some(true); NUM_BITS],
        //     params: &params
        // };

        let circuit = SHA256PreimageCircuit {
            preimage: vec![Some(true); 512],
        };

        println!("creating proof");
        let start = Instant::now();
        let proof = create_proof::<Bls12, _, ChosenBackend>(&AdaptorCircuit(circuit.clone()), &srs).unwrap();
        println!("done in {:?}", start.elapsed());

        println!("creating advice");
        let start = Instant::now();
        let advice = create_advice::<Bls12, _, ChosenBackend>(&AdaptorCircuit(circuit.clone()), &proof, &srs);
        println!("done in {:?}", start.elapsed());

        println!("creating aggregate for {} proofs", samples);
        let start = Instant::now();
        let proofs: Vec<_> = (0..samples).map(|_| (proof.clone(), advice.clone())).collect();
        let aggregate = create_aggregate::<Bls12, _, ChosenBackend>(&AdaptorCircuit(circuit.clone()), &proofs, &srs);
        println!("done in {:?}", start.elapsed());

        {
            let mut verifier = MultiVerifier::<Bls12, _, ChosenBackend>::new(AdaptorCircuit(circuit.clone()), &srs).unwrap();
            println!("verifying 1 proof without advice");
            let start = Instant::now();
            {
                for _ in 0..1 {
                    verifier.add_proof(&proof, &[], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }

        {
            let mut verifier = MultiVerifier::<Bls12, _, ChosenBackend>::new(AdaptorCircuit(circuit.clone()), &srs).unwrap();
            println!("verifying {} proofs without advice", samples);
            let start = Instant::now();
            {
                for _ in 0..samples {
                    verifier.add_proof(&proof, &[], |_, _| None);
                }
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
        
        {
            let mut verifier = MultiVerifier::<Bls12, _, ChosenBackend>::new(AdaptorCircuit(circuit.clone()), &srs).unwrap();
            println!("verifying 100 proofs with advice");
            let start = Instant::now();
            {
                for (ref proof, ref advice) in &proofs {
                    verifier.add_proof_with_advice(proof, &[], advice);
                }
                verifier.add_aggregate(&proofs, &aggregate);
                assert_eq!(verifier.check_all(), true); // TODO
            }
            println!("done in {:?}", start.elapsed());
        }
    }
}
