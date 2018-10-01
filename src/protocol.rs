use merlin::Transcript;
use pairing::{Engine, CurveProjective, CurveAffine, Field};
use {Circuit, SynthesisError, Variable, ConstraintSystem, LinearCombination};
use srs::SRS;
use util::{multiexp, ChainExt, TranscriptProtocol, multiply_polynomials, kate_divison, OptionExt};

pub struct Proof<E: Engine> {
    com_r: E::G1Affine,
    r2: E::G1Affine,
    a2: E::G1Affine,
    r1: E::G1Affine,
    s: E::G1Affine,
    sx: E::G1Affine,
    a1: E::G1Affine,
    comr_quotient: E::G1Affine,
    r1_quotient: E::G1Affine,
    av: E::Fr,
    sv: E::Fr,
    s_quotient: E::G1Affine,
    r_prime: E::G2Affine,
    rx: E::G1Affine,
    t: E::G1Affine,
}

pub fn create_proof<E: Engine, C: Circuit<E>>(
    circuit: &C,
    srs: &SRS<E>,
) -> Result<Proof<E>, SynthesisError>
{
    let mut proof = Proof {
        com_r: E::G1Affine::zero(),
        r2: E::G1Affine::zero(),
        a2: E::G1Affine::zero(),
        r1: E::G1Affine::zero(),
        s: E::G1Affine::zero(),
        sx: E::G1Affine::zero(),
        a1: E::G1Affine::zero(),
        comr_quotient: E::G1Affine::zero(),
        r1_quotient: E::G1Affine::zero(),
        av: E::Fr::zero(),
        sv: E::Fr::zero(),
        s_quotient: E::G1Affine::zero(),
        r_prime: E::G2Affine::zero(),
        rx: E::G1Affine::zero(),
        t: E::G1Affine::zero(),
    };

    // Compute our wire values
    struct Wires<E: Engine> {
        a: Vec<E::Fr>,
        b: Vec<E::Fr>,
        c: Vec<E::Fr>
    }

    impl<E: Engine> ConstraintSystem<E> for Wires<E> {
        fn multiply<F>(&mut self, values: F) -> Result<(Variable, Variable, Variable), SynthesisError>
        where
            F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>
        {
            let index = self.a.len();
            let (a, b, c) = values()?;

            self.a.push(a);
            self.b.push(b);
            self.c.push(c);

            Ok((Variable::A(index), Variable::B(index), Variable::C(index)))
        }

        fn enforce(&mut self, _: LinearCombination<E>, _: E::Fr) {
            // We don't care about linear constraints yet, we're just
            // constructing the witness.
        }

        fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
            match var {
                Variable::A(index) => self.a.get(index),
                Variable::B(index) => self.b.get(index),
                Variable::C(index) => self.c.get(index),
            }.ok_or(SynthesisError::AssignmentMissing).map(|x| *x)
        }
    }

    let mut wires = Wires {
        a: vec![],
        b: vec![],
        c: vec![]
    };

    circuit.synthesize(&mut wires)?;

    // TODO: we can't have more wires than the SRS supports
    let n = wires.a.len();

    // Construct the transcript with the verifier
    let mut transcript = Transcript::new(&[]);

    // We're going to start by commiting to r1(X)
    proof.com_r = multiexp(&srs.g_positive_x[1..(n + 1)], &wires.a).into_affine();

    // We're going to evaluate r2(X) in alpha
    proof.r2 = multiexp(
        srs.g_negative_x_alpha[0..(2*n)].iter(),
        wires.b.iter().chain_ext(wires.c.iter())
    ).into_affine();

    // We're also going to evaluate it normally but shifted
    // right by d, so we can demonstrate they're strictly negative
    // exponents.
    proof.a2 = multiexp(
        srs.g_positive_x[srs.d - (2*n)..srs.d].iter(),
        wires.b.iter().chain_ext(wires.c.iter()).rev()
    ).into_affine();

    // Send ComR, R_2, A_2 to verifier
    transcript.commit_point(&proof.com_r);
    transcript.commit_point(&proof.r2);
    transcript.commit_point(&proof.a2);

    // Sample y from the verifier
    let y = transcript.get_challenge_scalar::<E::Fr>();

    // Let's compute r1(X, y)
    let mut r1xy = wires.a.clone();
    {
        let mut tmp = y;
        for coeff in &mut r1xy {
            coeff.mul_assign(&tmp);
            tmp.mul_assign(&y);
        }
    }

    // Evaluate r1(x, y)
    proof.r1 = multiexp(&srs.g_positive_x[1..(n + 1)], &r1xy).into_affine();

    // Compute s(X, y)
    let (s_poly_negative, s_poly_positive, k_y) = {
        let mut s_eval = SEval::new(y, n);
        circuit.synthesize(&mut s_eval)?;
        s_eval.finalize()
    };

    // Evaluate s(x, y) in alpha
    proof.s = multiexp(
        srs.g_negative_x_alpha[0..n].iter().chain_ext(
            srs.g_positive_x_alpha[0..(2*n)].iter()
        ),
        s_poly_negative.iter().chain_ext(s_poly_positive.iter())
    ).into_affine();

    // Evaluate x^n s(x, y) so we can use Kate
    proof.sx = multiexp(
        srs.g_positive_x[0..(3*n + 1)].iter(),
        s_poly_negative.iter().rev().chain_ext(Some(&E::Fr::zero())).chain_ext(s_poly_positive.iter())
    ).into_affine();

    // Evaluate r1(x, y) with a shift so we can demonstrate it
    // has no negative exponents
    proof.a1 = multiexp(
        srs.g_negative_x[srs.d - (n)..srs.d].iter(),
        r1xy.iter().rev()
    ).into_affine();

    // Same thing, but shifting up
    proof.rx = multiexp(
        srs.g_positive_x[(1 + (srs.d - (n)))..(srs.d+1)].iter(),
        r1xy.iter()
    ).into_affine();

    // Send S, Sx, A1, R1, Rx to the verifier
    transcript.commit_point(&proof.s);
    transcript.commit_point(&proof.sx);
    transcript.commit_point(&proof.a1);
    transcript.commit_point(&proof.r1);
    transcript.commit_point(&proof.rx);

    // Sample z from the verifier
    let z = transcript.get_challenge_scalar::<E::Fr>();

    // Make sure ComR and R1 have consistent coefficients
    proof.comr_quotient = {
        let mut point = y;
        point.mul_assign(&z);
        let poly = kate_divison(
            Some(&E::Fr::zero()).into_iter().chain_ext(wires.a.iter()),
            point,
        );
        multiexp(&srs.g_positive_x[0..poly.len()], &poly[..]).into_affine()
    };

    proof.r1_quotient = {
        let point = z;
        let poly = kate_divison(
            Some(&E::Fr::zero()).into_iter().chain_ext(r1xy.iter()),
            point,
        );
        multiexp(&srs.g_positive_x[0..poly.len()], &poly[..]).into_affine()
    };

    {
        let mut yz = z;
        yz.mul_assign(&y);
        let mut tmp = yz;
        for a in &wires.a {
            let mut a = *a;
            a.mul_assign(&tmp);

            let av: &mut E::Fr = &mut proof.av;
            av.add_assign(&a);

            tmp.mul_assign(&yz);
        }
    }

    {
        let mut tmp = E::Fr::one();
        for s in s_poly_negative.iter().rev().chain(Some(&E::Fr::zero())).chain(s_poly_positive.iter()) {
            let mut s = *s;
            s.mul_assign(&tmp);

            let sv: &mut E::Fr = &mut proof.sv;
            sv.add_assign(&s);

            tmp.mul_assign(&z);
        }
    }

    proof.s_quotient = {
        let poly = kate_divison(
            s_poly_negative.iter().rev().chain_ext(Some(&E::Fr::zero())).chain_ext(s_poly_positive.iter()),
            z
        );
        multiexp(&srs.g_positive_x[0..poly.len()], &poly).into_affine()
    };

    // Let's compute t(X, y)
    let mut r_x_y = wires.b;
    r_x_y.extend(wires.c);
    r_x_y.reverse();
    r_x_y.push(E::Fr::zero()); // constant term
    r_x_y.extend(r1xy);
    r_x_y.resize(4*n+1, E::Fr::zero());

    let mut r_x_y_prime = r_x_y.clone();
    // Add 2s(x, y)
    for (r, mut s) in r_x_y_prime[0..(2*n)].iter_mut().rev().zip(s_poly_negative) {
        s.double();
        r.add_assign(&s);
    }
    for (r, mut s) in r_x_y_prime[(2*n+1)..].iter_mut().zip(s_poly_positive) {
        s.double();
        r.add_assign(&s);
    }

    // Evaluate r'(x, y) in G2, in alpha
    proof.r_prime = multiexp(
        srs.h_negative_x_alpha[0..2*n].iter().chain_ext(
            srs.h_positive_x_alpha[0..2*n].iter()
        ),
        r_x_y_prime[0..2*n].iter().rev().chain_ext(r_x_y_prime[2*n+1..4*n+1].iter())
    ).into_affine();

    let mut t_x_y = multiply_polynomials::<E>(r_x_y, r_x_y_prime);

    assert_eq!(t_x_y.len(), 8*n + 1);

    // constant term should be 2*k_y
    t_x_y[4*n].sub_assign(&k_y);
    t_x_y[4*n].sub_assign(&k_y);
    assert!(t_x_y[4*n].is_zero());

    // Evaluate t(x, y) in alpha
    proof.t = multiexp(
        srs.g_positive_x_alpha[0..(4*n)].iter().chain_ext(
            srs.g_negative_x_alpha[0..(4*n)].iter()
        ),
        t_x_y[(4*n+1)..].iter().chain_ext(
            t_x_y[0..4*n].iter().rev()
        )
    ).into_affine();

    Ok(proof)
}

struct SEval<E: Engine> {
    y: E::Fr,

    // current value of k(y)
    k_y: E::Fr,
    // current value of y^{N+q}
    yqn: E::Fr,
    // current value of y^i
    yi: E::Fr,

    // x^{-i} y^{-i} (\sum\limits_{q=1}^Q y^{q+N} u_{q,i})
    u: Vec<E::Fr>,
    // x^{i} (\sum\limits_{q=1}^Q y^{q+N} v_{q,i})
    v: Vec<E::Fr>,
    // x^{i+N} (-y^i + \sum\limits_{q=1}^Q y^{q+N} w_{q,i})
    w: Vec<E::Fr>,
}

impl<E: Engine> SEval<E> {
    fn new(y: E::Fr, n: usize) -> Self {
        SEval {
            y: y,

            k_y: E::Fr::zero(),
            yqn: y.pow([(n + 1) as u64]),
            yi: y,

            u: vec![],
            v: vec![],
            w: vec![],
        }
    }

    /// Returns (s_negative, s_positive, k_y)
    fn finalize(mut self) -> (Vec<E::Fr>, Vec<E::Fr>, E::Fr) {
        let y_inv = self.y.inverse().unwrap();
        let mut tmp = y_inv;
        for u in &mut self.u {
            u.mul_assign(&tmp);
            tmp.mul_assign(&y_inv);
        }

        self.v.extend(self.w);

        (self.u, self.v, self.k_y)
    }
}

impl<E: Engine> ConstraintSystem<E> for SEval<E> {
    fn multiply<F>(&mut self, _: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>
    {
        let index = self.u.len();

        self.u.push(E::Fr::zero());
        self.v.push(E::Fr::zero());

        let mut negyi = self.yi;
        negyi.negate();
        self.w.push(negyi);

        self.yi.mul_assign(&self.y);

        Ok((Variable::A(index), Variable::B(index), Variable::C(index)))
    }

    fn enforce(&mut self, left: LinearCombination<E>, mut right: E::Fr) {
        for (var, mut coeff) in left.0 {
            coeff.mul_assign(&self.yqn);

            match var {
                Variable::A(index) => {
                    self.u[index].add_assign(&coeff);
                },
                Variable::B(index) => {
                    self.v[index].add_assign(&coeff);
                },
                Variable::C(index) => {
                    self.w[index].add_assign(&coeff);
                }
            }
        }

        // right will usually be 0 in practice :)
        if !right.is_zero() {
            right.mul_assign(&self.yqn);
            self.k_y.add_assign(&right);
        }

        self.yqn.mul_assign(&self.y);
    }

    fn get_value(&self, _: Variable) -> Result<E::Fr, SynthesisError> {
        Err(SynthesisError::AssignmentMissing)
    }
}

#[test]
fn circuit_test() {
    /// Circuit tests knowledge of x such that
    /// x^3 = r for given r.
    struct MyCircuit<E: Engine> {
        x: Option<E::Fr>,
        r: E::Fr,
    }

    impl<E: Engine> Circuit<E> for MyCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let (xl, xr, x2) = cs.multiply(|| {
                let x = self.x.get()?;

                let mut x2 = x;
                x2.square();

                Ok((x, x, x2))
            })?;

            cs.enforce(LinearCombination::<E>::from(xl) - xr, E::Fr::zero());

            let (a, b, x3) = cs.multiply(|| {
                let x = self.x.get()?;

                let mut x2 = x;
                x2.square();

                let mut x3 = x2;
                x3.mul_assign(&x);

                Ok((x, x2, x3))
            })?;

            cs.enforce(LinearCombination::<E>::from(a) - xl, E::Fr::zero());
            cs.enforce(LinearCombination::<E>::from(b) - x2, E::Fr::zero());
            cs.enforce(LinearCombination::<E>::from(x3), self.r);

            Ok(())
        }
    }

    use pairing::{PrimeField};
    use pairing::bls12_381::{Bls12, Fr};

    let srs_x = Fr::from_str("23923").unwrap();
    let srs_alpha = Fr::from_str("23728792").unwrap();
    let srs = SRS::<Bls12>::new(10, srs_x, srs_alpha);
    // let prepared_srs = PreparedSRS::from_srs(&srs);

    let x = Fr::from_str("2").unwrap();
    let mut x3 = x;
    x3.square();
    x3.mul_assign(&x);

    let proof = create_proof::<Bls12, _>(&MyCircuit { x: Some(x), r: x3 }, &srs).unwrap();

    // verify_proof::<Bls12, _>(&MyCircuit { x: None, r: x3 }, &srs, &proof).unwrap();

    // let r = Fr::from_str("3948349").unwrap();

    // use std::time::Instant;
    // let start = Instant::now();
    // verify_proof_faster::<Bls12, _>(&MyCircuit { x: None, r: x3 }, &srs, &prepared_srs, &proof, &r).unwrap();
    // let elapsed = start.elapsed();
    // panic!("{:?}", elapsed);
}
