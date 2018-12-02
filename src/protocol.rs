use merlin::Transcript;
use pairing::{CurveAffine, CurveProjective, Engine, Field, PrimeField};
use srs::SRS;
use util::{kate_divison, multiexp, multiply_polynomials, ChainExt, TranscriptProtocol};
use {Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};

/*
Note that this protocol differs from the paper in several ways,
and is probably broken because of it. (I think it may be secure
in the algebraic group model, which is all I really care about.)

 A' = [r_1(x, 1)] G
A_R = [r_1(x, 1) x^{d - N}] G
A_L = [r_1(x, 1) x^{-d}] G
  B = [r_2(x)] G
B_R = [r_2(x) x^{d}] G
* e(A', [x^{d - N}] H) = e(A_R, H)
* e(A', [x^{-d}] H) = e(A_L, H)
* e(B, [x^{d}] H) = e(B_R, H)
-----
y <- F
  A = [r_1(x, y)] G
  S = [s(x, y)] G
-----
z <- F
A_v = r_1(z, y)
A_x = [\frac{r_1(x, 1) - A_v}{x - yz}] G
A_y = [\frac{r_1(x, y) - A_v}{x - z}] G
* e(A_x, [x - yz] H) = e(A' - [A_v] G, H)
* e(A_y, [x - z] H) = e(A - [A_v] G, H)
R = [r(x, y) \alpha] H
* e(A + B, [\alpha] H) = e(G, R)
T = [t(x, y) \alpha] G
* e(A + B + 2S, R) e([-2k(y)] G, [\alpha] H) = e(T, H)

Per-proof verification of S:
S_v = s(z, y) z^n
 S' = [\frac{s(x, y) x^n - S_v}{x - z}] G
* e(S', [x - z] H) = e(S, [x^n] H) e([-S_v] G, H)
*/

pub struct Proof<E: Engine> {
    a_prime: E::G1Affine,
    a_r: E::G1Affine,
    a_l: E::G1Affine,
    b: E::G1Affine,
    b_r: E::G1Affine,

    a: E::G1Affine,
    s: E::G1Affine,

    a_v: E::Fr,
    a_x: E::G1Affine,
    a_y: E::G1Affine,
    r: E::G2Affine,
    t: E::G1Affine,

    s_v: E::Fr,
    s_prime: E::G1Affine,
}

pub struct Precomp<'a, E: Engine, C: Circuit<E>> {
    /// The circuit used
    circuit: C,

    /// The SRS being used
    srs: &'a SRS<E>,

    /// Number of multiplication gates
    n: usize,

    /// Number of linear constraints
    q: usize,

    /// Map from public inputs to the exponent
    /// of y in k(y).
    k_map: Vec<u64>,

    // H
    h: <E::G2Affine as CurveAffine>::Prepared,

    // [x] H
    x: <E::G2Affine as CurveAffine>::Prepared,

    // [x^{d}] H
    x_d: <E::G2Affine as CurveAffine>::Prepared,

    // [x^{-d}] H
    x_neg_d: <E::G2Affine as CurveAffine>::Prepared,

    // [x^{d-N}] H
    x_d_minus_n: <E::G2Affine as CurveAffine>::Prepared,

    // [x^N] H
    x_n: <E::G2Affine as CurveAffine>::Prepared,

    // [\alpha] H
    alpha: <E::G2Affine as CurveAffine>::Prepared,
}

impl<'a, E: Engine, C: Circuit<E>> Precomp<'a, E, C> {
    pub fn new(circuit: C, srs: &'a SRS<E>) -> Result<Self, SynthesisError> {
        struct Temp {
            n: usize,
            q: usize,
            k_map: Vec<u64>,
        }

        impl<E: Engine> ConstraintSystem<E> for Temp {
            fn alloc_input<F>(&mut self, _value: F) -> Result<Variable, SynthesisError>
            where
                F: FnOnce() -> Result<E::Fr, SynthesisError>,
            {
                let index = self.n;
                self.n += 1;
                self.q += 1;

                self.k_map.push(self.q as u64);

                Ok(Variable::A(index))
            }

            fn multiply<F>(
                &mut self,
                _: F,
            ) -> Result<(Variable, Variable, Variable), SynthesisError>
            where
                F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>,
            {
                let index = self.n;
                self.n += 1;

                Ok((Variable::A(index), Variable::B(index), Variable::C(index)))
            }

            fn enforce(&mut self, _lc: LinearCombination<E>) {
                self.q += 1;
                // We don't care about linear constraints yet.
            }
        }

        let mut tmp: Temp = Temp {
            n: 0,
            q: 0,
            k_map: vec![],
        };

        ConstraintSystem::<E>::alloc_input(&mut tmp, || Ok(E::Fr::one())).unwrap();

        circuit.synthesize(&mut tmp)?;

        for i in &mut tmp.k_map {
            *i += tmp.n as u64;
        }

        println!("gates {}", tmp.n);

        let d_minus_n = srs.d - tmp.n;
        let d = srs.d;

        Ok(Precomp {
            circuit: circuit,
            srs: srs,
            n: tmp.n,
            q: tmp.q,
            k_map: tmp.k_map,

            h: srs.h_positive_x[0].prepare(),
            x: srs.h_positive_x[1].prepare(),
            x_d: srs.h_positive_x[d].prepare(),
            x_neg_d: srs.h_negative_x[d].prepare(),
            x_d_minus_n: srs.h_positive_x[d_minus_n].prepare(),
            x_n: srs.h_positive_x[tmp.n].prepare(),
            alpha: srs.h_positive_x_alpha[0].prepare(),
        })
    }

    pub fn new_batch(&self, use_advice: bool) -> Batch<E, C> {
        Batch {
            precomp: self,

            acc: E::Fqk::one(),

            h: E::G1::zero(),
            x: E::G1::zero(),
            x_d: E::G1::zero(),
            x_neg_d: E::G1::zero(),
            x_d_minus_n: E::G1::zero(),
            x_n: E::G1::zero(),
            alpha: E::G1::zero(),

            use_advice,
            previous_s: vec![],
        }
    }
}

pub struct Advice<E: Engine> {
    // [s(z, x) z^n] G
    c: E::G1Affine,
    // s(z, y)
    v: Vec<E::Fr>,
    // [\frac{s(z, x) z^n - s(z, y) z^n}{x - y}] G
    c_prime: Vec<E::G1Affine>,
    // [\frac{s(x, y) x^n - s(z, y) x^n}{x - z}] G
    s_prime: Vec<E::G1Affine>,

    // [\frac{s(w, x) w^n - s(w, y) w^n}{x - w}] G
    opening: E::G1Affine,
}

pub struct Batch<'a, E: Engine, C: Circuit<E> + 'a> {
    precomp: &'a Precomp<'a, E, C>,

    acc: E::Fqk,

    h: E::G1,
    x: E::G1,
    x_d: E::G1,
    x_neg_d: E::G1,
    x_d_minus_n: E::G1,
    x_n: E::G1,
    alpha: E::G1,

    use_advice: bool,
    previous_s: Vec<(E::G1Affine, E::Fr)>,
}

impl<'a, E: Engine, C: Circuit<E> + 'a> Batch<'a, E, C> {
    pub fn add_proof(
        &mut self,
        proof: &Proof<E>,
        inputs: &[E::Fr],
    ) -> Result<bool, SynthesisError> {
        // TODO: accept a transcript from the public API instead
        let mut transcript = Transcript::new(&[]);

        transcript.commit_point(&proof.a_prime);
        transcript.commit_point(&proof.a_r);
        transcript.commit_point(&proof.a_l);
        transcript.commit_point(&proof.b);
        transcript.commit_point(&proof.b_r);

        let y = transcript.get_challenge_scalar::<E::Fr>();

        transcript.commit_point(&proof.a);
        transcript.commit_point(&proof.s);

        let z = transcript.get_challenge_scalar::<E::Fr>();

        transcript.commit_scalar(&proof.a_v);
        transcript.commit_point(&proof.a_x);
        transcript.commit_point(&proof.a_y);
        transcript.commit_point(&proof.r);
        transcript.commit_point(&proof.t);

        transcript.commit_scalar(&proof.s_v);
        transcript.commit_point(&proof.s_prime);

        // TODO: should just sample randomness instead of using
        // get_challenge_scalar during verification

        {
            // e(A', [x^{d - N}] H) = e(A_R, H)
            let mut r = transcript.get_challenge_scalar::<E::Fr>();
            self.add_x_d_minus_n(&proof.a_prime.into_projective(), &r);

            r.negate();
            self.add_h(&proof.a_r.into_projective(), &r);
        }
        {
            // e(A', [x^{-d}] H) = e(A_L, H)
            let mut r = transcript.get_challenge_scalar::<E::Fr>();
            self.add_x_neg_d(&proof.a_prime.into_projective(), &r);

            r.negate();
            self.add_h(&proof.a_l.into_projective(), &r);
        }
        {
            // e(B, [x^{d}] H) = e(B_R, H)
            let mut r = transcript.get_challenge_scalar::<E::Fr>();
            self.add_x_d(&proof.b.into_projective(), &r);

            r.negate();
            self.add_h(&proof.b_r.into_projective(), &r);
        }
        {
            // TODO: Performance of this could be improved. We effectively
            // recompute [r] A_x twice here. Also, we can amortize the cost
            // of the A_v computation in the scalar field.

            // e(A_x, [x] H) e([-yz] A_x, H) = e(A', H) e(- [A_v] G, H)
            let mut r = transcript.get_challenge_scalar::<E::Fr>();
            self.add_x(&proof.a_x.into_projective(), &r);
            let mut yz = y;
            yz.mul_assign(&z);
            yz.negate();
            self.add_h(&proof.a_x.mul(yz.into_repr()), &r);

            r.negate();
            self.add_h(&proof.a_prime.into_projective(), &r);
            let mut tmp = self.precomp.srs.g_positive_x[0].mul(proof.a_v.into_repr());
            tmp.negate();
            self.add_h(&tmp, &r);
        }
        {
            // TODO: Performance of this could be improved. We effectively
            // recompute [r] A_y twice here. Also, we can amortize the cost
            // of the A_v computation in the scalar field.

            // e(A_y, [x] H) e([-z] A_y, H) = e(A, H) e(- [A_v] G, H)
            let mut r = transcript.get_challenge_scalar::<E::Fr>();
            self.add_x(&proof.a_y.into_projective(), &r);
            let mut z = z;
            z.negate();
            self.add_h(&proof.a_y.mul(z.into_repr()), &r);

            r.negate();
            self.add_h(&proof.a.into_projective(), &r);
            let mut tmp = self.precomp.srs.g_positive_x[0].mul(proof.a_v.into_repr());
            tmp.negate();
            self.add_h(&tmp, &r);
        }
        let r_prepared = proof.r.prepare();
        {
            // e(A + B, [\alpha] H) = e(G, R)
            let mut r = transcript.get_challenge_scalar::<E::Fr>();
            let mut tmp = proof.a.into_projective();
            tmp.add_assign_mixed(&proof.b);
            self.add_alpha(&tmp, &r);

            r.negate();
            self.accumulate(
                &self.precomp.srs.g_positive_x[0].into_projective(),
                &r_prepared,
                &r,
            );
        }
        {
            // e(A + B + 2S, R) e([-2k(y)] G, [\alpha] H) = e(T, H)
            let mut r = transcript.get_challenge_scalar::<E::Fr>();
            let mut tmp = proof.s.into_projective();
            tmp.double();
            tmp.add_assign_mixed(&proof.a);
            tmp.add_assign_mixed(&proof.b);
            self.accumulate(&tmp, &r_prepared, &r);

            // Compute k(y)
            if inputs.len() + 1 != self.precomp.k_map.len() {
                return Ok(false);
            }

            let mut neg_2ky = E::Fr::zero();
            for (exp, coeff) in self
                .precomp
                .k_map
                .iter()
                .zip(Some(E::Fr::one()).iter().chain(inputs.iter()))
            {
                let mut tmp = y.pow(&[*exp]);
                tmp.mul_assign(coeff);
                neg_2ky.add_assign(&tmp);
            }
            neg_2ky.double();
            neg_2ky.negate();

            self.add_alpha(&self.precomp.srs.g_positive_x[0].mul(neg_2ky), &r);

            r.negate();

            self.add_h(&proof.t.into_projective(), &r);
        }

        if self.use_advice {
            self.previous_s.push((proof.s, y));
        } else {
            {
                // e(S', [x] H) e([-z] S', H) = e(S, [x^n] H) e([-S_v] G, H)
                let mut r = transcript.get_challenge_scalar::<E::Fr>();
                self.add_x(&proof.s_prime.into_projective(), &r);
                let mut z: E::Fr = z;
                z.negate();
                self.add_h(&proof.s_prime.mul(z.into_repr()), &r);

                r.negate();

                self.add_x_n(&proof.s.into_projective(), &r);
                let mut tmp = proof.s_v;
                tmp.negate();
                self.add_h(&self.precomp.srs.g_positive_x[0].mul(tmp.into_repr()), &r);
            }

            // Now, let's compute s(z, y) z^n!
            let mut tmp = SxEval::<E>::new(y, self.precomp.n);

            ConstraintSystem::<E>::alloc_input(&mut tmp, || Ok(E::Fr::one())).unwrap();

            self.precomp.circuit.synthesize(&mut tmp)?;

            if tmp.finalize(z, self.precomp.n) != proof.s_v {
                return Ok(false);
            }
        }

        /*
            // Now, let's compute s(z, y) z^n!
            let mut tmp = SyEval::<E>::new(z, self.precomp.n, self.precomp.q);

            ConstraintSystem::<E>::alloc_input(&mut tmp, || Ok(E::Fr::one())).unwrap();

            self.precomp.circuit.synthesize(&mut tmp)?;

            if tmp.finalize(y, self.precomp.n) != proof.s_v {
                return Ok(false)
            }
        */

        Ok(true)
    }

    /// Returns a boolean that is true iff all of the accumulated
    /// proofs are valid.
    pub fn check_all(mut self, advice: Option<&Advice<E>>) -> bool {
        if self.use_advice {
            let advice = advice.expect("check_all called without advice as expected");
            /*
            pub struct Advice<E: Engine> {
                // [s(z, x) z^n] G
                c: E::G1Affine,
                // s(z, y)
                v: Vec<E::Fr>,
                // [\frac{s(z, x) z^n - s(z, y) z^n}{x - y}] G
                c_prime: Vec<E::G1Affine>,
                // [\frac{s(x, y) x^n - s(z, y) x^n}{x - z}] G
                s_prime: Vec<E::G1Affine>,

                // [\frac{s(z, x) z^n - s(z, w) z^n}{x - w}] G
                opening: E::G1Affine,
            }
            */

            // First, commit to all of the (S, y) from the previous proofs
            let mut transcript = Transcript::new(&[]);
            for &(ref s, ref y) in &self.previous_s {
                transcript.commit_point(s);
                transcript.commit_scalar(y);
            }

            // Get a z
            let z: E::Fr = transcript.get_challenge_scalar();

            // Feed in C to get w
            transcript.commit_point(&advice.c);
            let w: E::Fr = transcript.get_challenge_scalar();

            let previous_s = self.previous_s.clone();

            assert_eq!(previous_s.len(), advice.c_prime.len());
            assert_eq!(previous_s.len(), advice.s_prime.len());
            assert_eq!(previous_s.len(), advice.v.len());

            for (((v, c_prime), s_prime), &(ref s, ref y)) in advice.v.iter()
                .zip(advice.c_prime.iter())
                .zip(advice.s_prime.iter())
                .zip(previous_s.iter())
            {
                {
                    // Test opening of the commitment with y
                    // e(C', [x] H) e([-y] C', H) = e(C - [v] G, H)
                    let mut r: E::Fr = transcript.get_challenge_scalar();

                    self.add_x(&c_prime.into_projective(), &r);
                    let mut point = *y;
                    point.negate();
                    self.add_h(&c_prime.mul(point.into_repr()), &r);

                    r.negate();

                    let mut tmp = self.precomp.srs.g_positive_x[0].mul(v.into_repr());
                    tmp.negate();
                    tmp.add_assign_mixed(&advice.c);

                    self.add_h(&tmp, &r);
                }
                {
                    // Test opening of S with z
                    // e(S', [x] H) e([-z] S', H) = e(S, [x^n] H) e([-v] G, H)
                    let mut r: E::Fr = transcript.get_challenge_scalar();

                    self.add_x(&s_prime.into_projective(), &r);
                    let mut point = z;
                    point.negate();
                    self.add_h(&s_prime.mul(point.into_repr()), &r);

                    r.negate();

                    self.add_x_n(&s.into_projective(), &r);
                    let mut tmp = self.precomp.srs.g_positive_x[0].mul(v.into_repr());
                    tmp.negate();

                    self.add_h(&tmp, &r);
                }
            }

            let v = {
                // Now, let's compute s(z, w) z^n!
                let mut tmp = SyEval::<E>::new(z, self.precomp.n, self.precomp.q);

                ConstraintSystem::<E>::alloc_input(&mut tmp, || Ok(E::Fr::one())).unwrap();

                self.precomp.circuit.synthesize(&mut tmp).unwrap(); // TODO

                tmp.finalize(w, self.precomp.n)
            };

            {
                // Test opening of the commitment with y
                // e(C', [x] H) e([-y] C', H) = e(C - [v] G, H)
                let mut r: E::Fr = transcript.get_challenge_scalar();

                self.add_x(&advice.opening.into_projective(), &r);
                let mut point = w;
                point.negate();
                self.add_h(&advice.opening.mul(point.into_repr()), &r);

                r.negate();

                let mut tmp = self.precomp.srs.g_positive_x[0].mul(v.into_repr());
                tmp.negate();
                tmp.add_assign_mixed(&advice.c);

                self.add_h(&tmp, &r);
            }
        }

        self.check_is_zero()
    }

    pub fn create_advice(&self) -> Advice<E> {
        assert!(self.use_advice); // TODO

        // First, commit to all of the (S, y) from the previous proofs
        let mut transcript = Transcript::new(&[]);
        for &(ref s, ref y) in &self.previous_s {
            transcript.commit_point(s);
            transcript.commit_scalar(y);
        }

        // Get a z
        let z: E::Fr = transcript.get_challenge_scalar();

        let poly = {
            let mut tmp = SyEval::<E>::new(z, self.precomp.n, self.precomp.q);
            ConstraintSystem::<E>::alloc_input(&mut tmp, || Ok(E::Fr::one())).unwrap();
            self.precomp.circuit.synthesize(&mut tmp).unwrap(); // TODO
            tmp.poly()
        };

        let c = {
            // C = [s(z, x) z^n] G
            let mut c = multiexp(&self.precomp.srs.g_positive_x[0..poly.len()], &poly[..]);
            c.mul_assign(
                z.pow(&[self.precomp.n as u64])
            );

            c.into_affine()
        };

        transcript.commit_point(&c);
        let w: E::Fr = transcript.get_challenge_scalar();

        // opening = [\frac{s(z, x) z^n - s(z, w) z^n}{x - w}] G
        let opening = {
            let poly = kate_divison(
                poly.iter(),
                w,
            );
            let mut opening = multiexp(&self.precomp.srs.g_positive_x[0..poly.len()], &poly[..]);
            opening.mul_assign(z.pow(&[self.precomp.n as u64]).into_repr());
            opening.into_affine()
        };

        let mut c_prime = vec![];
        let mut s_prime = vec![];
        let mut v = vec![];

        for &(ref s, ref y) in self.previous_s.iter() {
            // Create opening of C at y
            let mut v_temp = E::Fr::zero();
            {
                let mut tmp = E::Fr::one();
                for &coeff in &poly {
                    let mut coeff = coeff;
                    coeff.mul_assign(&tmp);
                    v_temp.add_assign(&coeff);
                    tmp.mul_assign(y);
                }
                v_temp.mul_assign(&z.pow(&[self.precomp.n as u64]));
            }

            v.push(v_temp);

            c_prime.push({
                let poly = kate_divison(
                    poly.iter(),
                    *y,
                );
                let mut opening = multiexp(&self.precomp.srs.g_positive_x[0..poly.len()], &poly[..]);
                opening.mul_assign(z.pow(&[self.precomp.n as u64]).into_repr());
                opening.into_affine()
            });

            s_prime.push({
                let (s_poly_negative, s_poly_positive) = {
                    let mut tmp = SxEval::<E>::new(*y, self.precomp.n);
                    ConstraintSystem::<E>::alloc_input(&mut tmp, || Ok(E::Fr::one())).unwrap();
                    self.precomp.circuit.synthesize(&mut tmp).unwrap(); // TODO
                    tmp.poly()
                };
                let point = z;
                let poly = kate_divison(
                    s_poly_negative
                        .iter()
                        .rev()
                        .chain_ext(Some(E::Fr::zero()).iter())
                        .chain_ext(s_poly_positive.iter()),
                    point,
                );
                multiexp(&self.precomp.srs.g_positive_x[0..poly.len()], &poly[..]).into_affine()
            });
        }

        Advice {
            c,
            opening,
            c_prime,
            s_prime,
            v
        }
    }

    #[must_use]
    fn check_is_zero(self) -> bool {
        let mut acc = self.acc;
        acc.mul_assign(&E::miller_loop(&[
            (&self.h.into_affine().prepare(), &self.precomp.h),
            (&self.x.into_affine().prepare(), &self.precomp.x),
            (&self.x_d.into_affine().prepare(), &self.precomp.x_d),
            (&self.x_neg_d.into_affine().prepare(), &self.precomp.x_neg_d),
            (
                &self.x_d_minus_n.into_affine().prepare(),
                &self.precomp.x_d_minus_n,
            ),
            (&self.x_n.into_affine().prepare(), &self.precomp.x_n),
            (&self.alpha.into_affine().prepare(), &self.precomp.alpha),
        ]));
        // TODO: could fold the `accumulate` work into this as well

        E::final_exponentiation(&acc).unwrap() == E::Fqk::one()
    }

    fn accumulate(&mut self, g: &E::G1, h: &<E::G2Affine as CurveAffine>::Prepared, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());

        self.acc
            .mul_assign(&E::miller_loop(&[(&tmp.into_affine().prepare(), h)]));
    }

    fn add_h(&mut self, g: &E::G1, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());
        self.h.add_assign(&tmp);
    }

    fn add_x(&mut self, g: &E::G1, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());
        self.x.add_assign(&tmp);
    }

    fn add_x_d(&mut self, g: &E::G1, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());
        self.x_d.add_assign(&tmp);
    }

    fn add_x_neg_d(&mut self, g: &E::G1, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());
        self.x_neg_d.add_assign(&tmp);
    }

    fn add_x_d_minus_n(&mut self, g: &E::G1, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());
        self.x_d_minus_n.add_assign(&tmp);
    }

    fn add_x_n(&mut self, g: &E::G1, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());
        self.x_n.add_assign(&tmp);
    }

    fn add_alpha(&mut self, g: &E::G1, r: &E::Fr) {
        let mut tmp = *g;
        tmp.mul_assign(r.into_repr());
        self.alpha.add_assign(&tmp);
    }
}

/*
s(X, Y) =   \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q+N-i} u_{i,q} X^{-i}
          + \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q+N} v_{i,q} X^{i}
          + \sum\limits_{i=1}^N \sum\limits_{q=1}^Q Y^{q+N} w_{i,q} X^{i+N}
          - \sum\limits_{i=1}^N Y^i X^{i+N}
*/
struct SyEval<E: Engine> {
    x: E::Fr,

    max_n: usize,

    current_n: usize,
    current_q: usize,

    // x^{-1}, ..., x^{-N}
    a: Vec<E::Fr>,

    // x^1, ..., x^{N}
    b: Vec<E::Fr>,

    // x^{N+1}, ..., x^{2*N}
    c: Vec<E::Fr>,

    // coeffs for y^0, y^1, ..., y^{N+Q}
    coeffs: Vec<E::Fr>,
}

impl<E: Engine> SyEval<E> {
    fn new(x: E::Fr, n: usize, q: usize) -> Self {
        let xinv = x.inverse().unwrap();
        let mut tmp = E::Fr::one();
        let mut a = vec![E::Fr::zero(); n];
        for a in &mut a {
            tmp.mul_assign(&xinv); // tmp = x^{-i}
            *a = tmp;
        }

        let mut tmp = E::Fr::one();
        let mut b = vec![E::Fr::zero(); n];
        for b in &mut b {
            tmp.mul_assign(&x); // tmp = x^{i}
            *b = tmp;
        }

        let mut coeffs = vec![E::Fr::zero(); n + q + 1];

        let mut c = vec![E::Fr::zero(); n];
        for (c, coeff) in c.iter_mut().zip(&mut coeffs[1..]) {
            tmp.mul_assign(&x); // tmp = x^{i+N}
            *c = tmp;

            // - \sum\limits_{i=1}^N Y^i X^{i+N}
            let mut tmp = tmp;
            tmp.negate();
            *coeff = tmp;
        }

        SyEval {
            x,
            a,
            b,
            c,
            coeffs,
            current_n: 0,
            current_q: 0,
            max_n: n,
        }
    }

    // TODO: we already have max_n
    fn finalize(self, y: E::Fr, n: usize) -> E::Fr {
        let mut acc = E::Fr::zero();

        let mut tmp = E::Fr::one();
        for mut coeff in self.coeffs {
            coeff.mul_assign(&tmp);
            acc.add_assign(&coeff);
            tmp.mul_assign(&y);
        }

        acc.mul_assign(&self.x.pow(&[n as u64]));

        acc
    }

    fn poly(self) -> Vec<E::Fr> {
        self.coeffs
    }
}

impl<E: Engine> ConstraintSystem<E> for SyEval<E> {
    fn alloc_input<F>(&mut self, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let (a, _, _) = self.multiply(|| unreachable!())?;

        self.enforce(LinearCombination::from(a));

        Ok(a)
    }

    fn multiply<F>(&mut self, _: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>,
    {
        let index = self.current_n;
        self.current_n += 1;

        Ok((Variable::A(index), Variable::B(index), Variable::C(index)))
    }

    fn enforce(&mut self, lc: LinearCombination<E>) {
        self.current_q += 1;

        for (var, mut coeff) in lc.0 {
            match var {
                Variable::A(index) => {
                    // Y^{q+N-i} += X^{-i} * coeff
                    coeff.mul_assign(&self.a[index]);
                    let yindex = self.current_q + self.max_n - (index + 1);
                    self.coeffs[yindex].add_assign(&coeff);
                }
                Variable::B(index) => {
                    // Y^{q+N} += X^{i} * coeff
                    coeff.mul_assign(&self.b[index]);
                    let yindex = self.current_q + self.max_n;
                    self.coeffs[yindex].add_assign(&coeff);
                }
                Variable::C(index) => {
                    // Y^{q+N} += X^{i+N} * coeff
                    coeff.mul_assign(&self.c[index]);
                    let yindex = self.current_q + self.max_n;
                    self.coeffs[yindex].add_assign(&coeff);
                }
            }
        }
    }
}

/*
s(X, Y) =   \sum\limits_{i=1}^N u_i(Y) X^{-i} Y^{-i}
          + \sum\limits_{i=1}^N v_i(Y) X^{i}
          + \sum\limits_{i=1}^N w_i(Y) X^{i+N}

where

    u_i(Y) =        \sum\limits_{q=1}^Q Y^{q+N} u_{i,q}
    v_i(Y) =        \sum\limits_{q=1}^Q Y^{q+N} v_{i,q}
    w_i(Y) = -Y^i + \sum\limits_{q=1}^Q Y^{q+N} w_{i,q}

*/
struct SxEval<E: Engine> {
    current_n: usize,

    y: E::Fr,

    // current value of y^{q+N}
    yqn: E::Fr,

    // x^{-i} y^{-i} (\sum\limits_{q=1}^Q y^{q+N} u_{q,i})
    u: Vec<E::Fr>,
    // x^{i} (\sum\limits_{q=1}^Q y^{q+N} v_{q,i})
    v: Vec<E::Fr>,
    // x^{i+N} (-y^i + \sum\limits_{q=1}^Q y^{q+N} w_{q,i})
    w: Vec<E::Fr>,
}

impl<E: Engine> SxEval<E> {
    fn new(y: E::Fr, n: usize) -> Self {
        let yqn = y.pow(&[n as u64]);

        let u = vec![E::Fr::zero(); n];
        let v = vec![E::Fr::zero(); n];
        let mut w = vec![E::Fr::zero(); n];

        let mut tmp = y;
        for w in &mut w {
            let mut new = tmp;
            new.negate();
            *w = new;
            tmp.mul_assign(&y);
        }

        SxEval {
            current_n: 0,
            y,
            yqn,
            u,
            v,
            w,
        }
    }

    fn poly(mut self) -> (Vec<E::Fr>, Vec<E::Fr>) {
        let yinv = self.y.inverse().unwrap();

        let mut tmp = yinv;
        for u in &mut self.u {
            u.mul_assign(&tmp);
            tmp.mul_assign(&yinv);
        }

        self.v.extend(self.w);

        (self.u, self.v)
    }

    fn finalize(self, x: E::Fr, n: usize) -> E::Fr {
        let mut xy_inv = x;
        xy_inv.mul_assign(&self.y);
        xy_inv = xy_inv.inverse().unwrap(); // TODO

        let mut tmp = xy_inv;

        let mut acc = E::Fr::zero();
        for mut u in self.u {
            u.mul_assign(&tmp);
            acc.add_assign(&u);
            tmp.mul_assign(&xy_inv);
        }

        let mut tmp = x;
        for mut v in self.v {
            v.mul_assign(&tmp);
            acc.add_assign(&v);
            tmp.mul_assign(&x);
        }
        for mut w in self.w {
            w.mul_assign(&tmp);
            acc.add_assign(&w);
            tmp.mul_assign(&x);
        }

        acc.mul_assign(&x.pow(&[n as u64]));

        acc
    }
}

impl<E: Engine> ConstraintSystem<E> for SxEval<E> {
    fn alloc_input<F>(&mut self, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
    {
        let (a, _, _) = self.multiply(|| unreachable!())?;

        self.enforce(LinearCombination::from(a));

        Ok(a)
    }

    fn multiply<F>(&mut self, _: F) -> Result<(Variable, Variable, Variable), SynthesisError>
    where
        F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>,
    {
        let index = self.current_n;
        self.current_n += 1;

        Ok((Variable::A(index), Variable::B(index), Variable::C(index)))
    }

    fn enforce(&mut self, lc: LinearCombination<E>) {
        self.yqn.mul_assign(&self.y);

        for (var, mut coeff) in lc.0 {
            coeff.mul_assign(&self.yqn);

            match var {
                Variable::A(index) => {
                    self.u[index].add_assign(&coeff);
                }
                Variable::B(index) => {
                    self.v[index].add_assign(&coeff);
                }
                Variable::C(index) => {
                    self.w[index].add_assign(&coeff);
                }
            }
        }
    }
}

pub fn create_proof<E: Engine, C: Circuit<E>>(
    circuit: &C,
    srs: &SRS<E>,
) -> Result<Proof<E>, SynthesisError> {
    struct WireAssignment<E: Engine> {
        a: Vec<E::Fr>,
        b: Vec<E::Fr>,
        c: Vec<E::Fr>,
        current_n: usize,
    }

    impl<E: Engine> ConstraintSystem<E> for WireAssignment<E> {
        fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
        where
            F: FnOnce() -> Result<E::Fr, SynthesisError>,
        {
            let (a, _, _) = self.multiply(|| Ok((value()?, E::Fr::zero(), E::Fr::zero())))?;

            Ok(a)
        }

        fn multiply<F>(
            &mut self,
            values: F,
        ) -> Result<(Variable, Variable, Variable), SynthesisError>
        where
            F: FnOnce() -> Result<(E::Fr, E::Fr, E::Fr), SynthesisError>,
        {
            let index = self.current_n;
            self.current_n += 1;

            let (a, b, c) = values()?;
            self.a.push(a);
            self.b.push(b);
            self.c.push(c);

            Ok((Variable::A(index), Variable::B(index), Variable::C(index)))
        }

        fn enforce(&mut self, _lc: LinearCombination<E>) {
            // We don't care about linear combinations yet.
        }

        fn get_value(&self, var: Variable) -> Result<E::Fr, ()> {
            Ok(match var {
                Variable::A(index) => self.a[index],
                Variable::B(index) => self.b[index],
                Variable::C(index) => self.c[index],
            })
        }
    }

    let mut wires = WireAssignment {
        a: vec![],
        b: vec![],
        c: vec![],
        current_n: 0,
    };

    ConstraintSystem::<E>::alloc_input(&mut wires, || Ok(E::Fr::one())).unwrap();

    circuit.synthesize(&mut wires)?;

    let n = wires.current_n;

    // TODO: Check that n isn't too large

    // Construct the transcript with the verifier
    // TODO: accept from input
    let mut transcript = Transcript::new(&[]);

    // A' = [r_1(x, 1)] G
    let a_prime = multiexp(&srs.g_positive_x[1..(n + 1)], &wires.a).into_affine();

    // A_R = [r_1(x, 1) x^{d - N}] G
    let a_r = multiexp(&srs.g_positive_x[(1 + srs.d - n)..], &wires.a).into_affine();

    // A_L = [r_1(x, 1) x^{-d}] G
    let a_l = multiexp(
        &srs.g_negative_x[(srs.d - n)..(srs.d)],
        wires.a.iter().rev(),
    ).into_affine();

    // B = [r_2(x)] G
    let b = multiexp(
        &srs.g_negative_x[1..(1 + 2 * n)],
        wires.b.iter().chain_ext(wires.c.iter()),
    ).into_affine();

    // B_R = [r_2(x) x^{d}] G
    let b_r = multiexp(
        &srs.g_positive_x[(srs.d - 2 * n)..(srs.d)],
        wires.b.iter().chain_ext(wires.c.iter()).rev(),
    ).into_affine();

    transcript.commit_point(&a_prime);
    transcript.commit_point(&a_r);
    transcript.commit_point(&a_l);
    transcript.commit_point(&b);
    transcript.commit_point(&b_r);

    let y = transcript.get_challenge_scalar::<E::Fr>();

    let mut r1xy = wires.a.clone();
    {
        let mut tmp = y;
        for coeff in &mut r1xy {
            coeff.mul_assign(&tmp);
            tmp.mul_assign(&y);
        }
    }

    // A = [r_1(x, y)] G
    let a = multiexp(&srs.g_positive_x[1..(n + 1)], &r1xy).into_affine();

    let (s_poly_negative, s_poly_positive) = {
        let mut tmp = SxEval::<E>::new(y, n);
        ConstraintSystem::<E>::alloc_input(&mut tmp, || Ok(E::Fr::one())).unwrap();
        circuit.synthesize(&mut tmp)?;
        tmp.poly()
    };

    // S = [s(x, y)] G
    let s = multiexp(
        srs.g_negative_x[1..(n + 1)]
            .iter()
            .chain_ext(srs.g_positive_x[1..(2 * n + 1)].iter()),
        s_poly_negative.iter().chain_ext(s_poly_positive.iter()),
    ).into_affine();

    transcript.commit_point(&a);
    transcript.commit_point(&s);

    let z = transcript.get_challenge_scalar::<E::Fr>();

    let mut s_v = E::Fr::zero();

    {
        let mut tmp = E::Fr::one();
        for &a in s_poly_negative
            .iter()
            .rev()
            .chain(Some(E::Fr::zero()).iter())
            .chain(s_poly_positive.iter())
        {
            let mut a = a;
            a.mul_assign(&tmp);
            s_v.add_assign(&a);
            tmp.mul_assign(&z);
        }
    }

    let s_prime = {
        let point = z;
        let poly = kate_divison(
            s_poly_negative
                .iter()
                .rev()
                .chain_ext(Some(E::Fr::zero()).iter())
                .chain_ext(s_poly_positive.iter()),
            point,
        );
        multiexp(&srs.g_positive_x[0..poly.len()], &poly[..]).into_affine()
    };

    let mut a_v = E::Fr::zero();

    {
        let mut tmp = z;
        for &a in &r1xy {
            let mut a = a;
            a.mul_assign(&tmp);
            a_v.add_assign(&a);
            tmp.mul_assign(&z);
        }
    }

    let a_x = {
        let mut point = z;
        point.mul_assign(&y);
        let poly = kate_divison(
            Some(&E::Fr::zero()).into_iter().chain_ext(wires.a.iter()),
            point,
        );
        multiexp(&srs.g_positive_x[0..poly.len()], &poly[..]).into_affine()
    };

    drop(wires.a);

    let a_y = {
        let point = z;
        let poly = kate_divison(
            Some(&E::Fr::zero()).into_iter().chain_ext(r1xy.iter()),
            point,
        );
        multiexp(&srs.g_positive_x[0..poly.len()], &poly[..]).into_affine()
    };

    let r = multiexp(
        srs.h_positive_x_alpha[1..(n + 1)]
            .iter()
            .chain_ext(srs.h_negative_x_alpha[1..(2 * n + 1)].iter()),
        r1xy.iter()
            .chain_ext(wires.b.iter())
            .chain_ext(wires.c.iter()),
    ).into_affine();

    // Let's compute t(X, y)
    let mut r_x_y = wires.b;
    r_x_y.extend(wires.c);
    r_x_y.reverse();
    r_x_y.push(E::Fr::zero()); // constant term
    r_x_y.extend(r1xy);
    r_x_y.resize(4 * n + 1, E::Fr::zero());

    let mut r_x_y_prime = r_x_y.clone();
    // Add 2s(x, y)
    for (r, mut s) in r_x_y_prime[0..(2 * n)]
        .iter_mut()
        .rev()
        .zip(s_poly_negative)
    {
        s.double();
        r.add_assign(&s);
    }
    for (r, mut s) in r_x_y_prime[(2 * n + 1)..].iter_mut().zip(s_poly_positive) {
        s.double();
        r.add_assign(&s);
    }

    let t_x_y = multiply_polynomials::<E>(r_x_y, r_x_y_prime);

    assert_eq!(t_x_y.len(), 8 * n + 1);

    // // constant term should be 2*k_y
    // t_x_y[4 * n].sub_assign(&k_y);
    // t_x_y[4 * n].sub_assign(&k_y);
    // assert!(t_x_y[4 * n].is_zero());

    // Evaluate t(x, y) in alpha
    let t = multiexp(
        srs.g_positive_x_alpha[0..(4 * n)]
            .iter()
            .chain_ext(srs.g_negative_x_alpha[0..(4 * n)].iter()),
        t_x_y[(4 * n + 1)..]
            .iter()
            .chain_ext(t_x_y[0..4 * n].iter().rev()),
    ).into_affine();

    Ok(Proof {
        a_prime,
        a_r,
        a_l,
        b,
        b_r,

        a,
        s,

        a_v,
        a_x,
        a_y,
        r,
        t,

        s_v,
        s_prime,
    })
}

#[test]
fn my_fun_circuit_test() {
    use pairing::bls12_381::{Bls12, Fr};
    use pairing::PrimeField;

    struct MyCircuit;

    impl<E: Engine> Circuit<E> for MyCircuit {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let (a, b, _) = cs.multiply(|| {
                Ok((
                    E::Fr::from_str("10").unwrap(),
                    E::Fr::from_str("20").unwrap(),
                    E::Fr::from_str("200").unwrap(),
                ))
            })?;

            cs.enforce(LinearCombination::from(a) + a - b);

            let multiplier = cs.alloc_input(|| Ok(E::Fr::from_str("20").unwrap()))?;

            cs.enforce(LinearCombination::from(b) - multiplier);

            Ok(())
        }
    }

    let srs = SRS::<Bls12>::new(
        20,
        Fr::from_str("22222").unwrap(),
        Fr::from_str("33333333").unwrap(),
    );
    let proof = create_proof(&MyCircuit, &srs).unwrap();

    let precomp = Precomp::new(MyCircuit, &srs).unwrap();
    let mut batch = precomp.new_batch(false);

    assert_eq!(
        batch
            .add_proof(&proof, &[Fr::from_str("20").unwrap()])
            .unwrap(),
        true
    );

    assert!(batch.check_all(None));
}
