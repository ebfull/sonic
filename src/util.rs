use merlin::Transcript;
use pairing::{CurveAffine, CurveProjective, Engine, Field, PrimeField, PrimeFieldRepr};
use std::io;
use SynthesisError;

pub trait TranscriptProtocol {
    fn commit_point<G: CurveAffine>(&mut self, point: &G);
    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F);
    fn get_challenge_scalar<F: PrimeField>(&mut self) -> F;
}

impl TranscriptProtocol for Transcript {
    fn commit_point<G: CurveAffine>(&mut self, point: &G) {
        self.commit_bytes(b"point", point.into_compressed().as_ref());
    }

    fn commit_scalar<F: PrimeField>(&mut self, scalar: &F) {
        let mut v = vec![];
        scalar.into_repr().write_le(&mut v).unwrap();

        self.commit_bytes(b"scalar", &v);
    }

    fn get_challenge_scalar<F: PrimeField>(&mut self) -> F {
        loop {
            let mut repr: F::Repr = Default::default();
            repr.read_be(TranscriptReader(self)).unwrap();

            if let Ok(result) = F::from_repr(repr) {
                return result;
            }
        }
    }
}

struct TranscriptReader<'a>(&'a mut Transcript);

impl<'a> io::Read for TranscriptReader<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.challenge_bytes(b"read", buf);

        Ok(buf.len())
    }
}

pub trait ChainExt: Iterator {
    fn chain_ext<U>(self, other: U) -> Chain<Self, U::IntoIter>
    where
        Self: Sized,
        U: IntoIterator<Item = Self::Item>,
    {
        Chain {
            t: self,
            u: other.into_iter(),
        }
    }
}

impl<I: Iterator> ChainExt for I {}

#[derive(Clone)]
pub struct Chain<T, U> {
    t: T,
    u: U,
}

impl<T, U> Iterator for Chain<T, U>
where
    T: Iterator,
    U: Iterator<Item = T::Item>,
{
    type Item = T::Item;

    fn next(&mut self) -> Option<T::Item> {
        match self.t.next() {
            Some(v) => Some(v),
            None => match self.u.next() {
                Some(v) => Some(v),
                None => None,
            },
        }
    }
}

impl<T, U> ExactSizeIterator for Chain<T, U>
where
    T: Iterator,
    U: Iterator<Item = T::Item>,
    T: ExactSizeIterator,
    U: ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.t.len() + self.u.len()
    }
}

impl<T, U> DoubleEndedIterator for Chain<T, U>
where
    T: Iterator,
    U: Iterator<Item = T::Item>,
    T: DoubleEndedIterator,
    U: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<T::Item> {
        match self.u.next_back() {
            Some(v) => Some(v),
            None => match self.t.next_back() {
                Some(v) => Some(v),
                None => None,
            },
        }
    }
}

pub fn multiexp<
    'a,
    G: CurveAffine,
    IB: IntoIterator<Item = &'a G>,
    IS: IntoIterator<Item = &'a G::Scalar>,
>(
    g: IB,
    s: IS,
) -> G::Projective
where
    IB::IntoIter: ExactSizeIterator + Clone,
    IS::IntoIter: ExactSizeIterator,
{
    let g = g.into_iter();
    let s = s.into_iter();
    assert_eq!(g.len(), s.len());

    let c = if s.len() < 32 {
        3u32
    } else {
        (f64::from(s.len() as u32)).ln().ceil() as u32
    };

    // Convert all of the scalars into representations
    let mut s = s.map(|s| s.into_repr()).collect::<Vec<_>>();

    let mut windows = vec![];
    let mut buckets = vec![];

    let mask = (1u64 << c) - 1u64;
    let mut cur = 0;
    while cur <= <G::Engine as Engine>::Fr::NUM_BITS {
        let mut acc = G::Projective::zero();

        buckets.truncate(0);
        buckets.resize((1 << c) - 1, G::Projective::zero());

        let g = g.clone();

        for (s, g) in s.iter_mut().zip(g) {
            let index = (s.as_ref()[0] & mask) as usize;

            if index != 0 {
                buckets[index - 1].add_assign_mixed(g);
            }

            s.shr(c as u32);
        }

        let mut running_sum = G::Projective::zero();
        for exp in buckets.iter().rev() {
            running_sum.add_assign(exp);
            acc.add_assign(&running_sum);
        }

        windows.push(acc);

        cur += c;
    }

    let mut acc = G::Projective::zero();

    for window in windows.into_iter().rev() {
        for _ in 0..c {
            acc.double();
        }

        acc.add_assign(&window);
    }

    acc
}

/// Divides polynomial `a` in `x` by `x - b` with
/// no remainder.
pub fn kate_divison<'a, F: Field, I: IntoIterator<Item = &'a F>>(a: I, mut b: F) -> Vec<F>
where
    I::IntoIter: DoubleEndedIterator + ExactSizeIterator,
{
    b.negate();
    let a = a.into_iter();

    let mut q = vec![F::zero(); a.len() - 1];

    let mut tmp = F::zero();
    for (q, r) in q.iter_mut().rev().zip(a.rev()) {
        let mut lead_coeff = *r;
        lead_coeff.sub_assign(&tmp);
        *q = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
    }

    q
}

pub fn multiply_polynomials<E: Engine>(mut a: Vec<E::Fr>, mut b: Vec<E::Fr>) -> Vec<E::Fr> {
    let result_len = a.len() + b.len() - 1;

    // Compute the size of our evaluation domain
    let mut m = 1;
    let mut exp = 0;
    while m < result_len {
        m *= 2;
        exp += 1;

        // The pairing-friendly curve may not be able to support
        // large enough (radix2) evaluation domains.
        if exp >= E::Fr::S {
            panic!("polynomial too large")
        }
    }

    // Compute omega, the 2^exp primitive root of unity
    let mut omega = E::Fr::root_of_unity();
    for _ in exp..E::Fr::S {
        omega.square();
    }

    // Extend with zeroes
    a.resize(m, E::Fr::zero());
    b.resize(m, E::Fr::zero());

    serial_fft::<E>(&mut a[..], &omega, exp);
    serial_fft::<E>(&mut b[..], &omega, exp);

    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign(b);
    }

    serial_fft::<E>(&mut a[..], &omega.inverse().unwrap(), exp);

    a.truncate(result_len);

    let minv = E::Fr::from_str(&format!("{}", m))
        .unwrap()
        .inverse()
        .unwrap();

    for a in a.iter_mut() {
        a.mul_assign(&minv);
    }

    a
}

fn serial_fft<E: Engine>(a: &mut [E::Fr], omega: &E::Fr, log_n: u32) {
    fn bitreverse(mut n: u32, l: u32) -> u32 {
        let mut r = 0;
        for _ in 0..l {
            r = (r << 1) | (n & 1);
            n >>= 1;
        }
        r
    }

    let n = a.len() as u32;
    assert_eq!(n, 1 << log_n);

    for k in 0..n {
        let rk = bitreverse(k, log_n);
        if k < rk {
            a.swap(rk as usize, k as usize);
        }
    }

    let mut m = 1;
    for _ in 0..log_n {
        let w_m = omega.pow(&[(n / (2 * m)) as u64]);

        let mut k = 0;
        while k < n {
            let mut w = E::Fr::one();
            for j in 0..m {
                let mut t = a[(k + j + m) as usize];
                t.mul_assign(&w);
                let mut tmp = a[(k + j) as usize];
                tmp.sub_assign(&t);
                a[(k + j + m) as usize] = tmp;
                a[(k + j) as usize].add_assign(&t);
                w.mul_assign(&w_m);
            }

            k += 2 * m;
        }

        m *= 2;
    }
}

pub trait OptionExt<T> {
    fn get(self) -> Result<T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn get(self) -> Result<T, SynthesisError> {
        match self {
            Some(t) => Ok(t),
            None => Err(SynthesisError::AssignmentMissing),
        }
    }
}
