use pairing::{CurveAffine, CurveProjective, Engine, Field, PrimeField};

pub struct SRS<E: Engine> {
    pub d: usize,

    // g^{x^0}, g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}}
    pub g_negative_x: Vec<E::G1Affine>,

    // g^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}}
    pub g_positive_x: Vec<E::G1Affine>,

    // g^{x^0}, g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}}
    pub h_negative_x: Vec<E::G2Affine>,

    // g^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}}
    pub h_positive_x: Vec<E::G2Affine>,

    // alpha*(g^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}})
    pub g_negative_x_alpha: Vec<E::G1Affine>,

    // alpha*(g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}})
    pub g_positive_x_alpha: Vec<E::G1Affine>,

    // alpha*(h^{x^0}, h^{x^{-1}}, g^{x^{-2}}, ..., g^{x^{-d}})
    pub h_negative_x_alpha: Vec<E::G2Affine>,

    // alpha*(h^{x^0}, g^{x^{1}}, g^{x^{2}}, ..., g^{x^{d}})
    pub h_positive_x_alpha: Vec<E::G2Affine>,
}

impl<E: Engine> SRS<E> {
    pub fn new(d: usize, x: E::Fr, alpha: E::Fr) -> Self {
        fn table<C: CurveAffine>(mut cur: C::Scalar, step: C::Scalar, num: usize) -> Vec<C> {
            let mut v = vec![];
            for _ in 0..num {
                v.push(C::one().mul(cur.into_repr()).into_affine());
                cur.mul_assign(&step);
            }
            v
        }

        let x_inv = x.inverse().unwrap();

        let mut x_alpha = x;
        x_alpha.mul_assign(&alpha);

        let mut inv_x_alpha = x_inv;
        inv_x_alpha.mul_assign(&alpha);

        SRS {
            d: d,
            g_negative_x: table(E::Fr::one(), x_inv, d + 1),
            g_positive_x: table(E::Fr::one(), x, d + 1),

            h_negative_x: table(E::Fr::one(), x_inv, d + 1),
            h_positive_x: table(E::Fr::one(), x, d + 1),

            g_negative_x_alpha: table(inv_x_alpha, x_inv, d),
            g_positive_x_alpha: table(x_alpha, x, d),

            h_negative_x_alpha: table(alpha, x_inv, d + 1),
            h_positive_x_alpha: table(alpha, x, d + 1),
        }
    }
}
