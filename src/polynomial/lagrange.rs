
use crate::polynomial::Field;
use crate::polynomial::univariate::DensePolynomial;
use crate::polynomial::UVPolynomial;

struct LagrangePolynomial<F: Field> {
    /// The coefficient of `f(k)/(\prod_{k=1,i\neq k}^{m}(k-i))` is stored at location `k` in `self.coeffs`.
    pub interpolated_coeffs: Vec<F>,
    /// `X-1,X-2,\cdots,X-m`, interpolate at `1,2,\cdots,m` seperately.
    pub interpolated_polys: Vec<DensePolynomial<F>>,
}

impl<F: Field + std::cmp::PartialEq> LagrangePolynomial<F> {
    fn new(coeffs: &[(F, F)]) -> Self {
        let n = coeffs.len();
        let mut interpolated_coeffs: Vec<F> = Vec::new();
        let mut interpolated_polys: Vec<DensePolynomial<F>> = Vec::new();
        for i in 0..n {
            let mut y = coeffs[i].1;
            let cof_0 = -coeffs[i].0;
            let term = DensePolynomial::from_coefficients_vec(vec![cof_0, F::one()]);
            interpolated_polys.push(term);
            for j in 0..n {
                if i != j {
                    assert!(coeffs[i].0 != coeffs[j].0);
                    let denominator = coeffs[i].0 - coeffs[j].0;
                    y = y * denominator.inverse().unwrap();                    
                }
            }

            interpolated_coeffs.push(y);
        }
        LagrangePolynomial {
            interpolated_coeffs,
            interpolated_polys,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::polynomial::lagrange::LagrangePolynomial;
    use rand_core::{CryptoRng, RngCore};
    use crate::scalar::{Scalar, ScalarFromPrimitives};
    use std::cmp::max;
    use num_traits::Zero;
    use rand::rngs::OsRng;
    
     #[test]
    fn lagrangePolynomial_random() {
        let mut csprng: OsRng = OsRng;
        let n = 2;

        let mut x: Vec<(Scalar, Scalar)> = Vec::new();
        for _ in 0..n {
            x.push((Scalar::random(&mut csprng), Scalar::random(&mut csprng)));
        }
        
        let P = LagrangePolynomial::new(&x);
    }
}