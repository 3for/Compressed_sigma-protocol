
use crate::polynomial::Field;
use crate::polynomial::univariate::DensePolynomial;
use crate::polynomial::UVPolynomial;
use crate::polynomial::Polynomial;

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
            let mut denominator = F::one();
            for j in 0..n {
                if i != j {
                    assert!(coeffs[i].0 != coeffs[j].0);
                    denominator = denominator * (coeffs[i].0 - coeffs[j].0);
                }
            }
            y = y * denominator.inverse().unwrap();                    
            interpolated_coeffs.push(y);
        }
        LagrangePolynomial {
            interpolated_coeffs,
            interpolated_polys,
        }
    }

    /// Evaluates `self` at the given `point` in `Self::Point`.
    fn evaluate(&self, point: &F) -> F {
        if self.interpolated_coeffs.len() == 0 {
            return F::zero();
        }
        let n = self.interpolated_coeffs.len();
        let mut total = F::zero();
        let mut evals: Vec<F> = Vec::new();
        for i in 0..n {
            let eval = self.interpolated_polys[i].evaluate(point);
            evals.push(eval); 
        }
        for i in 0..n {
            let cof = self.interpolated_coeffs[i];
            let mut eval_mul = F::one();
            for j in 0..n {
                if i != j {
                    eval_mul = eval_mul * evals[j];
                }
            }
            total = total + cof * eval_mul;
        }
        total
    }
}

pub struct LagrangePolynomialDirect<F: Field> {
    /// The coefficient of `x^i` is stored at location `k` in `self.coeffs`.
    pub lg_poly: DensePolynomial<F>,
}

impl<F: Field + std::cmp::PartialEq> LagrangePolynomialDirect<F> {
    pub fn new(coeffs: &[(F, F)]) -> Self {
        let n = coeffs.len();
        let mut total_poly = DensePolynomial::from_coefficients_vec(vec![F::zero()]);
        for i in 0..n {
            let mut y = coeffs[i].1;
            let mut term = DensePolynomial::from_coefficients_vec(vec![F::one()]);
            let mut denominator = F::one();
            for j in 0..n {
                if i != j {
                    assert!(coeffs[i].0 != coeffs[j].0);
                    denominator = denominator * (coeffs[i].0 - coeffs[j].0);
                    term = term.naive_mul(&DensePolynomial::from_coefficients_vec(vec![-coeffs[j].0, F::one()]));
                }
            }
            y = y * denominator.inverse().unwrap();                    
            
            total_poly = &total_poly + &term.naive_mul(&DensePolynomial::from_coefficients_vec(vec![y]));
        }
        LagrangePolynomialDirect {
            lg_poly: total_poly,
        }
    }

    /// Evaluates `self` at the given `point` in `Self::Point`.
    pub fn evaluate(&self, point: &F) -> F {
        if self.lg_poly.coeffs.len() == 0 {
            return F::zero();
        } else if point.is_zero() {
            return self.lg_poly.coeffs[0];
        }
        self.lg_poly.evaluate(point)
    }
}

#[cfg(test)]
mod tests {
    use crate::polynomial::lagrange::*;
    use rand_core::{CryptoRng, RngCore};
    use crate::scalar::{Scalar, ScalarFromPrimitives};
    use std::cmp::max;
    use num_traits::Zero;
    use rand::rngs::OsRng;
    
    #[test]
    fn lagrangePolynomial_evaluate() {
        let mut csprng: OsRng = OsRng;
        let n = 100;

        let mut x: Vec<(Scalar, Scalar)> = Vec::new();
        for _ in 0..n {
            x.push((Scalar::random(&mut csprng), Scalar::random(&mut csprng)));
        }
        
        let P = LagrangePolynomial::new(&x);

        for i in 0..n {
            assert_eq!(P.evaluate(&(x[i].0)), x[i].1);
        }
    }

    #[test]
    fn lagrangePolynomial_direct_evaluate() {
        let mut csprng: OsRng = OsRng;
        let n = 100;

        let mut x: Vec<(Scalar, Scalar)> = Vec::new();
        for _ in 0..n {
            x.push((Scalar::random(&mut csprng), Scalar::random(&mut csprng)));
        }
        
        let P = LagrangePolynomialDirect::new(&x);

        for i in 0..n {
            assert_eq!(P.evaluate(&(x[i].0)), x[i].1);
        }
    }
}