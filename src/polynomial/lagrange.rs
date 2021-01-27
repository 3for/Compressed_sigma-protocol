
use crate::polynomial::Field;
use crate::polynomial::univariate::DensePolynomial;

struct LagrangePolynomial<F: Field> {
    /// The coefficient of `f(k)/(\prod_{k=1,i\neq k}^{m}(k-i))` is stored at location `k` in `self.coeffs`.
    pub interpolated_coeffs: Vec<F>,
    /// `X-1,X-2,\cdots,X-m`, interpolate at `1,2,\cdots,m` seperately.
    pub interpolated_polys: Vec<DensePolynomial<F>>,
}

/*impl<F: Field> for DensePolynomial<F> {
    fn new(coeffs: &[(usize, F)]) -> Self {
        let n = coeffs.len();
        for i in 0..n {
            let mut term = coeffs[i].1;
            for j in 0..n {
                if i != j {
                    assert!(coeffs[i].0 != coeffs[j].0);
                    let denominator = coeffs[i].0 - coeffs[j].0;
                    let numerator = DensePolynomial
                }
            }
        }
    }
}*/