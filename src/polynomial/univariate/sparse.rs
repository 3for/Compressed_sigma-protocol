use crate::polynomial::Field;
use std::fmt;
use num_traits::{Zero};
use std::ops::{Add, AddAssign, Neg, SubAssign};
use std::collections::BTreeMap;
use crate::polynomial::{Polynomial, UVPolynomial};
use crate::polynomial::univariate::{DenseOrSparsePolynomial, DensePolynomial};

/// Stores a sparse polynomial in coefficient form.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct SparsePolynomial<F: Field>{
    /// The coefficient a_i of `x^i` is stored as (i, a_i) in `self.coeffs`.
    /// the entries in `self.coeffs` *must*  be sorted in increasing order of
    /// `i`.
    coeffs: Vec<(usize, F)>,
}


impl<F: Field> fmt::Debug for SparsePolynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for (i, coeff) in self.coeffs.iter().filter(|(_, c)| !c.is_zero()) {
            if *i == 0 {
                write!(f, "\n{:?}", coeff)?;
            } else if *i == 1 {
                write!(f, " + \n{:?} * x", coeff)?;
            } else {
                write!(f, " + \n{:?} * x^{}", coeff, i)?;
            }
        }
        Ok(())
    }
}

impl<F: Field> core::ops::Deref for SparsePolynomial<F> {
    type Target = [(usize, F)];

    fn deref(&self) -> &[(usize, F)] {
        &self.coeffs
    }
}

impl<F: Field> Polynomial<F> for SparsePolynomial<F> {
    type Point = F;

    /// Returns the degree of the polynomial.
    fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            assert!(self.coeffs.last().map_or(false, |(_, c)| !c.is_zero()));
            self.coeffs.last().unwrap().0
        }
    }

    /// Evaluates `self` at the given `point` in the field.
    fn evaluate(&self, point: &F) -> F {
        if self.is_zero() {
            return F::zero();
        }
        // compute all coeff * point^{i} and then sum the results
        let total = self
            .coeffs
            .iter()
            .map(|(i, c)| (*c * point.power(&[*i as u64])))
            .sum();
        total
    }
}


impl<F: Field> Add for SparsePolynomial<F> {
    type Output = SparsePolynomial<F>;

    fn add(self, other: SparsePolynomial<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Add<&'a SparsePolynomial<F>> for &'b SparsePolynomial<F> {
    type Output = SparsePolynomial<F>;

    fn add(self, other: &'a SparsePolynomial<F>) -> SparsePolynomial<F> {
        if self.is_zero() {
            return other.clone();
        } else if other.is_zero() {
            return self.clone();
        }
        // Single pass add algorithm (merging two sorted sets)
        let mut result = SparsePolynomial::<F>::zero();
        // our current index in each vector
        let mut self_index = 0;
        let mut other_index = 0;
        loop {
            // if we've reached the end of one vector, just append the other vector to our result.
            if self_index == self.coeffs.len() && other_index == other.coeffs.len() {
                return result;
            } else if self_index == self.coeffs.len() {
                result.append_coeffs(&other.coeffs[other_index..]);
                return result;
            } else if other_index == other.coeffs.len() {
                result.append_coeffs(&self.coeffs[self_index..]);
                return result;
            }

            // Get the current degree / coeff for each
            let (self_term_degree, self_term_coeff) = self.coeffs[self_index];
            let (other_term_degree, other_term_coeff) = other.coeffs[other_index];
            // add the lower degree term to our sorted set.
            if self_term_degree < other_term_degree {
                result.coeffs.push((self_term_degree, self_term_coeff));
                self_index += 1;
            } else if self_term_degree == other_term_degree {
                let term_sum = self_term_coeff + other_term_coeff;
                if !term_sum.is_zero() {
                    result
                        .coeffs
                        .push((self_term_degree, self_term_coeff + other_term_coeff));
                }
                self_index += 1;
                other_index += 1;
            } else {
                result.coeffs.push((other_term_degree, other_term_coeff));
                other_index += 1;
            }
        }
    }
}

impl<'a, 'b, F: Field> AddAssign<&'a SparsePolynomial<F>> for SparsePolynomial<F> {
    // TODO: Reduce number of clones
    fn add_assign(&mut self, other: &'a SparsePolynomial<F>) {
        self.coeffs = (self.clone() + other.clone()).coeffs;
    }
}

impl<'a, 'b, F: Field> AddAssign<(F, &'a SparsePolynomial<F>)> for SparsePolynomial<F> {
    // TODO: Reduce number of clones
    fn add_assign(&mut self, (f, other): (F, &'a SparsePolynomial<F>)) {
        self.coeffs = (self.clone() + other.clone()).coeffs;
        for i in 0..self.coeffs.len() {
            self.coeffs[i].1 *= f;
        }
    }
}

impl<F: Field> Neg for SparsePolynomial<F> {
    type Output = SparsePolynomial<F>;

    #[inline]
    fn neg(mut self) -> SparsePolynomial<F> {
        for (_, coeff) in &mut self.coeffs {
            *coeff = -*coeff;
        }
        self
    }
}

impl<'a, 'b, F: Field> SubAssign<&'a SparsePolynomial<F>> for SparsePolynomial<F> {
    // TODO: Reduce number of clones
    #[inline]
    fn sub_assign(&mut self, other: &'a SparsePolynomial<F>) {
        let self_copy = -self.clone();
        self.coeffs = (self_copy + other.clone()).coeffs;
    }
}

impl<F: Field> Zero for SparsePolynomial<F> {
    /// Returns the zero polynomial.
    fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Checks if the given polynomial is zero.
    fn is_zero(&self) -> bool {
        self.coeffs.is_empty() || self.coeffs.iter().all(|(_, c)| c.is_zero())
    }
}

impl<F: Field> SparsePolynomial<F> {
    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_slice(coeffs: &[(usize, F)]) -> Self {
        Self::from_coefficients_vec(coeffs.to_vec())
    }

    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_vec(mut coeffs: Vec<(usize, F)>) -> Self {
        // While there are zeros at the end of the coefficient vector, pop them off.
        while coeffs.last().map_or(false, |(_, c)| c.is_zero()) {
            coeffs.pop();
        }
        // Ensure that coeffs are in ascending order.
        coeffs.sort_by(|(c1, _), (c2, _)| c1.cmp(c2));
        // Check that either the coefficients vec is empty or that the last coeff is
        // non-zero.
        assert!(coeffs.last().map_or(true, |(_, c)| !c.is_zero()));

        Self { coeffs }
    }

    /// Perform a naive n^2 multiplication of `self` by `other`.
    #[allow(clippy::or_fun_call)]
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            SparsePolynomial::zero()
        } else {
            let mut result = BTreeMap::new();
            for (i, self_coeff) in self.coeffs.iter() {
                for (j, other_coeff) in other.coeffs.iter() {
                    let cur_coeff = result.entry(i + j).or_insert(F::zero());
                    *cur_coeff += &(*self_coeff * other_coeff);
                }
            }
            let result = result.into_iter().collect::<Vec<_>>();
            SparsePolynomial::from_coefficients_vec(result)
        }
    }

    // append append_coeffs to self.
    // Correctness relies on the lowest degree term in append_coeffs
    // being higher than self.degree()
    fn append_coeffs(&mut self, append_coeffs: &[(usize, F)]) {
        assert!(append_coeffs.len() == 0 || self.degree() < append_coeffs[0].0);
        for (i, elem) in append_coeffs.iter() {
            self.coeffs.push((*i, *elem));
        }
    }
}

impl<F: Field> Into<DensePolynomial<F>> for SparsePolynomial<F> {
    fn into(self) -> DensePolynomial<F> {
        let mut other = vec![F::zero(); self.degree() + 1];
        for (i, coeff) in self.coeffs {
            other[i] = coeff;
        }
        DensePolynomial::from_coefficients_vec(other)
    }
}

impl<F: Field> From<DensePolynomial<F>> for SparsePolynomial<F> {
    fn from(dense_poly: DensePolynomial<F>) -> SparsePolynomial<F> {
        let coeffs = dense_poly.coeffs();
        let mut sparse_coeffs = Vec::<(usize, F)>::new();
        for i in 0..coeffs.len() {
            if !coeffs[i].is_zero() {
                sparse_coeffs.push((i, coeffs[i]));
            }
        }
        SparsePolynomial::from_coefficients_vec(sparse_coeffs)
    }
}

#[cfg(test)]
mod tests {
    use crate::polynomial::Polynomial;
    use crate::polynomial::univariate::{SparsePolynomial, DensePolynomial};
    use rand_core::{CryptoRng, RngCore};
    use crate::scalar::{Scalar, ScalarFromPrimitives};
    use std::cmp::max;
    use num_traits::Zero;

    fn rand_sparse_poly<R: RngCore + CryptoRng>(degree: usize, rng: &mut R) -> SparsePolynomial<Scalar> {
        // Initialize coeffs so that its guaranteed to have a x^{degree} term
        let mut coeffs = vec![(degree, Scalar::random(rng))];
        for i in 0..degree {
            coeffs.push((i, Scalar::random(rng)));
        }
        SparsePolynomial::from_coefficients_vec(coeffs)
    }

    #[test]
    fn add_polynomial() {
        // Test adding polynomials by comparing against dense polynomial
        let mut rng = rand::thread_rng();
        for degree_a in 0..20 {
            let sparse_poly_a = rand_sparse_poly(degree_a, &mut rng);
            let dense_poly_a: DensePolynomial<Scalar> = sparse_poly_a.clone().into();
            for degree_b in 0..20 {
                let sparse_poly_b = rand_sparse_poly(degree_b, &mut rng);
                let dense_poly_b: DensePolynomial<Scalar> = sparse_poly_b.clone().into();

                // Test Add trait
                let sparse_sum = sparse_poly_a.clone() + sparse_poly_b.clone();
                assert_eq!(
                    sparse_sum.degree(),
                    max(degree_a, degree_b),
                    "degree_a = {}, degree_b = {}",
                    degree_a,
                    degree_b
                );

                let actual_dense_sum: DensePolynomial<Scalar> = sparse_sum.into();
                let expected_dense_sum = dense_poly_a.clone() + dense_poly_b;
                assert_eq!(
                    actual_dense_sum, expected_dense_sum,
                    "degree_a = {}, degree_b = {}",
                    degree_a, degree_b
                );
                // Test AddAssign Trait
                let mut sparse_add_assign_sum = sparse_poly_a.clone();
                sparse_add_assign_sum += &sparse_poly_b;
                let actual_add_assign_dense_sum: DensePolynomial<Scalar> = sparse_add_assign_sum.into();
                assert_eq!(
                    actual_add_assign_dense_sum, expected_dense_sum,
                    "degree_a = {}, degree_b = {}",
                    degree_a, degree_b
                );
            }
        }
    }

    #[test]
    fn evaluate_at_point_a() {
        let degree = 4;
        let mut coeffs = vec![(degree, Scalar::one())];
        for i in 0..degree {
            coeffs.push((i, Scalar::one()));
        }
        let sparse_poly = SparsePolynomial::from_coefficients_vec(coeffs);

        let pt = Scalar::one() + Scalar::one();

        assert_eq!(sparse_poly.evaluate(&pt), (31 as usize).to_scalar());
    }

    #[test]
    fn evaluate_at_point() {
        let mut rng = rand::thread_rng();
        // Test evaluation at point by comparing against DensePolynomial
        for degree in 0..60 {
            let sparse_poly = rand_sparse_poly(degree, &mut rng);
            let dense_poly: DensePolynomial<Scalar> = sparse_poly.clone().into();
            let pt = Scalar::random(&mut rng);
            assert_eq!(sparse_poly.evaluate(&pt), dense_poly.evaluate(&pt));
        }
    }

    #[test]
    fn polynomial_additive_identity() {
        // Test adding polynomials with its negative equals 0
        let mut rng = rand::thread_rng();
        for degree in 0..70 {
            // Test with Neg trait
            let sparse_poly = rand_sparse_poly(degree, &mut rng);
            let neg = -sparse_poly.clone();
            assert!((sparse_poly + neg).is_zero());

            // Test with SubAssign trait
            let sparse_poly = rand_sparse_poly(degree, &mut rng);
            let mut result = sparse_poly.clone();
            result -= &sparse_poly;
            assert!(result.is_zero());
        }
    }

    #[test]
    fn mul_polynomial() {
        // Test multiplying polynomials over their domains, and over the native representation.
        // The expected result is obtained by comparing against dense polynomial
        let mut rng = rand::thread_rng();
        for degree_a in 0..20 {
            let sparse_poly_a = rand_sparse_poly(degree_a, &mut rng);
            let dense_poly_a: DensePolynomial<Scalar> = sparse_poly_a.clone().into();
            for degree_b in 0..20 {
                let sparse_poly_b = rand_sparse_poly(degree_b, &mut rng);
                let dense_poly_b: DensePolynomial<Scalar> = sparse_poly_b.clone().into();

                // Test multiplying the polynomials over their native representation
                let sparse_prod = sparse_poly_a.mul(&sparse_poly_b);
                assert_eq!(
                    sparse_prod.degree(),
                    degree_a + degree_b,
                    "degree_a = {}, degree_b = {}",
                    degree_a,
                    degree_b
                );

                let dense_prod = dense_poly_a.naive_mul(&dense_poly_b);
                assert_eq!(sparse_prod.degree(), dense_prod.degree());
                assert_eq!(
                    sparse_prod,
                    SparsePolynomial::<Scalar>::from(dense_prod),
                    "degree_a = {}, degree_b = {}",
                    degree_a,
                    degree_b
                );

                // Test multiplying the polynomials over their evaluations and interpolating
                let pt = Scalar::random(&mut rng);
                let poly_a_evals = sparse_poly_a.evaluate(&pt);
                let poly_b_evals = sparse_poly_b.evaluate(&pt);
                let poly_prod_evals = sparse_prod.evaluate(&pt);
                assert_eq!(poly_a_evals.mul(&poly_b_evals), poly_prod_evals);
            }
        }
    }

}