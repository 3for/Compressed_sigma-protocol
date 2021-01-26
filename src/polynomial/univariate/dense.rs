use crate::polynomial::Field;
use std::fmt;
use num_traits::{Zero};
use std::ops::{Add, AddAssign, Neg, SubAssign, Div, Sub, Deref, DerefMut,};
use crate::polynomial::{Polynomial, UVPolynomial};
use crate::polynomial::univariate::DenseOrSparsePolynomial;
use rand_core::{CryptoRng, RngCore};

#[cfg(feature = "parallel")]
use std::cmp::max;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Stores a polynomial in coefficient form.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct DensePolynomial<F: Field> {
    /// The coefficient of `x^i` is stored at location `i` in `self.coeffs`.
    pub coeffs: Vec<F>,
}


impl<F: Field> Polynomial<F> for DensePolynomial<F> {
    type Point = F;

    /// Returns the total degree of the polynomial
    fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            assert!(self.coeffs.last().map_or(false, |coeff| !coeff.is_zero()));
            self.coeffs.len() - 1
        }
    }

    /// Evaluates `self` at the given `point` in `Self::Point`.
    fn evaluate(&self, point: &F) -> F {
        if self.is_zero() {
            return F::zero();
        } else if point.is_zero() {
            return self.coeffs[0];
        }
        self.internal_evaluate(point)
    }
}

#[cfg(feature = "parallel")]
// Set some minimum number of field elements to be worked on per thread
// to avoid per-thread costs dominating parallel execution time.
const MIN_ELEMENTS_PER_THREAD: usize = 16;

impl<F: Field> DensePolynomial<F> {
    #[inline]
    // Horner's method for polynomial evaluation
    fn horner_evaluate(poly_coeffs: &[F], point: &F) -> F {
        let mut result = F::zero();
        let num_coeffs = poly_coeffs.len();
        for i in (0..num_coeffs).rev() {
            result *= point;
            result += poly_coeffs[i];
        }
        result
    }

    #[cfg(not(feature = "parallel"))]
    fn internal_evaluate(&self, point: &F) -> F {
        Self::horner_evaluate(&self.coeffs, point)
    }

    #[cfg(feature = "parallel")]
    fn internal_evaluate(&self, point: &F) -> F {
        // Horners method - parallel method
        // compute the number of threads we will be using.
        let num_cpus_available = rayon::current_num_threads();
        let num_coeffs = self.coeffs.len();
        let num_elem_per_thread = max(num_coeffs / num_cpus_available, MIN_ELEMENTS_PER_THREAD);

        // run Horners method on each thread as follows:
        // 1) Split up the coefficients across each thread evenly.
        // 2) Do polynomial evaluation via horner's method for the thread's coefficeints
        // 3) Scale the result point^{thread coefficient start index}
        // Then obtain the final polynomial evaluation by summing each threads result.
        let result = self
            .coeffs
            .par_chunks(num_elem_per_thread)
            .enumerate()
            .map(|(i, chunk)| {
                let mut thread_result = Self::horner_evaluate(&chunk, point);
                thread_result *= point.pow(&[(i * num_elem_per_thread) as u64]);
                thread_result
            })
            .sum();
        result
    }
}

impl<F: Field> UVPolynomial<F> for DensePolynomial<F> {
    /// Constructs a new polynomial from a list of coefficients.
    fn from_coefficients_slice(coeffs: &[F]) -> Self {
        Self::from_coefficients_vec(coeffs.to_vec())
    }

    /// Constructs a new polynomial from a list of coefficients.
    fn from_coefficients_vec(coeffs: Vec<F>) -> Self {
        let mut result = Self { coeffs };
        // While there are zeros at the end of the coefficient vector, pop them off.
        result.truncate_leading_zeros();
        // Check that either the coefficients vec is empty or that the last coeff is
        // non-zero.
        assert!(result.coeffs.last().map_or(true, |coeff| !coeff.is_zero()));
        result
    }

    /// Returns the coefficients of `self`
    fn coeffs(&self) -> &[F] {
        &self.coeffs
    }

    /// Outputs a univariate polynomial of degree `d` where
    /// each coefficient is sampled uniformly at random.
    fn rand<R: RngCore + CryptoRng>(d: usize, rng: &mut R) -> Self {
        let mut random_coeffs = Vec::new();
        for _ in 0..=d {
            random_coeffs.push(F::rand(rng));
        }
        Self::from_coefficients_vec(random_coeffs)
    }
}

impl<F: Field> DensePolynomial<F> {
    fn truncate_leading_zeros(&mut self) {
        while self.coeffs.last().map_or(false, |c| c.is_zero()) {
            self.coeffs.pop();
        }
    }

    /// Perform a naive n^2 multiplication of `self` by `other`.
    pub fn naive_mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            DensePolynomial::zero()
        } else {
            let mut result = vec![F::zero(); self.degree() + other.degree() + 1];
            for (i, self_coeff) in self.coeffs.iter().enumerate() {
                for (j, other_coeff) in other.coeffs.iter().enumerate() {
                    result[i + j] += &(*self_coeff * other_coeff);
                }
            }
            DensePolynomial::from_coefficients_vec(result)
        }
    }
}

impl<F: Field> fmt::Debug for DensePolynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for (i, coeff) in self.coeffs.iter().enumerate().filter(|(_, c)| !c.is_zero()) {
            if i == 0 {
                write!(f, "\n{:?}", coeff)?;
            } else if i == 1 {
                write!(f, " + \n{:?} * x", coeff)?;
            } else {
                write!(f, " + \n{:?} * x^{}", coeff, i)?;
            }
        }
        Ok(())
    }
}

impl<F: Field> Deref for DensePolynomial<F> {
    type Target = [F];

    fn deref(&self) -> &[F] {
        &self.coeffs
    }
}

impl<F: Field> DerefMut for DensePolynomial<F> {
    fn deref_mut(&mut self) -> &mut [F] {
        &mut self.coeffs
    }
}

impl<F: Field> Add for DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn add(self, other: DensePolynomial<F>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field> Add<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn add(self, other: &'a DensePolynomial<F>) -> DensePolynomial<F> {
        let mut result = if self.is_zero() {
            other.clone()
        } else if other.is_zero() {
            self.clone()
        } else if self.degree() >= other.degree() {
            let mut result = self.clone();
            result
                .coeffs
                .iter_mut()
                .zip(&other.coeffs)
                .for_each(|(a, b)| {
                    *a += b;
                });
            result
        } else {
            let mut result = other.clone();
            result
                .coeffs
                .iter_mut()
                .zip(&self.coeffs)
                .for_each(|(a, b)| {
                    *a += b;
                });
            result
        };
        result.truncate_leading_zeros();
        result
    }
}

impl<'a, 'b, F: Field> AddAssign<&'a DensePolynomial<F>> for DensePolynomial<F> {
    fn add_assign(&mut self, other: &'a DensePolynomial<F>) {
        if self.is_zero() {
            self.coeffs.truncate(0);
            self.coeffs.extend_from_slice(&other.coeffs);
        } else if other.is_zero() {
        } else if self.degree() >= other.degree() {
            self.coeffs
                .iter_mut()
                .zip(&other.coeffs)
                .for_each(|(a, b)| {
                    *a += b;
                });
        } else {
            // Add the necessary number of zero coefficients.
            self.coeffs.resize(other.coeffs.len(), F::zero());
            self.coeffs
                .iter_mut()
                .zip(&other.coeffs)
                .for_each(|(a, b)| {
                    *a += b;
                });
            self.truncate_leading_zeros();
        }
    }
}

impl<'a, 'b, F: Field> AddAssign<(F, &'a DensePolynomial<F>)> for DensePolynomial<F> {
    fn add_assign(&mut self, (f, other): (F, &'a DensePolynomial<F>)) {
        if self.is_zero() {
            self.coeffs.truncate(0);
            self.coeffs.extend_from_slice(&other.coeffs);
            self.coeffs.iter_mut().for_each(|c| *c *= &f);
            return;
        } else if other.is_zero() {
            return;
        } else if self.degree() >= other.degree() {
        } else {
            // Add the necessary number of zero coefficients.
            self.coeffs.resize(other.coeffs.len(), F::zero());
        }
        self.coeffs
            .iter_mut()
            .zip(&other.coeffs)
            .for_each(|(a, b)| {
                *a += &(f * b);
            });
        // If the leading coefficient ends up being zero, pop it off.
        // This can happen if they were the same degree, or if a
        // polynomial's coefficients were constructed with leading zeros.
        self.truncate_leading_zeros();
    }
}

impl<F: Field> Neg for DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    #[inline]
    fn neg(mut self) -> DensePolynomial<F> {
        self.coeffs.iter_mut().for_each(|coeff| {
            *coeff = -*coeff;
        });
        self
    }
}

impl<'a, 'b, F: Field> Sub<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    #[inline]
    fn sub(self, other: &'a DensePolynomial<F>) -> DensePolynomial<F> {
        let mut result = if self.is_zero() {
            let mut result = other.clone();
            result.coeffs.iter_mut().for_each(|c| *c = -(*c));
            result
        } else if other.is_zero() {
            self.clone()
        } else if self.degree() >= other.degree() {
            let mut result = self.clone();
            result
                .coeffs
                .iter_mut()
                .zip(&other.coeffs)
                .for_each(|(a, b)| *a -= b);
            result
        } else {
            let mut result = self.clone();
            result.coeffs.resize(other.coeffs.len(), F::zero());
            result
                .coeffs
                .iter_mut()
                .zip(&other.coeffs)
                .for_each(|(a, b)| *a -= b);
            result
        };
        result.truncate_leading_zeros();
        result
    }
}

impl<'a, 'b, F: Field> SubAssign<&'a DensePolynomial<F>> for DensePolynomial<F> {
    #[inline]
    fn sub_assign(&mut self, other: &'a DensePolynomial<F>) {
        if self.is_zero() {
            self.coeffs.resize(other.coeffs.len(), F::zero());
        } else if other.is_zero() {
            return;
        } else if self.degree() >= other.degree() {
        } else {
            // Add the necessary number of zero coefficients.
            self.coeffs.resize(other.coeffs.len(), F::zero());
        }
        self.coeffs
            .iter_mut()
            .zip(&other.coeffs)
            .for_each(|(a, b)| {
                *a -= b;
            });
        // If the leading coefficient ends up being zero, pop it off.
        // This can happen if they were the same degree, or if other's
        // coefficients were constructed with leading zeros.
        self.truncate_leading_zeros();
    }
}

impl<'a, 'b, F: Field> Div<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    #[inline]
    fn div(self, divisor: &'a DensePolynomial<F>) -> DensePolynomial<F> {
        let a = DenseOrSparsePolynomial::from(self);
        let b = DenseOrSparsePolynomial::from(divisor);
        a.divide_with_q_and_r(&b).expect("division failed").0
    }
}

impl<F: Field> Zero for DensePolynomial<F> {
    /// Returns the zero polynomial.
    fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Checks if the given polynomial is zero.
    fn is_zero(&self) -> bool {
        self.coeffs.is_empty() || self.coeffs.iter().all(|coeff| coeff.is_zero())
    }
}