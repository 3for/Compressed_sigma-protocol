
use super::super::scalar::Scalar;

// compute linear form $y=L(\vec{x})$
pub fn compute_linearform(a: &[Scalar], b: &[Scalar]) -> Scalar {
  assert_eq!(a.len(), b.len());
  (0..a.len()).map(|i| a[i] * b[i]).sum()
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
  let mut out = Scalar::zero();
  if a.len() != b.len() {
    panic!("inner_product(a,b): lengths of vectors do not match");
  }
  for i in 0..a.len() {
    out += a[i] * b[i];
  }
  out
}

// Creates a vector from the scalar `x`
// contents of vector = <x, x^2, x^3, ..., x^s>
pub fn vandemonde_challenge(x: Scalar, s: usize) -> Vec<Scalar> {
  let mut challenges: Vec<Scalar> = Vec::with_capacity(s);
  challenges.push(x);
  for i in 0..s-1 {
    challenges.push(challenges[i] * x);
  }
  challenges
}

// Creates a vector from the scalar `x`
// contents of vector = <1, x, x^2, x^3, ..., x^{s-1}>
pub fn vandemonde_challenge_one(x: Scalar, s: usize) -> Vec<Scalar> {
  let mut challenges: Vec<Scalar> = Vec::with_capacity(s);
  challenges.push(Scalar::one());
  for i in 0..s-1 {
    challenges.push(challenges[i] * x);
  }
  challenges
}

// Takes a matrix and a vector
// Returns a new vector i.e. (Ax=b)
pub fn matrix_vector_mul(matrix: &Vec<Vec<Scalar>>, vec: &[Scalar]) -> Vec<Scalar> {
    matrix.iter().map(|row| compute_linearform(row, &vec)).collect()
}

// Takes two rows and adds them together
// The (i) entry of row a is added to the i entry of row b
pub fn row_row_add(row_a: &[Scalar], row_b: &[Scalar]) -> Vec<Scalar> {
    assert_eq!(row_a.len(), row_b.len());

    row_a.iter().zip(row_b.iter()).map(|(a, b)| a + b).collect()
}

// Takes the transpose of a matrix
pub fn matrix_transpose(matrix: &Vec<Vec<Scalar>>) -> Vec<Vec<Scalar>> {
    let mut transpose: Vec<Vec<Scalar>> = vec![Vec::new(); matrix[0].len()];

    for (_, row) in matrix.iter().enumerate() {
        for (i, element) in row.iter().enumerate() {
            transpose[i].push(element.clone());
        }
    }

    transpose
}

// Takes a scalar and a vector
// Returns a new vector i.e. (a\vec{x}=[a*x_1,...,a*x_n])
pub fn scalar_vector_mul(a: &Scalar, vec: &[Scalar]) -> Vec<Scalar> {
    vec.iter().map(|v| a * v).collect()
}


pub fn zeros(size: usize) -> Vec<Scalar> {
  let mut zero_vec: Vec<Scalar> = Vec::with_capacity(size as usize);
  for _ in 0..size {
    zero_vec.push(Scalar::zero());
  }
  return zero_vec;
}

pub fn negOnes(size: usize) -> Vec<Scalar> {
  let mut zero_vec: Vec<Scalar> = Vec::with_capacity(size as usize);
  let negOne = -Scalar::one();
  for _ in 0..size {
    zero_vec.push(negOne);
  }
  return zero_vec;
}