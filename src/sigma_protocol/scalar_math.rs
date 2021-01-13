
use super::super::scalar::Scalar;

// compute linear form $y=L(\vec{x})$
pub fn compute_linearform(a: &[Scalar], b: &[Scalar]) -> Scalar {
  assert_eq!(a.len(), b.len());
  (0..a.len()).map(|i| a[i] * b[i]).sum()
}

// Creates a vector from the scalar `x`
// contents of vector = <x, x^2, x^3, ..., x^s>
pub fn vandemonde_challenge(mut x: Scalar, s: usize) -> Vec<Scalar> {
  let mut challenges: Vec<Scalar> = Vec::with_capacity(s);
  challenges.push(x);
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
