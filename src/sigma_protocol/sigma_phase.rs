use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::scalar_math;

pub fn commit_phase(
  gens_1: &MultiCommitGens,
  gens_n: &MultiCommitGens,
  transcript: &mut Transcript,
  random_tape: &mut RandomTape,
  a_vec: &[Scalar],
) -> (Vec<Scalar>, Scalar, CompressedGroup, Scalar) {
  let n = a_vec.len();
  assert_eq!(gens_n.n, a_vec.len());
  assert_eq!(gens_1.n, 1);

  // produce randomness for the proofs
  let r_vec = random_tape.random_vector(b"r_vec", n);
  let rho = random_tape.random_scalar(b"rho");
  let A = r_vec.commit(&rho, gens_n).compress();
  A.append_to_transcript(b"A", transcript);

  let t = scalar_math::compute_linearform(&a_vec, &r_vec);
  t.append_to_transcript(b"t", transcript);


  (
    r_vec,
    rho,
    A,
    t,
  )
}

pub fn challenge_phase(
  transcript: &mut Transcript
) -> Scalar {
  let c = transcript.challenge_scalar(b"c");
  c
}



pub fn response_phase(
  challenge: &Scalar,
  blind_x: &Scalar,
  blind_r: &Scalar,
  x_vec: &[Scalar],
  r_vec: &[Scalar],
) -> (Vec<Scalar>, Scalar) {
  assert_eq!(x_vec.len(), r_vec.len());  
  let z = (0..r_vec.len())
      .map(|i| challenge * x_vec[i] + r_vec[i])
      .collect::<Vec<Scalar>>();

  let phi = challenge * blind_x + blind_r;

  (
    z,
    phi
  )
}


pub fn batch_response_phase(
  challenge_vec: &[Scalar],
  blind_x_vec: &[Scalar],
  blind_r: &Scalar,
  x_matrix: &Vec<Vec<Scalar>>,
  r_vec: &[Scalar],
) -> (Vec<Scalar>, Scalar) {
  assert_eq!(x_matrix.len(), blind_x_vec.len());
  assert_eq!(x_matrix.len(), challenge_vec.len());

  let s = x_matrix.len();
  let x_matrix_t = scalar_math::matrix_transpose(&x_matrix);
  let z_vec = scalar_math::matrix_vector_mul(&x_matrix_t, &challenge_vec);
  let z = scalar_math::row_row_add(&z_vec, &r_vec);

  let phi: Scalar = challenge_vec.iter()
                            .zip(blind_x_vec.iter())
                            .map(|(challenge, blind_x)|  challenge * blind_x)
                            .sum::<Scalar>() + blind_r;

  (
    z,
    phi
  )
}
