use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};


// compute linear form $y=L(\vec{x})$
pub fn compute_linearform(a: &[Scalar], b: &[Scalar]) -> Scalar {
  assert_eq!(a.len(), b.len());
  (0..a.len()).map(|i| a[i] * b[i]).sum()
}


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

  let t = compute_linearform(&a_vec, &r_vec);
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

