use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};

//basic sigma protocol: $\Pi_0$-protocol
#[derive(Debug, Serialize, Deserialize)]
pub struct Basic_Pi_0_Proof {
  A: CompressedGroup,
  z: Vec<Scalar>,
  y_p: Scalar, // y'
  blind_z: Scalar,
}

impl Basic_Pi_0_Proof {
  fn protocol_name() -> &'static [u8] {
    b"basic pi_0 proof"
  }

  // compute linear form $y=L(\vec{x})$
  pub fn compute_linearform(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    (0..a.len()).map(|i| a[i] * b[i]).sum()
  }

  pub fn prove(
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    blind_x: &Scalar,
    a_vec: &[Scalar],
  ) -> (Basic_Pi_0_Proof, CompressedGroup, Scalar) {
    transcript.append_protocol_name(Basic_Pi_0_Proof::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens_n.n, a_vec.len());
    assert_eq!(gens_1.n, 1);

    // produce randomness for the proofs
    let r_vec = random_tape.random_vector(b"r_vec", n);
    let blind_r = random_tape.random_scalar(b"blind_r");
    //let r_beta = random_tape.random_scalar(b"r_beta");

    let Cx = x_vec.commit(&blind_x, gens_n).compress();
    Cx.append_to_transcript(b"Cx", transcript);

    let y = Basic_Pi_0_Proof::compute_linearform(&a_vec, &x_vec);
    y.append_to_transcript(b"y", transcript);

    let A = r_vec.commit(&blind_r, gens_n).compress();
    A.append_to_transcript(b"A", transcript);

    let y_p = Basic_Pi_0_Proof::compute_linearform(&a_vec, &r_vec);
    y_p.append_to_transcript(b"y_p", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z = (0..r_vec.len())
      .map(|i| c * x_vec[i] + r_vec[i])
      .collect::<Vec<Scalar>>();

    let blind_z = c * blind_x + blind_r;

    (
      Basic_Pi_0_Proof {
        A,
        z,
        y_p,
        blind_z,
      },
      Cx,
      y,
    )
  }

  pub fn verify(
    &self,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    Cx: &CompressedGroup,
    y: &Scalar,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n, a.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(Basic_Pi_0_Proof::protocol_name());
    Cx.append_to_transcript(b"Cx", transcript);
    y.append_to_transcript(b"y", transcript);
    self.A.append_to_transcript(b"A", transcript);
    self.y_p.append_to_transcript(b"y_p", transcript);

    let c = transcript.challenge_scalar(b"c");

    let mut result =
      c * Cx.unpack()? + self.A.unpack()? == self.z.commit(&self.blind_z, gens_n);

    let l_z = Basic_Pi_0_Proof::compute_linearform(&self.z, &a);
    result &= c * y + self.y_p == l_z;

    if result {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}


#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_basic_pi_0_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens_1 = MultiCommitGens::new(1, b"test-two");
    let gens_1024 = MultiCommitGens::new(n, b"test-1024");

    let mut x: Vec<Scalar> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      x.push(Scalar::random(&mut csprng));
      a.push(Scalar::random(&mut csprng));
    }

    let r_x = Scalar::random(&mut csprng);
    
    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cx, y) = Basic_Pi_0_Proof::prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
    );
    
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &Cx, &y)
      .is_ok());
  }

}
