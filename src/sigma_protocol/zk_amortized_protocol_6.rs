use super::super::transcript::{ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::*;
use crate::sigma_protocol::zk_amortized_protocol_5::Pi_c_Am_Proof;
use super::scalar_math;

// // Protocol 4 in the paper: Compressed Proof of Knowledge $\Pi_OPEN$ 
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_OPEN_Am_Proof {
  proof: Pi_c_Am_Proof,
}
// same linear form, different $\vec{x}$
impl Pi_OPEN_Am_Proof {
  fn protocol_name() -> &'static [u8] {
    b"open zk amortized compressed pi_c proof"
  }

  pub fn amortized_prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_matrix: &Vec<Vec<Scalar>>,
    gamma_vec: &[Scalar],
    l_vec: &[Scalar],
  ) -> (Pi_OPEN_Am_Proof, Vec<CompressedGroup>, CompressedGroup, Vec<Scalar>) {
    transcript.append_protocol_name(Pi_OPEN_Am_Proof::protocol_name());

    let n = l_vec.len();
    let s = x_matrix.len();
    assert_eq!(gamma_vec.len(), s);
    assert_eq!(gens.gens_n.n, n);

    let mut y_vec: Vec<Scalar> = Vec::new();
    for i in 0..s {
      let x_vec = &x_matrix[i];
      let y = scalar_math::compute_linearform(&l_vec, &x_vec);
      y_vec.push(y);
    }

    let (proof, P_vec, P_hat) = Pi_c_Am_Proof::amortized_prove(
      &gens,
      transcript,
      random_tape,
      &x_matrix,
      &gamma_vec,
      &l_vec,
      &y_vec,
    );

    (
      Pi_OPEN_Am_Proof{
        proof,
      },
      P_vec,
      P_hat, 
      y_vec
    )
  }

  pub fn amortized_verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    l_vec: &[Scalar],
    P_vec: &[CompressedGroup],
    y_vec: &[Scalar],
    P_hat: &CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);
    assert_eq!(l_vec.len(), n);

    transcript.append_protocol_name(Pi_OPEN_Am_Proof::protocol_name());
    

    return self.proof.amortized_verify(
      n,
      &gens,
      transcript,
      &l_vec,
      &P_vec,
      &y_vec,
      &P_hat,
    );
  }

}


#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_pi_open_Am_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1023;
    let s = 21;

    let gens = DotProductProofGens::new(n, b"test-1023");

    let mut x_matrix: Vec<Vec<Scalar>> = Vec::new();
    let mut l_vec: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      l_vec.push(Scalar::random(&mut csprng));
    }

    let mut gamma_vec: Vec<Scalar> = Vec::new();
    for _ in 0..s {
      gamma_vec.push(Scalar::random(&mut csprng));
      let tmp: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut csprng)).collect();
      x_matrix.push(tmp);
    }

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P_vec, P_hat, y_vec) = Pi_OPEN_Am_Proof::amortized_prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x_matrix,
      &gamma_vec,
      &l_vec,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .amortized_verify(n, &gens, &mut verifier_transcript, &l_vec, &P_vec, &y_vec, &P_hat)
      .is_ok());
  }
}
