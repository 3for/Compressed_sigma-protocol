use super::super::transcript::{ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, GROUP_BASEPOINT, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::*;
use crate::sigma_protocol::zk_protocol_5::Pi_c_Proof;
use super::scalar_math;

// // Protocol 4 in the paper: Compressed Proof of Knowledge $\Pi_OPEN$ 
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_NULLITY_Proof {
  proof: Pi_c_Proof,
}
// different linear forms, same $\vec{x}$
impl Pi_NULLITY_Proof {
  fn protocol_name() -> &'static [u8] {
    b"nullity zk pi_nullity proof"
  }

  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    gamma: &Scalar,
    l_matrix: &Vec<Vec<Scalar>>,
  ) -> (Pi_NULLITY_Proof, CompressedGroup, CompressedGroup, Scalar) {
    transcript.append_protocol_name(Pi_NULLITY_Proof::protocol_name());

    let n = x_vec.len();
    let s = l_matrix.len();
    assert_eq!(gens.gens_n.n, n);

    let rho = transcript.challenge_scalar(b"rho");
    let rho_vec = scalar_math::vandemonde_challenge_one(rho, s);
    let l_matrix_t = scalar_math::matrix_transpose(&l_matrix);
    let l_vec = scalar_math::matrix_vector_mul(&l_matrix_t, &rho_vec);
    
    let y = scalar_math::compute_linearform(&l_vec, &x_vec);

    let (proof, P, P_hat) = Pi_c_Proof::prove(
      &gens,
      transcript,
      random_tape,
      x_vec,
      gamma,
      &l_vec,
      &y,
    );

    (
      Pi_NULLITY_Proof{
        proof,
      },
      P,
      P_hat, 
      y
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    l_matrix: &Vec<Vec<Scalar>>,
    P: &CompressedGroup,
    y: &Scalar,
    P_hat: &CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);

    transcript.append_protocol_name(Pi_NULLITY_Proof::protocol_name());
    
    let s = l_matrix.len();
    let rho = transcript.challenge_scalar(b"rho");
    let rho_vec = scalar_math::vandemonde_challenge_one(rho, s);
    let l_matrix_t = scalar_math::matrix_transpose(&l_matrix);
    let l_vec = scalar_math::matrix_vector_mul(&l_matrix_t, &rho_vec);

    return self.proof.verify(
      n,
      &gens,
      transcript,
      &l_vec,
      &P,
      &y,
      &P_hat,
    );
  }

}


#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_pi_nullity_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1023;
    let s = 21;

    let gens = DotProductProofGens::new(n, b"test-1023");

    let mut l_matrix: Vec<Vec<Scalar>> = Vec::new();
    let mut x_vec: Vec<Scalar> = Vec::new();
    for _ in 0..n-1 {
      x_vec.push(Scalar::random(&mut csprng));
    }

    let gamma = Scalar::random(&mut csprng);
    let tmp_x_vec = x_vec.clone();
    x_vec.push(-Scalar::one());
    for _ in 0..s {
      let mut tmp: Vec<Scalar> = (0..n-1).map(|_| Scalar::random(&mut csprng)).collect();

      //make $<L_i, \vec{x}>=0$
      let y = scalar_math::compute_linearform(&tmp, &tmp_x_vec);
      tmp.push(y);      
      l_matrix.push(tmp.clone());

      assert_eq!(scalar_math::compute_linearform(&tmp, &x_vec), Scalar::zero());
    }

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P_vec, P_hat, y) = Pi_NULLITY_Proof::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x_vec,
      &gamma,
      &l_matrix,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &l_matrix, &P_vec, &y, &P_hat)
      .is_ok());
  }
}
