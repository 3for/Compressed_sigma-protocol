use super::super::transcript::{ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::{DotProductProofGens};
use crate::sigma_protocol::zk_amortized_protocol_5::Pi_c_Am_Proof;
use super::scalar_math;

// Section 5.2 in https://blog.csdn.net/mutourend/article/details/108654372
// Opening Affine maps
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_NULLITY_Am_Proof {
  proof: Pi_c_Am_Proof,
}
// different linear forms, different $\vec{x}$
impl Pi_NULLITY_Am_Proof {
  fn protocol_name() -> &'static [u8] {
    b"zk amortized pi_nullity proof"
  }

  pub fn amortized_prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_matrix: &Vec<Vec<Scalar>>,
    gamma_vec: &[Scalar],
    l_matrix: &Vec<Vec<Scalar>>,
  ) -> (Pi_NULLITY_Am_Proof, Vec<CompressedGroup>, CompressedGroup, Vec<Scalar>) {
    transcript.append_protocol_name(Pi_NULLITY_Am_Proof::protocol_name());

    let s = x_matrix.len();
    assert_eq!(gamma_vec.len(), s);

    let rho = transcript.challenge_scalar(b"rho");
    let rho_vec = scalar_math::vandemonde_challenge_one(rho, s);
    let l_matrix_t = scalar_math::matrix_transpose(&l_matrix);
    let l_vec = scalar_math::matrix_vector_mul(&l_matrix_t, &rho_vec);

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
      Pi_NULLITY_Am_Proof{
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
    l_matrix: &Vec<Vec<Scalar>>,
    P_vec: &[CompressedGroup],
    y_vec: &[Scalar],
    P_hat: &CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);

    transcript.append_protocol_name(Pi_NULLITY_Am_Proof::protocol_name());
    
    let s = l_matrix.len();
    let rho = transcript.challenge_scalar(b"rho");
    let rho_vec = scalar_math::vandemonde_challenge_one(rho, s);
    let l_matrix_t = scalar_math::matrix_transpose(&l_matrix);
    let l_vec = scalar_math::matrix_vector_mul(&l_matrix_t, &rho_vec);

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
  fn check_pi_nullity_Am_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1023;
    let s = 21;

    let gens = DotProductProofGens::new(n, b"test-1023");

    //
    let mut l_matrix: Vec<Vec<Scalar>> = Vec::new();
    let mut x_matrix: Vec<Vec<Scalar>> = Vec::new();
    let mut gamma_vec: Vec<Scalar> = Vec::new();

    for _ in 0..s {
      gamma_vec.push(Scalar::random(&mut csprng));

      let mut l_tmp: Vec<Scalar> = (0..n-1).map(|_| Scalar::random(&mut csprng)).collect();
      let mut x_tmp: Vec<Scalar> = (0..n-1).map(|_| Scalar::random(&mut csprng)).collect();

      //make $<L_i, \vec{x}>=0$
      let y = scalar_math::compute_linearform(&l_tmp, &x_tmp);
      l_tmp.push(y);      
      l_matrix.push(l_tmp.clone());
      x_tmp.push(-Scalar::one());
      x_matrix.push(x_tmp.clone());

      assert_eq!(scalar_math::compute_linearform(&l_tmp, &x_tmp), Scalar::zero());
    }
    //

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P_vec, P_hat, y_vec) = Pi_NULLITY_Am_Proof::amortized_prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x_matrix,
      &gamma_vec,
      &l_matrix,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .amortized_verify(n, &gens, &mut verifier_transcript, &l_matrix, &P_vec, &y_vec, &P_hat)
      .is_ok());
  }
}
