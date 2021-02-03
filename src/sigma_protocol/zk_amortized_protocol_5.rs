use super::super::transcript::{ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, GROUP_BASEPOINT, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::{DotProductProofGens};
use crate::sigma_protocol::zk_amortized_protocol_2::Pi_0_Am_Proof;
use crate::sigma_protocol::nozk_protocol_3::Pi_1_Proof;
use crate::sigma_protocol::nozk_protocol_4::Pi_2_Proof;
use super::scalar_math;

// Section 4.3 in https://blog.csdn.net/mutourend/article/details/108654372
// amortized basic sigma protocol $\Pi_c^{Am}$-protocol
// same linear form
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_c_Am_Proof {
  proof_0: Pi_0_Am_Proof,
  proof_1: Pi_1_Proof,
  proof_2: Pi_2_Proof,
}

impl Pi_c_Am_Proof {
  fn protocol_name() -> &'static [u8] {
    b"zk amortized compressed pi_c proof"
  }

  pub fn amortized_prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_matrix: &Vec<Vec<Scalar>>,
    gamma_vec: &[Scalar],
    l_vec: &[Scalar],
    y_vec: &[Scalar],
  ) -> (Pi_c_Am_Proof, Vec<CompressedGroup>, CompressedGroup) {
    transcript.append_protocol_name(Pi_c_Am_Proof::protocol_name());

    let n = l_vec.len();
    let s = x_matrix.len();
    assert_eq!(gamma_vec.len(), s);
    assert_eq!(gens.gens_n.n, n);

    let (proof_0, P_vec, z_vec, phi) = Pi_0_Am_Proof::mod_amortized_prove(
      &gens.gens_n,
      transcript,
      random_tape,
      &x_matrix,
      &gamma_vec,
      &l_vec,
      &y_vec,
    );

    let (proof_1, P_hat, _y_hat, L_tilde, z_hat, G_hat_vec) = Pi_1_Proof::mod_prove(
      &gens.gens_n,
      transcript,
      &z_vec,
      &phi,
      &l_vec,
    );

    let gens_hat = MultiCommitGens {
      n: n+1,
      G: G_hat_vec,
      h: GROUP_BASEPOINT,
    }; 

    let (proof_2, _Q) = Pi_2_Proof::mod_prove(
      &gens_hat,
      &gens.gens_1,
      transcript,
      &L_tilde,
      &z_hat
    );


    (
      Pi_c_Am_Proof {
        proof_0,
        proof_1,
        proof_2,
      },
      P_vec,
      P_hat, 
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

    transcript.append_protocol_name(Pi_c_Am_Proof::protocol_name());
    let c_0 = 
    self.proof_0.mod_amortized_verify(
      &gens.gens_n,
      transcript,
      &l_vec,
      &P_vec,
      &y_vec,);

    let s = y_vec.len();
    let c_0_vec = scalar_math::vandemonde_challenge(c_0, s);
    let y_hat = scalar_math::compute_linearform(
        &c_0_vec,
        y_vec,
      ) + self.proof_0.t;
    let mut P_depressed_vec: Vec<GroupElement> = Vec::new();
    for i in 0..s {       
      match P_vec[i].unpack() {
        Ok(P) => P_depressed_vec.push(P),
        Err(r) => return Err(r),
      }
    }

    let c_1 = 
    self.proof_1.mod_verify(
      transcript,
      &P_hat,
      &y_hat,
    );

    let mut L_hat = l_vec.clone().to_vec();
    L_hat.push(Scalar::zero());
    
    let mut L_tilde: Vec<Scalar> = Vec::new();
    for i in 0..L_hat.len() {
      L_tilde.push(c_1 * L_hat[i]);
    }

    let Q = (GroupElement::vartime_multiscalar_mul(
        c_0_vec.clone(),
        P_depressed_vec,
      ) + (c_1 * y_hat) * gens.gens_1.G[0] + self.proof_0.A.unpack()?).compress();

    let mut G_hat_vec = gens.gens_n.G.clone();
    G_hat_vec.push(gens.gens_n.h);
    let gens_hat = MultiCommitGens {
      n: n+1,
      G: G_hat_vec,
      h: GROUP_BASEPOINT,
    };

    return self.proof_2.mod_verify(
      n+1,
      &gens_hat,
      &gens.gens_1,
      transcript,
      &L_tilde,
      &Q,
    );
  }

}


#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_pi_c_Am_proof() {
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

    let mut y_vec: Vec<Scalar> = Vec::new();
    for i in 0..s {
      let x_vec = &x_matrix[i];
      let y = scalar_math::compute_linearform(&l_vec, &x_vec);
      y_vec.push(y);
    }

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P_vec, P_hat, ) = Pi_c_Am_Proof::amortized_prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x_matrix,
      &gamma_vec,
      &l_vec,
      &y_vec,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .amortized_verify(n, &gens, &mut verifier_transcript, &l_vec, &P_vec, &y_vec, &P_hat)
      .is_ok());
  }
}
