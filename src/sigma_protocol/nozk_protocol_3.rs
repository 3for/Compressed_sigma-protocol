use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::scalar_math;
use crate::sigma_protocol::zk_basic_protocol_2::Pi_0_Proof;

// Protocol 3 in the paper: Argument of Knowledge $\Pi_1$ for $R_1$
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_1_Proof {
}

impl Pi_1_Proof {
  fn protocol_name() -> &'static [u8] {
    b"nozk pi_1 proof"
  }

  // non zeroknowledge, finally expose z_hat=[z_vec,phi] to Verifier.
  pub fn mod_prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    z_vec: &[Scalar], //private info
    phi: &Scalar, //private info
    a_vec: &[Scalar], //public info.
    proof_0: &Pi_0_Proof,
  ) -> (Pi_1_Proof, CompressedGroup, Scalar, Vec<Scalar>, Vec<Scalar>, Vec<GroupElement>) {
    transcript.append_protocol_name(Pi_1_Proof::protocol_name());

    let P_hat = z_vec.commit(phi, gens_n).compress();
    P_hat.append_to_transcript(b"P_hat", transcript);

    let mut z_hat = z_vec.clone().to_vec();
    z_hat.push(*phi);

    let mut L_hat = a_vec.clone().to_vec();
    L_hat.push(Scalar::zero());

    let y_hat = scalar_math::compute_linearform(&L_hat, &z_hat);
    y_hat.append_to_transcript(b"y_hat", transcript);

    let c_1 = transcript.challenge_scalar(b"c_1");
    
    let mut L_tilde: Vec<Scalar> = Vec::new();
    for i in 0..L_hat.len() {
      L_tilde.push(c_1 * L_hat[i]);
    }

    let mut G_hat = gens_n.G.clone();
    G_hat.push(gens_n.h);
    
    (
      Pi_1_Proof {},
      P_hat,
      y_hat,
      L_tilde,
      z_hat,
      G_hat,
    )
  }

  pub fn mod_verify(
    &self,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    a_vec: &[Scalar],
    P_hat: &CompressedGroup,
    y_hat: &Scalar,
    L_tilde: &[Scalar],
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n, a_vec.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(Pi_1_Proof::protocol_name());
    P_hat.append_to_transcript(b"P_hat", transcript);
    y_hat.append_to_transcript(b"y_hat", transcript);

    let mut L_hat = a_vec.clone().to_vec();
    L_hat.push(Scalar::zero());
    
    let c_1 = transcript.challenge_scalar(b"c_1");
    for i in 0..L_hat.len(){
      if L_tilde[i] != c_1 * L_hat[i] {
        return Err(ProofVerifyError::InternalError)
      }
    }

    Ok(())
  }


}

// Protocol 3 in the paper: Argument of Knowledge $\Pi_1$ for $R_1$
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_1_Proof_Pure {
  pub z_hat: Vec<Scalar>,
}

impl Pi_1_Proof_Pure {
  fn protocol_name() -> &'static [u8] {
    b"nozk pi_1 proof pure"
  }

  // non zeroknowledge, finally expose z_hat=[z_vec,phi] to Verifier.
  pub fn nozk_prove(
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    z_vec: &[Scalar],
    phi: &Scalar,
    L_hat: &[Scalar],
  ) -> (Pi_1_Proof_Pure, CompressedGroup, Scalar) {
    transcript.append_protocol_name(Pi_1_Proof_Pure::protocol_name());

    let P_hat = z_vec.commit(&phi, gens_n).compress();
    P_hat.append_to_transcript(b"P_hat", transcript);

    
    let mut z_hat = z_vec.clone().to_vec();
    z_hat.push(*phi);

    let y_hat = scalar_math::compute_linearform(&L_hat, &z_hat);
    y_hat.append_to_transcript(b"y_hat", transcript);
    
    (
      Pi_1_Proof_Pure {
        z_hat: z_hat,
      },
      P_hat,
      y_hat,
    )
  }

  

  pub fn nozk_verify(
    &self,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    L_hat: &[Scalar],
    P_hat: &CompressedGroup,
    y_hat: &Scalar,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n+1, L_hat.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(Pi_1_Proof::protocol_name());
    P_hat.append_to_transcript(b"P_hat", transcript);
    y_hat.append_to_transcript(b"y_hat", transcript);
    
    let c_1 = transcript.challenge_scalar(b"c_1");
    let mut result = false;
    match P_hat.unpack() {
      Ok(P) => {
        result = P + (c_1 * y_hat) * gens_1.G[0] == self.z_hat[..self.z_hat.len()-1].commit(&self.z_hat[self.z_hat.len()-1], gens_n) + c_1 * scalar_math::compute_linearform(&L_hat, &self.z_hat) * gens_1.G[0];
        if result {
          return Ok(())
        } else {
          return Err(ProofVerifyError::InternalError)
        }
      },
      Err(r) => return Err(r),
    }

  }

}



#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_pi_1_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens_1 = MultiCommitGens::new(1, b"test-two"); //[k,k_h]
    let gens_1024 = MultiCommitGens::new(n, b"test-1024"); //[vec{g},h]

    let mut z: Vec<Scalar> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      z.push(Scalar::random(&mut csprng));
      a.push(Scalar::random(&mut csprng));
    }

    let r_z = Scalar::random(&mut csprng);
    
    let mut L_hat = a.clone().to_vec();
    L_hat.push(Scalar::zero());

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof_1, P_1, y_1) = Pi_1_Proof_Pure::nozk_prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &z,
      &r_z,
      &L_hat,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof_1
      .nozk_verify(&gens_1, &gens_1024, &mut verifier_transcript, &L_hat, &P_1, &y_1)
      .is_ok());
  }
}
