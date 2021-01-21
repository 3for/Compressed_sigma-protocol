use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, GROUP_BASEPOINT};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::*;
use crate::math::Math;
use crate::nizk::bullet::BulletReductionProof;
use crate::sigma_protocol::zk_basic_protocol_2::Pi_0_Proof;
use crate::sigma_protocol::nozk_protocol_3::Pi_1_Proof;
use crate::sigma_protocol::nozk_protocol_4::Pi_2_Proof;

// Protocol 4 in the paper: Compressed Proof of Knowledge $\Pi_2$ for $R_2$
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_c_Proof {
  proof_0: Pi_0_Proof,
  proof_1: Pi_1_Proof,
  proof_2: Pi_2_Proof,
}

impl Pi_c_Proof {
  fn protocol_name() -> &'static [u8] {
    b"zk compressed pi_c proof"
  }

  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    blind_x: &Scalar,
    l_vec: &[Scalar],
    y: &Scalar,
  ) -> (Pi_c_Proof, CompressedGroup, Scalar, CompressedGroup, Scalar) {
    transcript.append_protocol_name(Pi_c_Proof::protocol_name());

    let n = x_vec.len();
    assert_eq!(l_vec.len(), x_vec.len());
    assert_eq!(gens.gens_n.n, n);

    let (proof_0, P, y, z_vec, phi) = Pi_0_Proof::mod_prove(
      &gens.gens_1,
      &gens.gens_n,
      transcript,
      random_tape,
      &x_vec,
      &blind_x,
      &l_vec,
    );

    let (proof_1, P_hat, y_hat, L_tilde, z_hat, G_hat_vec) = Pi_1_Proof::mod_prove(
      &gens.gens_n,
      transcript,
      random_tape,
      &z_vec,
      &phi,
      &l_vec,
      &proof_0,
    );

    let gens_hat = MultiCommitGens {
      n: n+1,
      G: G_hat_vec,
      h: GROUP_BASEPOINT,
    }; 

    let (proof_2, Q) = Pi_2_Proof::mod_prove(
      &gens_hat,
      &gens.gens_1,
      transcript,
      random_tape,
      &L_tilde,
      &y_hat,
      &z_hat
    );


    (
      Pi_c_Proof {
        proof_0,
        proof_1,
        proof_2,
      },
      P,
      y,
      P_hat, 
      y_hat,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    l_vec: &[Scalar],
    P: &CompressedGroup,
    y: &Scalar,
    P_hat: &CompressedGroup,
    y_hat: &Scalar,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);
    assert_eq!(l_vec.len(), n);

    transcript.append_protocol_name(Pi_c_Proof::protocol_name());
    let mut result = 
    match self.proof_0.mod_verify(
      &gens.gens_1,
      &gens.gens_n,
      transcript,
      &l_vec,
      &P,
      &y,) {
        Ok(()) => true ,
        Err(r) => return Err(r),
      };

    result = 
    match self.proof_1.mod_verify(
      &gens.gens_1,
      &gens.gens_n,
      transcript,
      random_tape,
      &z_vec,
      &phi,
      &l_vec,
      &proof_0,
    ) {
        Ok(()) => true ,
        Err(r) => return Err(r),
      };

    Ok(())
  }

}


#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_pi_c_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1023;

    let gens = DotProductProofGens::new(n, b"test-1023");

    let l: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let z: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let y = DotProductProof::compute_dotproduct(&l, &z);
    
    let r_z = Scalar::random(&mut csprng);
    let Cz = z.commit(&r_z, &gens.gens_n).compress();

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P, y,
      P_hat, 
      y_hat,) = Pi_c_Proof::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &z,
      &r_z,
      &l,
      &y,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &l, &P, &y, &P_hat, &y_hat)
      .is_ok());
  }
}
