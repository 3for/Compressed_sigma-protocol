use super::super::transcript::{ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GROUP_BASEPOINT};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{MultiCommitGens, Commitments};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::*;
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
    gamma: &Scalar,
    l_vec: &[Scalar],
    y: &Scalar,
  ) -> (Pi_c_Proof, CompressedGroup, CompressedGroup) {
    transcript.append_protocol_name(Pi_c_Proof::protocol_name());

    let n = x_vec.len();
    assert_eq!(l_vec.len(), x_vec.len());
    assert_eq!(gens.gens_n.n, n);

    let (proof_0, P, z_vec, phi) = Pi_0_Proof::mod_prove(
      &gens.gens_n,
      transcript,
      random_tape,
      &x_vec,
      &gamma,
      &l_vec,
      &y,
    );

    let (proof_1, P_hat, y_hat, L_tilde, z_hat, G_hat_vec) = Pi_1_Proof::mod_prove(
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

    let (proof_2, Q) = Pi_2_Proof::mod_prove(
      &gens_hat,
      &gens.gens_1,
      transcript,
      &L_tilde,
      &z_hat
    );


    (
      Pi_c_Proof {
        proof_0,
        proof_1,
        proof_2,
      },
      P,
      P_hat, 
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
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);
    assert_eq!(l_vec.len(), n);

    transcript.append_protocol_name(Pi_c_Proof::protocol_name());
    let c_0 = 
    self.proof_0.mod_verify(
      &gens.gens_n,
      transcript,
      &l_vec,
      &P,
      &y,);
    
    let y_hat = c_0  * y + self.proof_0.t;

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

    let Q = (self.proof_0.A.unpack()? + c_0 * P.unpack()? + c_1 * y_hat * gens.gens_1.G[0]).compress();

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
    let (proof, P, P_hat, ) = Pi_c_Proof::prove(
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
      .verify(n, &gens, &mut verifier_transcript, &l, &P, &y, &P_hat)
      .is_ok());
  }
}
