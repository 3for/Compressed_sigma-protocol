use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::sigma_phase;
use super::scalar_math;

// Protocol 3 in the paper: compressed basic sigma protocol $\Pi_1$-protocol
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Compressed_Basic_Pi_1_Proof {
  z: Vec<Scalar>,
}

impl Compressed_Basic_Pi_1_Proof {
  fn protocol_name() -> &'static [u8] {
    b"compressed basic pi_1 proof"
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
  ) -> (Compressed_Basic_Pi_1_Proof, CompressedGroup, Scalar) {
    transcript.append_protocol_name(Compressed_Basic_Pi_1_Proof::protocol_name());

    let P_hat = z_vec.commit(&phi, gens_n).compress();
    P_hat.append_to_transcript(b"P_hat", transcript);

    
    let mut z_hat = z_vec.clone().to_vec();
    z_hat.push(*phi);

    let y_hat = scalar_math::compute_linearform(&L_hat, &z_hat);
    y_hat.append_to_transcript(b"y_hat", transcript);
    
    let c_1 = sigma_phase::challenge_phase(transcript);

    (
      Compressed_Basic_Pi_1_Proof {
        z: z_hat,
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

    transcript.append_protocol_name(Compressed_Basic_Pi_1_Proof::protocol_name());
    P_hat.append_to_transcript(b"P_hat", transcript);
    y_hat.append_to_transcript(b"y_hat", transcript);
    
    let c_1 = transcript.challenge_scalar(b"c");
    let mut result = false;
    match P_hat.unpack() {
      Ok(P) => {
        result = P + (c_1 * y_hat) * gens_1.G[0] == self.z[..self.z.len()-1].commit(&self.z[self.z.len()-1], gens_n) + c_1 * scalar_math::compute_linearform(&L_hat, &self.z) * gens_1.G[0];
        println!("zyd result:{:?}", result);
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
  fn check_compressed_basic_pi_1_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens_1 = MultiCommitGens::new(1, b"test-two"); //[k,k_h]
    let gens_1024 = MultiCommitGens::new(n, b"test-1024"); //[vec{g},h]

    let mut x: Vec<Scalar> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      x.push(Scalar::random(&mut csprng));
      a.push(Scalar::random(&mut csprng));
    }

    let r_x = Scalar::random(&mut csprng);
    
    let mut L_hat = a.clone().to_vec();
    L_hat.push(Scalar::zero());

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof_1, P_1, y_1) = Compressed_Basic_Pi_1_Proof::nozk_prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &L_hat,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof_1
      .nozk_verify(&gens_1, &gens_1024, &mut verifier_transcript, &L_hat, &P_1, &y_1)
      .is_ok());
  }
}
