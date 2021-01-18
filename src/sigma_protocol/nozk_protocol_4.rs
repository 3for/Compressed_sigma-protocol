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
use super::super::nizk::*;
use crate::math::Math;
use crate::nizk::bullet::BulletReductionProof;

// Protocol 4 in the paper: Compressed Proof of Knowledge $\Pi_2$ for $R_2$
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_2_Proof {
  bullet_reduction_proof: BulletReductionProof,
  delta: CompressedGroup,
  beta: CompressedGroup,
  z1: Scalar,
  z2: Scalar,
}

impl Pi_2_Proof {
  fn protocol_name() -> &'static [u8] {
    b"nozk compressed pi_2 proof"
  }

  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    a_vec: &[Scalar],
    blind_a: &Scalar,
    x_vec: &[Scalar],
    y: &Scalar,
  ) -> (Pi_2_Proof, CompressedGroup) {
    transcript.append_protocol_name(Pi_2_Proof::protocol_name());

    let n = a_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens.gens_n.n, n);

    // produce randomness for generating a proof
    let d = random_tape.random_scalar(b"d");
    let r_delta = random_tape.random_scalar(b"r_delta");
    let r_beta = random_tape.random_scalar(b"r_delta");
    let blinds_vec = {
      let v1 = random_tape.random_vector(b"blinds_vec_1", 2 * n.log2());
      let v2 = random_tape.random_vector(b"blinds_vec_2", 2 * n.log2());
      (0..v1.len())
        .map(|i| (v1[i], v2[i]))
        .collect::<Vec<(Scalar, Scalar)>>()
    };

    let Ca = a_vec.commit(&blind_a, &gens.gens_n).compress();
    Ca.append_to_transcript(b"Ca", transcript);
    //add a challenge to avoid the Prover cheat as mentioned in Halo.
    let c_1 = transcript.challenge_scalar(b"c_1");
    
    let x_vec_new: Vec<Scalar>
     = x_vec.iter()
              .map(|x| c_1 * x)
              .collect();

    let blind_Gamma = blind_a;
    let (bullet_reduction_proof, _Gamma_hat, a_hat, x_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::prove(
        transcript,
        &gens.gens_1.G[0],
        &gens.gens_n.G,
        &gens.gens_n.h,
        a_vec,
        &x_vec_new,
        &blind_Gamma,
        &blinds_vec,
      );
    let y_hat = a_hat * x_hat;

    let delta = {
      let gens_hat = MultiCommitGens {
        n: 1,
        G: vec![g_hat],
        h: gens.gens_1.h,
      };
      d.commit(&r_delta, &gens_hat).compress()
    };
    delta.append_to_transcript(b"delta", transcript);

    let beta = d.commit(&r_beta, &gens.gens_1).compress();
    beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = d + c * y_hat;
    let z2 = x_hat * (c * rhat_Gamma + r_beta) + r_delta;

    (
      Pi_2_Proof {
        bullet_reduction_proof,
        delta,
        beta,
        z1,
        z2,
      },
      Ca,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    x: &[Scalar],
    Ca: &CompressedGroup,
    y: &Scalar,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);
    assert_eq!(x.len(), n);

    transcript.append_protocol_name(Pi_2_Proof::protocol_name());
    Ca.append_to_transcript(b"Ca", transcript);
    //add a challenge to avoid the Prover cheat as mentioned in Halo.
    let c_1 = transcript.challenge_scalar(b"c_1");

    let x_vec_new: Vec<Scalar>
     = x.iter()
              .map(|x| c_1 * x)
              .collect();

    let Gamma = Ca.unpack()? + c_1 * y * gens.gens_1.G[0];

    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(n, &x_vec_new, transcript, &Gamma, &gens.gens_n.G)?;
    self.delta.append_to_transcript(b"delta", transcript);
    self.beta.append_to_transcript(b"beta", transcript);

    let c = transcript.challenge_scalar(b"c");

    let c_s = &c;
    let beta_s = self.beta.unpack()?;
    let a_hat_s = &a_hat;
    let delta_s = self.delta.unpack()?;
    let z1_s = &self.z1;
    let z2_s = &self.z2;

    let lhs = ((Gamma_hat * c_s + beta_s) * a_hat_s + delta_s).compress();
    let rhs = ((g_hat + gens.gens_1.G[0] * a_hat_s) * z1_s + gens.gens_1.h * z2_s).compress();

    assert_eq!(lhs, rhs);

    if lhs == rhs {
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
  fn check_pi_2_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens = DotProductProofGens::new(n, b"test-1024");

    let x: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let a: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let y = DotProductProof::compute_dotproduct(&x, &a);

    let r_a = Scalar::random(&mut csprng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Ca) = Pi_2_Proof::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &a,
      &r_a,
      &x,
      &y,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &x, &Ca, &y)
      .is_ok());
  }
}
