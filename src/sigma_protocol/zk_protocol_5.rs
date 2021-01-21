use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt};
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
  bullet_reduction_proof: BulletReductionProof,
  delta: CompressedGroup,
  beta: CompressedGroup,
  z1: Scalar,
  z2: Scalar,
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
  ) -> (Pi_c_Proof, CompressedGroup) {
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

    let (proof_1, P_hat, y_hat, L_tilde, G_hat) = Pi_1_Proof::mod_prove(
      &gens.gens_n,
      transcript,
      random_tape,
      &z_vec,
      &phi,
      &l_vec,
      &proof_0,
    );

    let (proof_2, Q) = Pi_2_Proof::mod_prove(
      &gens,
      transcript,
      random_tape,
      &L_tilde,
      &y_hat,
      &proof_1,
      &G_hat,
    );


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

    let Cx = x_vec.commit(&blind_x, &gens.gens_n).compress();
    Cx.append_to_transcript(b"Cx", transcript);
    //add a challenge to avoid the Prover cheat as mentioned in Halo.
    let c_1 = transcript.challenge_scalar(b"c_1");
    
    let l_vec_new: Vec<Scalar>
     = l_vec.iter()
              .map(|l| c_1 * l)
              .collect();

    let blind_Gamma = blind_x;
    let (bullet_reduction_proof, _Gamma_hat, z_hat, l_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::prove(
        transcript,
        &gens.gens_1.G[0],
        &gens.gens_n.G,
        &gens.gens_n.h,
        x_vec,
        &l_vec_new,
        &blind_Gamma,
        &blinds_vec,
      );
    let y_hat = z_hat * l_hat;

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
    let z2 = l_hat * (c * rhat_Gamma + r_beta) + r_delta;

    (
      Pi_c_Proof {
        bullet_reduction_proof,
        delta,
        beta,
        z1,
        z2,
      },
      Cx,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    l_vec: &[Scalar],
    Cx: &CompressedGroup,
    y: &Scalar,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);
    assert_eq!(l_vec.len(), n);

    transcript.append_protocol_name(Pi_c_Proof::protocol_name());
    Cx.append_to_transcript(b"Cx", transcript);
    //add a challenge to avoid the Prover cheat as mentioned in Halo.
    let c_1 = transcript.challenge_scalar(b"c_1");

    let l_vec_new: Vec<Scalar>
     = l_vec.iter()
              .map(|l| c_1 * l)
              .collect();

    let Gamma = Cx.unpack()? + c_1 * y * gens.gens_1.G[0];

    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(n, &l_vec_new, transcript, &Gamma, &gens.gens_n.G)?;
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
  fn check_pi_c_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens = DotProductProofGens::new(n, b"test-1024");

    let l: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let z: Vec<Scalar> = (0..n).map(|_i| Scalar::random(&mut csprng)).collect();
    let y = DotProductProof::compute_dotproduct(&l, &z);
    
    let r_z = Scalar::random(&mut csprng);
    let Cz = z.commit(&r_z, &gens.gens_n).compress();

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, Cz) = Pi_c_Proof::prove(
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
      .verify(n, &gens, &mut verifier_transcript, &l, &Cz, &y)
      .is_ok());
  }
}
