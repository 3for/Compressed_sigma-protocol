use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::sigma_phase;
use super::scalar_math;

// Protocol 2 in the paper: basic sigma protocol $\Pi_0$-protocol
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_0_Proof {
  pub A: CompressedGroup,
  pub t: Scalar, // L(\vec{r})
}

impl Pi_0_Proof {
  fn protocol_name() -> &'static [u8] {
    b"basic pi_0 proof"
  }

  pub fn mod_prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar], //private info.
    gamma: &Scalar, //blind_x
    a_vec: &[Scalar], //public info.
    y: &Scalar, //public info
  ) -> (Pi_0_Proof, CompressedGroup, Vec<Scalar>, Scalar) {
    transcript.append_protocol_name(Pi_0_Proof::protocol_name());
    
    let P = x_vec.commit(&gamma, gens_n).compress();
    P.append_to_transcript(b"P", transcript);

    //let y = scalar_math::compute_linearform(&a_vec, &x_vec);
    y.append_to_transcript(b"y", transcript);

    let (r_vec, rho, A, t) = sigma_phase::commit_phase( 
      &gens_n,
      transcript,
      random_tape,
      &a_vec,
    );

    let c = sigma_phase::challenge_phase(transcript);

    let (z, phi) = sigma_phase::response_phase(&c, &gamma, &rho, &x_vec, &r_vec);

    (
      Pi_0_Proof {
        A,
        t,
      },
      P,
      z,
      phi,
    )
  }

  pub fn mod_verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    P: &CompressedGroup,
    y: &Scalar,
  ) -> Scalar {
    assert_eq!(gens_n.n, a.len());

    transcript.append_protocol_name(Pi_0_Proof::protocol_name());
    P.append_to_transcript(b"P", transcript);
    y.append_to_transcript(b"y", transcript);
    self.A.append_to_transcript(b"A", transcript);
    self.t.append_to_transcript(b"t", transcript);

    let c = transcript.challenge_scalar(b"c");
    c
  }

}

// Protocol 2 in the paper: basic sigma protocol $\Pi_0$-protocol
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_0_Proof_Pure {
  pub A: CompressedGroup,
  pub z: Vec<Scalar>,
  pub t: Scalar, // L(\vec{r})
  pub phi: Scalar,
}

impl Pi_0_Proof_Pure {
  fn protocol_name() -> &'static [u8] {
    b"basic pi_0 proof pure"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    gamma: &Scalar,
    a_vec: &[Scalar],
  ) -> (Pi_0_Proof_Pure, CompressedGroup, Scalar) {
    transcript.append_protocol_name(Pi_0_Proof_Pure::protocol_name());
    
    let P = x_vec.commit(&gamma, gens_n).compress();
    P.append_to_transcript(b"P", transcript);

    let y = scalar_math::compute_linearform(&a_vec, &x_vec);
    y.append_to_transcript(b"y", transcript);

    let (r_vec, rho, A, t) = sigma_phase::commit_phase( 
      &gens_n,
      transcript,
      random_tape,
      &a_vec,
    );
    
    let c = sigma_phase::challenge_phase(transcript);

    let (z, phi) = sigma_phase::response_phase(&c, &gamma, &rho, &x_vec, &r_vec);

    (
      Pi_0_Proof_Pure {
        A,
        z,
        t,
        phi,
      },
      P,
      y,
    )
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    P: &CompressedGroup,
    y: &Scalar,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n, a.len());

    transcript.append_protocol_name(Pi_0_Proof_Pure::protocol_name());
    P.append_to_transcript(b"P", transcript);
    y.append_to_transcript(b"y", transcript);
    self.A.append_to_transcript(b"A", transcript);
    self.t.append_to_transcript(b"t", transcript);

    let c = transcript.challenge_scalar(b"c");

    let mut result =
      c * P.unpack()? + self.A.unpack()? == self.z.commit(&self.phi, gens_n);
    let l_z = scalar_math::compute_linearform(&self.z, &a);
    result &= c * y + self.t == l_z;

    if result {
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
  fn check_pi_0_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens_1024 = MultiCommitGens::new(n, b"test-1024");

    let mut x: Vec<Scalar> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      x.push(Scalar::random(&mut csprng));
      a.push(Scalar::random(&mut csprng));
    }

    let r_x = Scalar::random(&mut csprng);
    
    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P, y) = Pi_0_Proof_Pure::prove(
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
    );
    
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1024, &mut verifier_transcript, &a, &P, &y)
      .is_ok());
  }
}
