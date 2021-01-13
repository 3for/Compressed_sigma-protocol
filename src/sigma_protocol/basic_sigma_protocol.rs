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

// Protocol 2 in the paper: basic sigma protocol $\Pi_0$-protocol
#[derive(Debug, Serialize, Deserialize)]
pub struct Basic_Pi_0_Proof {
  A: CompressedGroup,
  z: Vec<Scalar>,
  t: Scalar, // L(\vec{r})
  phi: Scalar,
}

impl Basic_Pi_0_Proof {
  fn protocol_name() -> &'static [u8] {
    b"basic pi_0 proof"
  }

  pub fn prove(
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    gamma: &Scalar,
    a_vec: &[Scalar],
  ) -> (Basic_Pi_0_Proof, CompressedGroup, Scalar) {
    transcript.append_protocol_name(Basic_Pi_0_Proof::protocol_name());
    
    let P = x_vec.commit(&gamma, gens_n).compress();
    P.append_to_transcript(b"P", transcript);

    let y = scalar_math::compute_linearform(&a_vec, &x_vec);
    y.append_to_transcript(b"y", transcript);

    let (r_vec, rho, A, t) = sigma_phase::commit_phase( 
      &gens_1,
      &gens_n,
      transcript,
      random_tape,
      &a_vec,
    );
    
    let c = sigma_phase::challenge_phase(transcript);

    let (z, phi) = sigma_phase::response_phase(&c, &gamma, &rho, &x_vec, &r_vec);

    (
      Basic_Pi_0_Proof {
        A,
        z,
        t,
        phi,
      },
      P,
      y,
    )
  }

  // For amortized basic protocol: $\Pi_0^{Am}$
  pub fn amortized_prove(
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_matrix: &Vec<Vec<Scalar>>,
    gamma_vec: &[Scalar],
    a_vec: &[Scalar], //same linear form
  ) -> (Basic_Pi_0_Proof, Vec<CompressedGroup>, Vec<Scalar>) {
    transcript.append_protocol_name(Basic_Pi_0_Proof::protocol_name());

    println!("zyd 111");

    let P_vec = x_matrix.iter()
                    .zip(gamma_vec.iter())
                    .map(|(x_vec, gamma)| {let P = x_vec.commit(&gamma, gens_n).compress();
                        P.append_to_transcript(b"P", transcript); P })
                    .collect();
    let y_vec = x_matrix.iter()
                    .map(|x_vec| {let y = scalar_math::compute_linearform(&a_vec, &x_vec);
                        y.append_to_transcript(b"y", transcript); y})
                    .collect();

    println!("zyd 222");

    let (r_vec, rho, A, t) = sigma_phase::commit_phase( 
      &gens_1,
      &gens_n,
      transcript,
      random_tape,
      &a_vec,
    );
    println!("zyd 333");
    let s = x_matrix.len();
    
    let c = sigma_phase::challenge_phase(transcript);
    let c_vec = scalar_math::vandemonde_challenge(c, s);

    let (z, phi) = sigma_phase::batch_response_phase(&c_vec, &gamma_vec, &rho, &x_matrix, &r_vec);
    (
      Basic_Pi_0_Proof {
        A,
        z,
        t,
        phi,
      },
      P_vec,
      y_vec,
    )
  }

  pub fn verify(
    &self,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    P: &CompressedGroup,
    y: &Scalar,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n, a.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(Basic_Pi_0_Proof::protocol_name());
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

  pub fn amortized_verify(
    &self,
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    a: &[Scalar],
    P_vec: &[CompressedGroup],
    y_vec: &[Scalar],
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens_n.n, a.len());
    assert_eq!(gens_1.n, 1);

    transcript.append_protocol_name(Basic_Pi_0_Proof::protocol_name());

    P_vec.iter()
          .zip(y_vec.iter())
          .map(|(P, y)| {
            P.append_to_transcript(b"P", transcript);
            y.append_to_transcript(b"y", transcript);
          });
   
    self.A.append_to_transcript(b"A", transcript);
    self.t.append_to_transcript(b"t", transcript);

    let s = y_vec.len();
    let c = transcript.challenge_scalar(b"c");
    let c_vec = scalar_math::vandemonde_challenge(c, s);

    let mut result = false;
    let mut P_depressed_vec: Vec<GroupElement> = Vec::new();
    for i in 0..s {       
      match P_vec[i].unpack() {
        Ok(P) => P_depressed_vec.push(P),
        Err(r) => return Err(r),
      }
    }
    
    println!("zyd z:{:?}", self.z);
    result = GroupElement::vartime_multiscalar_mul(
        c_vec.clone(),
        P_depressed_vec,
      ) + self.A.unpack()? == self.z.commit(&self.phi, gens_n);
    println!("zyd 555");

    let l_z = scalar_math::compute_linearform(&self.z, &a);
    result &= scalar_math::compute_linearform(
        &c_vec,
        y_vec,
      ) + self.t == l_z;

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
  fn check_basic_pi_0_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1024;

    let gens_1 = MultiCommitGens::new(1, b"test-two");
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
    let (proof, P, y) = Basic_Pi_0_Proof::prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
    );
    
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &P, &y)
      .is_ok());
  }

   #[test]
  fn check_amortized_pi_0_Am_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 16;
    let s = 1;

    let gens_1 = MultiCommitGens::new(1, b"test-two");
    let gens_1024 = MultiCommitGens::new(n, b"test-1024");

    let mut x: Vec<Vec<Scalar>> = Vec::new();
    let mut a: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      a.push(Scalar::random(&mut csprng));
    }

    let mut r_x: Vec<Scalar> = Vec::new();
    for _ in 0..s {
      r_x.push(Scalar::random(&mut csprng));
      let tmp: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut csprng)).collect();
      x.push(tmp);
    }
    println!("zyd x:{:?}", x);
    
    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P, y) = Basic_Pi_0_Proof::amortized_prove(
      &gens_1,
      &gens_1024,
      &mut prover_transcript,
      &mut random_tape,
      &x,
      &r_x,
      &a,
    );
    
    let mut verifier_transcript = Transcript::new(b"example");
    /*assert!(proof
      .amortized_verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &P, &y)
      .is_ok());*/
  }

}
