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

// Section 3.1 in https://blog.csdn.net/mutourend/article/details/108654372
// amortized basic sigma protocol $\Pi_0^{Am}$-protocol
// same linear form
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_0_Am_Proof {
  A: CompressedGroup,
  z: Vec<Scalar>,
  t: Scalar, // L(\vec{r})
  phi: Scalar,
}

impl Pi_0_Am_Proof {
  fn protocol_name() -> &'static [u8] {
    b"amortized basic pi_0 proof"
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
  ) -> (Pi_0_Am_Proof, Vec<CompressedGroup>, Vec<Scalar>) {
    transcript.append_protocol_name(Pi_0_Am_Proof::protocol_name());

    assert_eq!(x_matrix.len(), gamma_vec.len());
    let s = x_matrix.len();

    let mut P_vec: Vec<CompressedGroup> = Vec::new();
    let mut y_vec: Vec<Scalar> = Vec::new();
    for i in 0..s {
      let x_vec = &x_matrix[i];
      let gamma = gamma_vec[i];
      let P = x_vec.commit(&gamma, gens_n).compress();
      P.append_to_transcript(b"P", transcript); 
      P_vec.push(P);
      let y = scalar_math::compute_linearform(&a_vec, &x_vec);
      y.append_to_transcript(b"y", transcript); 
      y_vec.push(y);
    }

    let (r_vec, rho, A, t) = sigma_phase::commit_phase( 
      &gens_1,
      &gens_n,
      transcript,
      random_tape,
      &a_vec,
    );
    
    let c = transcript.challenge_scalar(b"c");
    let c_vec = scalar_math::vandemonde_challenge(c, s);

    let (z, phi) = sigma_phase::batch_response_phase(&c_vec, &gamma_vec, &rho, &x_matrix, &r_vec);
    (
      Pi_0_Am_Proof {
        A,
        z,
        t,
        phi,
      },
      P_vec,
      y_vec,
    )
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
    assert_eq!(P_vec.len(), y_vec.len());

    transcript.append_protocol_name(Pi_0_Am_Proof::protocol_name());

    let s = y_vec.len();
    for i in 0..s {
      P_vec[i].append_to_transcript(b"P", transcript);
      y_vec[i].append_to_transcript(b"y", transcript);
    }
   
    self.A.append_to_transcript(b"A", transcript);
    self.t.append_to_transcript(b"t", transcript);

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

    result = GroupElement::vartime_multiscalar_mul(
        c_vec.clone(),
        P_depressed_vec,
      ) + self.A.unpack()? == self.z.commit(&self.phi, gens_n);

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
  fn check_pi_0_Am_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 512;
    let s = 21;

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
    
    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P, y) = Pi_0_Am_Proof::amortized_prove(
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
      .amortized_verify(&gens_1, &gens_1024, &mut verifier_transcript, &a, &P, &y)
      .is_ok());
  }

}
