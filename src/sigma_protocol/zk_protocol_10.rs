use super::super::transcript::{ProofTranscript, AppendToTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, GROUP_BASEPOINT, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{MultiCommitGens, Commitments};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::*;
use crate::sigma_protocol::zk_protocol_7::Pi_NULLITY_Proof;
use super::scalar_math;

// // Protocol 4 in the paper: Compressed Proof of Knowledge $\Pi_OPEN$ 
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_P_Proof {
  proof: Pi_NULLITY_Proof,
  A: CompressedGroup,
  Py: CompressedGroup,
  z: Scalar,
  phi: Scalar,
  P_hat: CompressedGroup,
}
// different linear forms, same $\vec{x}$
impl Pi_P_Proof {
  fn protocol_name() -> &'static [u8] {
    b"zk pi_p proof"
  }

  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    v_vec: &[Scalar],
    gamma_vec: &[Scalar],
    aux_vec: &[Scalar],
  ) -> (Pi_P_Proof, Vec<CompressedGroup>) {
    transcript.append_protocol_name(Pi_P_Proof::protocol_name());

    let s = v_vec.len();
    let t = aux_vec.len();
    assert_eq!(gens.gens_n.n, s+t+1);

    let mut P_vec: Vec<CompressedGroup> = Vec::new();
    for i in 0..s {
      let Pi = v_vec[i].commit(&gamma_vec[i], &gens.gens_1).compress();
      Pi.append_to_transcript(b"Pi", transcript);
      P_vec.push(Pi);
    }

    let r = random_tape.random_scalar(b"r");
    let rho = random_tape.random_scalar(b"rho");
    let A = r.commit(&rho, &gens.gens_1).compress();
    A.append_to_transcript(b"A", transcript);

    let mut y_vec = v_vec.clone().to_vec();
    y_vec.push(r);
    y_vec.extend(aux_vec.iter().clone());

    let Py = y_vec.commit(&Scalar::zero(), &gens.gens_n).compress();
    Py.append_to_transcript(b"Py", transcript);

    let c = transcript.challenge_scalar(b"c");

    let c_vec = scalar_math::vandemonde_challenge(c, s);
    
    let z = scalar_math::compute_linearform(&v_vec, &c_vec) + r;
    let phi = scalar_math::compute_linearform(&gamma_vec, &c_vec) + rho;

    let mut l_vec = c_vec.clone();
    l_vec.push(Scalar::one());
    for _ in 0..t {
      l_vec.push(Scalar::zero());
    }

    let mut l_matrix: Vec<Vec<Scalar>> = Vec::new();
    l_matrix.push(l_vec);

    let (proof, P, P_hat, y) = Pi_NULLITY_Proof::prove(
      &gens,
      transcript,
      random_tape,
      &y_vec,
      &Scalar::zero(),
      &l_matrix,
    );

    assert_eq!(P, Py);
    assert_eq!(y, z);

    (
      Pi_P_Proof{
        proof,
        A,
        Py,
        z,
        phi,
        P_hat,
      },
      P_vec
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    P_vec: &[CompressedGroup],
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);

    transcript.append_protocol_name(Pi_P_Proof::protocol_name());
    
    let s = P_vec.len();
    for i in 0..s {
      P_vec[i].append_to_transcript(b"Pi", transcript);
    }
    self.A.append_to_transcript(b"A", transcript);
    self.Py.append_to_transcript(b"Py", transcript);

    let c = transcript.challenge_scalar(b"c");
    let c_vec = scalar_math::vandemonde_challenge(c, s);
    
    let mut l_vec = c_vec.clone();
    l_vec.push(Scalar::one());
    let t = n-s-1;
    for _ in 0..t {
      l_vec.push(Scalar::zero());
    }

    let mut l_matrix: Vec<Vec<Scalar>> = Vec::new();
    l_matrix.push(l_vec);

    let mut P_depressed_vec: Vec<GroupElement> = Vec::new();
    for i in 0..s {       
      match P_vec[i].unpack() {
        Ok(P) => P_depressed_vec.push(P),
        Err(r) => return Err(r),
      }
    }
    let result = GroupElement::vartime_multiscalar_mul(
        c_vec,
        P_depressed_vec,
      ) + self.A.unpack()? == self.z.commit(&self.phi, &gens.gens_1);

    if !result {
      return Err(ProofVerifyError::InternalError);
    }

    return self.proof.verify(
      n,
      &gens,
      transcript,
      &l_matrix,
      &self.Py,
      &self.z,
      &self.P_hat,
    );
  }

}


#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  #[test]
  fn check_pi_p_proof() {
    let mut csprng: OsRng = OsRng;

    let s = 1000;
    let t = 22;
    let n = s + t + 1;

    let gens = DotProductProofGens::new(n, b"test-1023");

    let mut v_vec: Vec<Scalar> = Vec::new();
    let mut gamma_vec: Vec<Scalar> = Vec::new();
    for _ in 0..s {
      v_vec.push(Scalar::random(&mut csprng));
      gamma_vec.push(Scalar::random(&mut csprng));
    }
    let mut aux_vec: Vec<Scalar> = Vec::new();
    for _ in 0..t {
      aux_vec.push(Scalar::random(&mut csprng));
    }


    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P_vec) = Pi_P_Proof::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &v_vec,
      &gamma_vec,
      &aux_vec,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &P_vec)
      .is_ok());
  }
}
