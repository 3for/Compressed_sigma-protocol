use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::scalar_math;
use rand::rngs::OsRng;

// Protocol 9 in the paper: basic sigma protocol $\Pi_0$-protocol
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_shell_Proof_Pure {
  pub R1: CompressedGroup,
  pub R2: CompressedGroup,
  pub A: CompressedGroup,
  pub A1: CompressedGroup,
  pub A2: CompressedGroup,
  pub t1: Scalar, // L1(\vec{r})
  pub t2: Scalar, // L2(\vec{r})
  pub y12: Scalar,
  pub y21: Scalar,
  pub z_vec: Vec<Scalar>, 
  pub phi: Scalar,
  pub z1_tilde: Scalar,
  pub z2_tilde: Scalar,
  pub phi1: Scalar,
  pub phi2: Scalar,
}

impl Pi_shell_Proof_Pure {
  fn protocol_name() -> &'static [u8] {
    b"pi_shell proof pure"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    gens_k1: &MultiCommitGens,
    gens_k2: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    u: &Scalar,
    w: &Scalar,
    x1_vec: &[Scalar],
    gamma1: &Scalar,
    x2_vec: &[Scalar],
    gamma2: &Scalar,
    l1_vec: &[Scalar],
    l2_vec: &[Scalar],
  ) -> (Pi_shell_Proof_Pure, CompressedGroup, Scalar, CompressedGroup, Scalar, Vec<Scalar>, Vec<Scalar>) {
    assert_eq!(l1_vec.len(), l2_vec.len());
    transcript.append_protocol_name(Pi_shell_Proof_Pure::protocol_name());
    
    assert_eq!(gens_k1.h, gens_k2.h);
    assert_eq!(gens_n.h, gens_k1.h);
    
    // 1. public info
    let mut p1_vec = x1_vec.clone().to_vec();
    p1_vec.push(*u);
    p1_vec.push(Scalar::zero());
    
    let mut p2_vec = x2_vec.clone().to_vec();  
    p2_vec.push(Scalar::zero());
    p2_vec.push(*w);

    let P1 = p1_vec.commit(gamma1, gens_n).compress();
    P1.append_to_transcript(b"P1", transcript);

    let P2 = p2_vec.commit(gamma2, gens_n).compress();
    P2.append_to_transcript(b"P2", transcript);

    let y1 = scalar_math::compute_linearform(&l1_vec, &x1_vec);
    y1.append_to_transcript(b"y1", transcript);

    let y2 = scalar_math::compute_linearform(&l2_vec, &x2_vec);
    y2.append_to_transcript(b"y2", transcript);

    // 2. challenge
    let rho = transcript.challenge_scalar(b"rho");
    
    let mut l1_hat_vec = l1_vec.clone().to_vec();
    l1_hat_vec.push(Scalar::zero());
    l1_hat_vec.push(rho + Scalar::one());

    let mut l2_hat_vec = l2_vec.clone().to_vec();
    l2_hat_vec.push(rho + Scalar::one());
    l2_hat_vec.push(Scalar::zero());

    // 3. Prover select random paras and commit
    let mut csprng: OsRng = OsRng;
    let s1 = Scalar::random(&mut csprng);
    let s2 = Scalar::random(&mut csprng);
    let psi1 = Scalar::random(&mut csprng);
    let psi2 = Scalar::random(&mut csprng);
    let R1 = s1.commit(&psi1, gens_k1).compress();
    R1.append_to_transcript(b"R1", transcript);
    let R2 = s2.commit(&psi2, gens_k2).compress();
    R2.append_to_transcript(b"R2", transcript);
    let n = l1_hat_vec.len();
    assert_eq!(n, p1_vec.len());

    p1_vec[n-2] = *u + s1;
    p2_vec[n-1] = *w + s2;

    let y21 = scalar_math::compute_linearform(&l2_hat_vec, &p1_vec);
    y21.append_to_transcript(b"y21", transcript);

    let y12 = scalar_math::compute_linearform(&l1_hat_vec, &p2_vec);
    y12.append_to_transcript(b"y12", transcript);

    assert_eq!(scalar_math::compute_linearform(&l1_hat_vec, &p1_vec), y1);
    assert_eq!(scalar_math::compute_linearform(&l2_hat_vec, &p2_vec), y2);

    let r1 = Scalar::random(&mut csprng);
    let r2 = Scalar::random(&mut csprng);
    let eta1 = Scalar::random(&mut csprng);
    let eta2 = Scalar::random(&mut csprng);

    let A1 = r1.commit(&eta1, gens_k1).compress();
    A1.append_to_transcript(b"A1", transcript);
    let A2 = r2.commit(&eta2, gens_k2).compress();
    A2.append_to_transcript(b"A2", transcript);

    let r_vec = random_tape.random_vector(b"r_vec", n);
    let omega = Scalar::zero();//random_tape.random_scalar(b"omega");
    let A = r_vec.commit(&omega, gens_n).compress();
    A.append_to_transcript(b"A", transcript);

    let t1 = scalar_math::compute_linearform(&l1_hat_vec, &r_vec);
    t1.append_to_transcript(b"t1", transcript);
    let t2 = scalar_math::compute_linearform(&l2_hat_vec, &r_vec);
    t2.append_to_transcript(b"t2", transcript);

    // 4. challenge
    let c = transcript.challenge_scalar(b"c");

    // 5. Prove
    let mut z_vec: Vec<Scalar> = Vec::new();
    for i in 0..n {
      z_vec.push(p1_vec[i] * c + p2_vec[i] * c.square() + r_vec[i]);
    }
    let phi = (gamma1 + psi1) * c + (gamma2 + psi2) * c.square() + omega;
    let z1_tilde = c * s1 + r1;
    let phi1 = c * psi1 + eta1;
    let z2_tilde = c * s2 + r2;
    let phi2 = c * psi2 + eta2;

    (
      Pi_shell_Proof_Pure {
        R1,
        R2,
        A,
        A1,
        A2,
        t1,
        t2,
        y12,
        y21,
        z_vec, 
        phi,
        z1_tilde,
        z2_tilde,
        phi1,
        phi2,
      },
      P1,
      y1,
      P2,
      y2,
      l1_hat_vec,
      l2_hat_vec,
    )
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    gens_k1: &MultiCommitGens,
    gens_k2: &MultiCommitGens,
    transcript: &mut Transcript,
    l1_vec: &[Scalar],
    l2_vec: &[Scalar],
    P1: &CompressedGroup,
    y1: &Scalar,
    P2: &CompressedGroup,
    y2: &Scalar,
  ) -> Result<(), ProofVerifyError> {

    transcript.append_protocol_name(Pi_shell_Proof_Pure::protocol_name());
    // 1. public info.
    P1.append_to_transcript(b"P1", transcript);    
    P2.append_to_transcript(b"P2", transcript);
    y1.append_to_transcript(b"y1", transcript);
    y2.append_to_transcript(b"y2", transcript);

    // 2. challenge
    let rho = transcript.challenge_scalar(b"rho");

    let mut l1_hat_vec = l1_vec.clone().to_vec();
    l1_hat_vec.push(Scalar::zero());
    l1_hat_vec.push(rho + Scalar::one());

    let mut l2_hat_vec = l2_vec.clone().to_vec();
    l2_hat_vec.push(rho + Scalar::one());
    l2_hat_vec.push(Scalar::zero());

    // 3. get proof info
    self.R1.append_to_transcript(b"R1", transcript);
    self.R2.append_to_transcript(b"R2", transcript);
    self.y21.append_to_transcript(b"y21", transcript);
    self.y12.append_to_transcript(b"y12", transcript);
    self.A1.append_to_transcript(b"A1", transcript);
    self.A2.append_to_transcript(b"A2", transcript);
    self.A.append_to_transcript(b"A", transcript);
    self.t1.append_to_transcript(b"t1", transcript);
    self.t2.append_to_transcript(b"t2", transcript);

    // 4. challenge
    let c = transcript.challenge_scalar(b"c");

    // 5. Verify
    let mut result = self.z_vec.commit(&self.phi, gens_n) == self.A.unpack()?
    + c * (P1.unpack()?+ self.R1.unpack()?) + c.square() * (P2.unpack()? + self.R2.unpack()?);

    result &= c.square() * self.y12 + c * y1 + self.t1 == scalar_math::compute_linearform(&l1_hat_vec, &self.z_vec);
    result &= c * self.y21 + c.square() * y2 + self.t2 == scalar_math::compute_linearform(&l2_hat_vec, &self.z_vec);
    result &= c * self.R1.unpack()? + self.A1.unpack()? == self.z1_tilde.commit(&self.phi1, gens_k1);
    result &= c * self.R2.unpack()? + self.A2.unpack()? == self.z2_tilde.commit(&self.phi2, gens_k2);

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
  fn check_pi_shell_proof() {
    let mut csprng: OsRng = OsRng;

    let n = 1022;

    let gens_1024 = MultiCommitGens::new(n+2, b"test-1024");
    
    let gens_k1 = MultiCommitGens {
      n: 1,
      G: gens_1024.G[n..n+1].to_vec(),
      h: gens_1024.h,
    };
    let gens_k2 = MultiCommitGens {
      n: 1,
      G: gens_1024.G[n+1..n+2].to_vec(),
      h: gens_1024.h,
    };

    let mut x1_vec: Vec<Scalar> = Vec::new();
    let mut x2_vec: Vec<Scalar> = Vec::new();
    let mut l1_vec: Vec<Scalar> = Vec::new();
    let mut l2_vec: Vec<Scalar> = Vec::new();
    for _ in 0..n {
      x1_vec.push(Scalar::random(&mut csprng));
      x2_vec.push(Scalar::random(&mut csprng));
      l1_vec.push(Scalar::random(&mut csprng));
      l2_vec.push(Scalar::random(&mut csprng));
    }

    let gamma1 = Scalar::random(&mut csprng);
    let gamma2 = Scalar::random(&mut csprng);

    let u = Scalar::random(&mut csprng);
    let w = Scalar::random(&mut csprng);
    
    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, P1, y1, P2, y2, _l1_hat_vec, _l2_hat_vec) = Pi_shell_Proof_Pure::prove(
      &gens_1024,
      &gens_k1,
      &gens_k2,
      &mut prover_transcript,
      &mut random_tape,
      &u,
      &w,
      &x1_vec,
      &gamma1,
      &x2_vec,
      &gamma2,
      &l1_vec,
      &l2_vec,
    );
    
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1024, &gens_k1, &gens_k2, &mut verifier_transcript,
       &l1_vec, &l2_vec, &P1, &y1, &P2, &y2)
      .is_ok());
  }
}
