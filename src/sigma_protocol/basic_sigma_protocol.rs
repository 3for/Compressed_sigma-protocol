use super::super::transcript::{AppendToTranscript, ProofTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments, MultiCommitGens};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct KnowledgeProof {
  alpha: CompressedGroup,
  z1: Scalar,
  z2: Scalar,
}

impl KnowledgeProof {
  fn protocol_name() -> &'static [u8] {
    b"knowledge proof"
  }

  pub fn prove(
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x: &Scalar,
    r: &Scalar,
  ) -> (KnowledgeProof, CompressedGroup) {
    transcript.append_protocol_name(KnowledgeProof::protocol_name());

    // produce two random Scalars
    let t1 = random_tape.random_scalar(b"t1");
    let t2 = random_tape.random_scalar(b"t2");

    let C = x.commit(&r, gens_n).compress();
    C.append_to_transcript(b"C", transcript);

    let alpha = t1.commit(&t2, gens_n).compress();
    alpha.append_to_transcript(b"alpha", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = x * c + t1;
    let z2 = r * c + t2;

    (KnowledgeProof { alpha, z1, z2 }, C)
  }

  pub fn verify(
    &self,
    gens_n: &MultiCommitGens,
    transcript: &mut Transcript,
    C: &CompressedGroup,
  ) -> Result<(), ProofVerifyError> {
    transcript.append_protocol_name(KnowledgeProof::protocol_name());
    C.append_to_transcript(b"C", transcript);
    self.alpha.append_to_transcript(b"alpha", transcript);

    let c = transcript.challenge_scalar(b"c");

    let lhs = self.z1.commit(&self.z2, gens_n).compress();
    let rhs = (c * C.unpack()? + self.alpha.unpack()?).compress();

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
  fn check_knowledgeproof() {
    let mut csprng: OsRng = OsRng;

    let gens_1 = MultiCommitGens::new(1, b"test-knowledgeproof");

    let x = Scalar::random(&mut csprng);
    let r = Scalar::random(&mut csprng);

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, committed_value) =
      KnowledgeProof::prove(&gens_1, &mut prover_transcript, &mut random_tape, &x, &r);

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&gens_1, &mut verifier_transcript, &committed_value)
      .is_ok());
  }
}
