use super::super::transcript::{ProofTranscript, AppendToTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::*;
use crate::sigma_protocol::zk_protocol_7::Pi_NULLITY_Proof;
use super::scalar_math;
use crate::scalar::ScalarFromPrimitives;
use crate::polynomial::lagrange::LagrangePolynomialDirect;
use crate::polynomial::Polynomial;

// // Protocol 8 in the paper: Compressed Proof of Knowledge $\Pi_cs$ 
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_cs_Proof {
  proof: Pi_NULLITY_Proof,
  Py: CompressedGroup,
  P_hat: CompressedGroup,
}
// different linear forms, same $\vec{x}$
impl Pi_cs_Proof {
  fn protocol_name() -> &'static [u8] {
    b"zk pi_cs proof"
  }


  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    x_vec: &[Scalar],
    alpha_vec: &[(Scalar, Scalar)],
    beta_vec: &[(Scalar, Scalar)],
    l_matrix: &Vec<Vec<Scalar>>,
  ) -> (Pi_cs_Proof, Vec<Vec<Scalar>>) {
    transcript.append_protocol_name(Pi_cs_Proof::protocol_name());

    let ny = gens.gens_n.n;
    let nx = x_vec.len();
    let m = alpha_vec.len();

    let mut f_vec = alpha_vec.to_vec().clone();
    let mut g_vec = beta_vec.to_vec().clone();
    let rho_f = random_tape.random_scalar(b"rho_f");
    let rho_g = random_tape.random_scalar(b"rho_g");
    f_vec.push((Scalar::zero(), rho_f));
    g_vec.push((Scalar::zero(), rho_g));

    let poly_f = LagrangePolynomialDirect::new(&f_vec);
    let poly_g = LagrangePolynomialDirect::new(&g_vec);
    let poly_h = (poly_f.lg_poly).naive_mul(&poly_g.lg_poly);

    for i in 0..f_vec.len() {
      assert_eq!(poly_f.evaluate(&(f_vec[i].0)), f_vec[i].1);
      assert_eq!(poly_g.evaluate(&(g_vec[i].0)), g_vec[i].1);
      assert_eq!(poly_h.evaluate(&(f_vec[i].0)), f_vec[i].1 * g_vec[i].1);
    }

    let mut y_vec: Vec<Scalar> = x_vec.to_vec().clone();
    y_vec.push(rho_f);
    y_vec.push(rho_g);
    for i in 0..(2*m+1) { // h(0), h(1),...,h(2m)
      y_vec.push(poly_h.evaluate(&(i as usize).to_scalar()));
    }

    y_vec.push(-Scalar::one());
    y_vec.push(-Scalar::one());
    y_vec.push(-Scalar::one());

    assert_eq!(y_vec.len(), gens.gens_n.n);

    let Py = y_vec.commit(&Scalar::zero(), &gens.gens_n).compress();
    Py.append_to_transcript(b"Py", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = poly_f.evaluate(&c);
    let z2 = poly_g.evaluate(&c);
    let z3 = poly_h.evaluate(&c);
    assert_eq!(z1*z2, z3);


    let mut f_coeffs = poly_f.lg_poly.coeffs;
    let mut g_coeffs = poly_g.lg_poly.coeffs;
    let mut h_coeffs = poly_h.coeffs;
    f_coeffs.push(z1);
    f_coeffs.append(&mut scalar_math::zeros(ny-(m+2)));
    g_coeffs.push(Scalar::zero());
    g_coeffs.push(z2);
    g_coeffs.append(&mut scalar_math::zeros(ny-(m+3)));
    h_coeffs.push(Scalar::zero());
    h_coeffs.push(Scalar::zero());
    h_coeffs.push(z3);
    h_coeffs.append(&mut scalar_math::zeros(ny-(2*m+4)));

    let mut l_matrix_new = l_matrix.clone();
    l_matrix_new.push(f_coeffs);
    l_matrix_new.push(g_coeffs);
    l_matrix_new.push(h_coeffs);

    for i in 0..l_matrix_new.len() {
      println!("zyd i :{:?}", i);
      assert_eq!(scalar_math::compute_linearform(&l_matrix_new[i], &y_vec), Scalar::zero());
    }


    let (proof, P, P_hat, y) = Pi_NULLITY_Proof::prove(
      &gens,
      transcript,
      random_tape,
      &y_vec,
      &Scalar::zero(),
      &l_matrix_new,
    );

    assert_eq!(P, Py);

    (
      Pi_cs_Proof{
        proof,
        Py,
        P_hat,
      },
      l_matrix_new
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    l_matrix_new: &Vec<Vec<Scalar>>,
  ) -> Result<(), ProofVerifyError> {
    assert!(gens.gens_n.n >= n);

    transcript.append_protocol_name(Pi_cs_Proof::protocol_name());
    
    self.Py.append_to_transcript(b"Py", transcript);

    let c = transcript.challenge_scalar(b"c");
    

    return self.proof.verify(
      n,
      &gens,
      transcript,
      &l_matrix_new,
      &self.Py,
      &Scalar::zero(),
      &self.P_hat,
    );
  }

}


#[cfg(test)]
mod tests {
  use super::*;
  use rand::rngs::OsRng;
  use crate::scalar::ScalarFromPrimitives;
  
  #[test]
  fn check_pi_cs_proof() {
    let mut csprng: OsRng = OsRng;

    let s = 21;
    let nx = 3;
    let m = 3;
    let ny = nx + 2*m + 3 + 3; //should be power_of_two - 1

    let gens = DotProductProofGens::new(ny, b"test-1023");

    let mut l_matrix: Vec<Vec<Scalar>> = Vec::new();
    let mut x_vec: Vec<Scalar> = Vec::new();
    for _ in 0..nx-1 {
      x_vec.push(Scalar::random(&mut csprng));
    }

    let gamma = Scalar::random(&mut csprng);
    let tmp_x_vec = x_vec.clone();
    x_vec.push(-Scalar::one());
    let raw_vec = x_vec.clone();
    let zero_vec: Vec<Scalar> = scalar_math::zeros(ny-nx);
    x_vec.extend(zero_vec.iter().clone());
    for _ in 0..s {
      let mut tmp: Vec<Scalar> = (0..nx-1).map(|_| Scalar::random(&mut csprng)).collect();
      //make $<L_i, \vec{x}>=0$
      let y = scalar_math::compute_linearform(&tmp, &tmp_x_vec);
      tmp.push(y);   

      tmp.extend(zero_vec.iter().clone());   
      l_matrix.push(tmp.clone());

      assert_eq!(scalar_math::compute_linearform(&tmp, &x_vec), Scalar::zero());
    }

    let mut alpha_vec: Vec<(Scalar, Scalar)> = Vec::new();
    let mut beta_vec: Vec<(Scalar, Scalar)> = Vec::new();

    for i in 0..m {
      alpha_vec.push(((i+1 as usize).to_scalar(), Scalar::random(&mut csprng)));
      beta_vec.push(((i+1 as usize).to_scalar(), Scalar::random(&mut csprng)));
    }

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, l_matrix_new) = Pi_cs_Proof::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &raw_vec,
      &alpha_vec,
      &beta_vec,
      &l_matrix,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(ny, &gens, &mut verifier_transcript, &l_matrix_new)
      .is_ok());
  }
}
