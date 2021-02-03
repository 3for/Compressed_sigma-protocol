use super::super::transcript::{ProofTranscript, AppendToTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::{DotProductProofGens};
use crate::sigma_protocol::zk_protocol_7::Pi_NULLITY_Proof;
use super::scalar_math;
use crate::scalar::ScalarFromPrimitives;
use crate::polynomial::lagrange::{LagrangePolynomialLinear};
use crate::polynomial::Polynomial;

// // Protocol 8 in the paper: Compressed Proof of Knowledge $\Pi_cs$ 
#[derive(Debug, Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub struct Pi_r_Proof {
  proof: Pi_NULLITY_Proof,
  Py: CompressedGroup,
  P_hat: CompressedGroup,
}
// different linear forms, same $\vec{x}$
impl Pi_r_Proof {
  fn protocol_name() -> &'static [u8] {
    b"zk pi_r proof"
  }


  pub fn prove(
    gens: &DotProductProofGens,
    transcript: &mut Transcript,
    random_tape: &mut RandomTape,
    y_vec_raw: &[Scalar],
    secret_out_vec: &[Scalar],
    alpha_vec: &[(Scalar, Scalar)],
    l_matrix: &Vec<Vec<Scalar>>,
  ) -> (Pi_r_Proof, Vec<Vec<Scalar>>) {
    transcript.append_protocol_name(Pi_r_Proof::protocol_name());

    let n = gens.gens_n.n;
    let m = alpha_vec.len();
    let s = secret_out_vec.len();

    let mut f_vec = alpha_vec.to_vec().clone();
    let rho_f = random_tape.random_scalar(b"rho_f");
    f_vec.push((Scalar::zero(), rho_f));
    let poly_f = LagrangePolynomialLinear::new(&f_vec);

    for i in 0..f_vec.len() {
      assert_eq!(poly_f.evaluate(&(f_vec[i].0)), f_vec[i].1);
    }

    let mut y_vec: Vec<Scalar> = y_vec_raw.to_vec().clone();
    y_vec.push(rho_f);

    let h0 = rho_f * (Scalar::one() - rho_f);
    y_vec.push(h0);
    let mut h_vec: Vec<(Scalar, Scalar)> = vec![(Scalar::zero(), h0)];

    for i in 1..m+1 {
      h_vec.push(((i as usize).to_scalar(),Scalar::zero()));
    }

    for i in (m+1)..(2*m+1) { // h(0), h(1),...,h(2m)
      let fi = poly_f.evaluate(&(i as usize).to_scalar());
      let hi = fi * (Scalar::one() - fi);
      y_vec.push(hi);
      h_vec.push(((i as usize).to_scalar(), hi));
    }
    let poly_h = LagrangePolynomialLinear::new(&h_vec);

    y_vec.push(-Scalar::one()); //make NULLITY
    for i in 0..s {
      y_vec.push(secret_out_vec[i]);
    }

    let zero_vec = scalar_math::zeros(n-y_vec.len()); // add zeros to be power_of_two.
    y_vec.extend(zero_vec.iter().clone());

    let Py = y_vec.commit(&Scalar::zero(), &gens.gens_n).compress();
    Py.append_to_transcript(b"Py", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = poly_f.evaluate(&c);
    let z2 = poly_h.evaluate(&c);
    assert_eq!(z1 * (Scalar::one() - z1), z2);

    let mut l_matrix_new: Vec<Vec<Scalar>> = Vec::new();
    for i in 0..s {
      let mut tmp = l_matrix[i].to_vec();
      tmp.extend(scalar_math::zeros(m+2+1+i).iter().clone());
      tmp.push(-Scalar::one());
      tmp.extend(scalar_math::zeros(n-tmp.len()).iter().clone());
      assert_eq!(scalar_math::compute_linearform(&tmp, &y_vec), Scalar::zero());
      l_matrix_new.push(tmp);
    }

    let m_plus1 = poly_f.coeff_polys.len();

    let mut fc_raw_vec: Vec<Scalar> = Vec::new();
    for i in 0..m_plus1 {
      let fc_i = poly_f.coeff_polys[i].evaluate(&c);
      fc_raw_vec.push(fc_i);      
    } 
    
    
    fc_raw_vec.extend(scalar_math::zeros(m+1).iter().clone());
    fc_raw_vec.push(z1);
    fc_raw_vec.extend(scalar_math::zeros(n-fc_raw_vec.len()).iter().clone());
    
    
    assert_eq!(scalar_math::compute_linearform(&fc_raw_vec, &y_vec), Scalar::zero());

    l_matrix_new.push(fc_raw_vec);

    let mut hc_raw_vec: Vec<Scalar> = scalar_math::zeros(n);
    for i in 0..poly_h.fk_coeffs.len(){
      let hc_i = poly_h.coeff_polys[i].evaluate(&c);
      if i == 0 {      
        hc_raw_vec[m + 1] = hc_i;
      } else if i > m {
        hc_raw_vec[i + 1] = hc_i;
      }
    }
    hc_raw_vec[2*m+2] = z2;

    assert_eq!(scalar_math::compute_linearform(&hc_raw_vec, &y_vec), Scalar::zero());


    l_matrix_new.push(hc_raw_vec);

  

    for i in 0..l_matrix_new.len() {
      assert_eq!(scalar_math::compute_linearform(&l_matrix_new[i], &y_vec), Scalar::zero());
    }

    let (proof, P, P_hat, _y) = Pi_NULLITY_Proof::prove(
      &gens,
      transcript,
      random_tape,
      &y_vec,
      &Scalar::zero(),
      &l_matrix_new,
    );

    assert_eq!(P, Py);

    (
      Pi_r_Proof{
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

    transcript.append_protocol_name(Pi_r_Proof::protocol_name());
    
    self.Py.append_to_transcript(b"Py", transcript);

    let _c = transcript.challenge_scalar(b"c");

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
  use crate::scalar::ScalarFromPrimitives;
  
  #[test]
  fn check_pi_r_rangeproof() {
    let secret = 4242344947u64; //prove lie in the range [0, 2^64]
    let s = 1; // secret number.
    let range = 64;
    let n = ((2 * range + 3 + s + 1) as usize).next_power_of_two() - 1;

    let gens = DotProductProofGens::new(n, b"test");


    //binary representation of `secret`.
    let mut x_vec: Vec<Scalar> = Vec::with_capacity(range); 
    let mut l_matrix: Vec<Vec<Scalar>> = Vec::new();
    let mut lc: Vec<Scalar> = scalar_math::zeros(range);
    let mut exp_2 = Scalar::one(); // start at 2^0 = 1.
    let mut alpha_vec: Vec<(Scalar, Scalar)> = Vec::new();
    for i in 0..range {
      x_vec.push(Scalar::from((secret >> i) & 1));
      lc[i] = exp_2;
      exp_2 = exp_2 + exp_2; // 2^i -> 2^(i+1)

      alpha_vec.push((((i + 1) as usize).to_scalar(), x_vec[i]));
    }

    assert_eq!(scalar_math::compute_linearform(&lc, &x_vec), Scalar::from(secret));

    l_matrix.push(lc);
    let y_vec_raw: Vec<Scalar> = x_vec.clone(); 
    let secret_out_vec: Vec<Scalar> =[Scalar::from(secret)].to_vec();
    
    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, l_matrix_new) = Pi_r_Proof::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &y_vec_raw,
      &secret_out_vec,
      &alpha_vec,
      &l_matrix,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &l_matrix_new)
      .is_ok());
  }
}
