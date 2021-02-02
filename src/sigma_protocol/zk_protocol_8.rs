use super::super::transcript::{ProofTranscript, AppendToTranscript};
use super::super::scalar::Scalar;
use super::super::group::{CompressedGroup};
use merlin::Transcript;
use super::super::random::RandomTape;
use super::super::commitments::{Commitments};
use super::super::errors::ProofVerifyError;
use serde::{Deserialize, Serialize};
use super::super::nizk::*;
use crate::sigma_protocol::zk_protocol_7::Pi_NULLITY_Proof;
use super::scalar_math;
use crate::scalar::ScalarFromPrimitives;
use crate::polynomial::lagrange::*;
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
    y_vec_raw: &[Scalar],
    out_vec: &[Scalar],
    alpha_vec: &[(Scalar, Scalar)],
    beta_vec: &[(Scalar, Scalar)],
    l_matrix: &Vec<Vec<Scalar>>,
  ) -> (Pi_cs_Proof, Vec<Vec<Scalar>>) {
    transcript.append_protocol_name(Pi_cs_Proof::protocol_name());

    let n = gens.gens_n.n;
    let nx = x_vec.len();
    let m = alpha_vec.len();

    let mut f_vec = alpha_vec.to_vec().clone();
    let mut g_vec = beta_vec.to_vec().clone();
    let rho_f = random_tape.random_scalar(b"rho_f");
    let rho_g = random_tape.random_scalar(b"rho_g");
    f_vec.push((Scalar::zero(), rho_f));
    g_vec.push((Scalar::zero(), rho_g));

    let poly_f = LagrangePolynomialLinear::new(&f_vec);
    let poly_g = LagrangePolynomialLinear::new(&g_vec);
    //let poly_h = (poly_f.lg_poly).naive_mul(&poly_g.lg_poly);

    for i in 0..f_vec.len() {
      assert_eq!(poly_f.evaluate(&(f_vec[i].0)), f_vec[i].1);
      assert_eq!(poly_g.evaluate(&(g_vec[i].0)), g_vec[i].1);
      //assert_eq!(poly_h.evaluate(&(f_vec[i].0)), f_vec[i].1 * g_vec[i].1);
    }

    let mut y_vec: Vec<Scalar> = y_vec_raw.to_vec().clone();
    y_vec.push(rho_f);
    y_vec.push(rho_g);

    let h0 = rho_f * rho_g;
    y_vec.push(h0);
    let mut h_vec: Vec<(Scalar, Scalar)> = vec![(Scalar::zero(), h0)];

    for i in 1..m+1 {
      h_vec.push(((i as usize).to_scalar(), y_vec_raw[nx+i-1]));
    }

    for i in (m+1)..(2*m+1) { // h(0), h(1),...,h(2m)
      let hi = poly_f.evaluate(&(i as usize).to_scalar()) * poly_g.evaluate(&(i as usize).to_scalar());
      y_vec.push(hi);
      h_vec.push(((i as usize).to_scalar(), hi));
    }
    let poly_h = LagrangePolynomialLinear::new(&h_vec);

    y_vec.push(-Scalar::one()); //make NULLITY

    let zero_vec = scalar_math::zeros(n-y_vec.len()); // add zeros to be power_of_two.
    y_vec.extend(zero_vec.iter().clone());

    let Py = y_vec.commit(&Scalar::zero(), &gens.gens_n).compress();
    Py.append_to_transcript(b"Py", transcript);

    let c = transcript.challenge_scalar(b"c");

    let z1 = poly_f.evaluate(&c);
    let z2 = poly_g.evaluate(&c);
    let z3 = poly_h.evaluate(&c);
    assert_eq!(z1*z2, z3);

    let mut l_matrix_new: Vec<Vec<Scalar>> = Vec::new();

    let m_plus1 = poly_f.coeff_polys.len();
    let mut fc_raw_vec: Vec<Scalar> = scalar_math::zeros(y_vec_raw.len());
    for i in 0..m_plus1 {
      let fc_i = poly_f.coeff_polys[i].evaluate(&c);
      if i < m_plus1-1 {        
        let tmp_vec = scalar_math::scalar_vector_mul(&fc_i, &l_matrix[i].to_vec());
        fc_raw_vec = scalar_math::row_row_add(&tmp_vec, &fc_raw_vec);
      } else {
        fc_raw_vec.push(fc_i);
      }
    } 
    let before_negOne_NO = nx + 3 + 2*m + 1;
    let tmp_NO = fc_raw_vec.len();
    let zeros_a = scalar_math::zeros(before_negOne_NO - tmp_NO);
    fc_raw_vec.extend(zeros_a.iter().clone());
    fc_raw_vec.push(z1);
    fc_raw_vec.extend(zero_vec.iter().clone());
    assert_eq!(scalar_math::compute_linearform(&fc_raw_vec, &y_vec), Scalar::zero());

    l_matrix_new.push(fc_raw_vec);

    let mut gc_raw_vec: Vec<Scalar> = scalar_math::zeros(y_vec_raw.len());
    for i in 0..m_plus1 {
      let gc_i = poly_g.coeff_polys[i].evaluate(&c);     
      if i < m_plus1-1 {
        let tmp_vec = scalar_math::scalar_vector_mul(&gc_i, &l_matrix[m+i].to_vec());
        gc_raw_vec = scalar_math::row_row_add(&tmp_vec, &gc_raw_vec);
      } else {
        gc_raw_vec.push(Scalar::zero());
        gc_raw_vec.push(gc_i);
      }
    }   

    let zeros_b = &zeros_a[0..(zeros_a.len()-1)];
    gc_raw_vec.extend(zeros_b.iter().clone());
    gc_raw_vec.push(z2);
    gc_raw_vec.extend(zero_vec.iter().clone());

    assert_eq!(scalar_math::compute_linearform(&gc_raw_vec, &y_vec), Scalar::zero());

    l_matrix_new.push(gc_raw_vec);

    let mut hc_raw_vec: Vec<Scalar> = scalar_math::zeros(n);
    for i in 0..poly_h.fk_coeffs.len(){
      let hc_i = poly_h.coeff_polys[i].evaluate(&c);      
      if i > 0 && i < m+1 {        
        hc_raw_vec[nx-1+i] = hc_i;
      } else if i > m {
        hc_raw_vec[nx+i+4-1] = hc_i;
      } else {
        hc_raw_vec[nx+m+1+2] = hc_i;
      }
    }
    hc_raw_vec[nx+3+2*m+1] = z3;
    assert_eq!(scalar_math::compute_linearform(&hc_raw_vec, &y_vec), Scalar::zero());


    l_matrix_new.push(hc_raw_vec);

    let lc_NO = l_matrix.len() - 2 * m;
    for i in 0..lc_NO {
      let mut tmp = l_matrix[2*m+i].to_vec();
      tmp.extend(zeros_a.iter().clone());
      tmp.push(Scalar::zero());
      tmp.push(out_vec[i]);
      tmp.extend(zero_vec.iter().clone());
      l_matrix_new.push(tmp);
    }

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
  fn check_pi_cs_proof_vitalik() {
    // x^3+x+5=35, solution: x=3
    let s = 1; //output number. Here is `~out`.
    let nx = 1;
    let m = 2;
    let ny = nx + 2*m + 3 + 1 + s; //should be power_of_two - 1
    let n = (ny as usize).next_power_of_two() - 1;

    let gens = DotProductProofGens::new(n, b"test-1023");

    let mut l_matrix: Vec<Vec<Scalar>> = Vec::new();
    let x_vec: Vec<Scalar> =[(3 as usize).to_scalar()].to_vec();
    let out_vec: Vec<Scalar> =[(35 as usize).to_scalar()].to_vec();
    let mut y_vec_raw: Vec<Scalar> = x_vec.clone(); // [x,gamma_1,gamma_2, one]
    y_vec_raw.push((9 as usize).to_scalar()); // gamma_1, same as h1
    y_vec_raw.push((27 as usize).to_scalar()); // gamma_2, same as h2
    y_vec_raw.push(Scalar::one());

    // construct linear form for alpha_1,alpha_2,beta_1,beta_2
    let u1 = [Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero()].to_vec();
    let u2 = [Scalar::zero(), Scalar::one(), Scalar::zero(), Scalar::zero()].to_vec();
    let v1 = [Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero()].to_vec();
    let v2 = [Scalar::one(), Scalar::zero(), Scalar::zero(), Scalar::zero()].to_vec();
    l_matrix.push(u1);
    l_matrix.push(u2);
    l_matrix.push(v1);
    l_matrix.push(v2);

     // construct linear form for `~out=gamma_2+x+5`. all ADD and const MUL gate.
    let lc = [Scalar::one(), Scalar::zero(), Scalar::one(), (5 as usize).to_scalar()].to_vec();
    l_matrix.push(lc);

    let mut alpha_vec: Vec<(Scalar, Scalar)> = Vec::new();
    let mut beta_vec: Vec<(Scalar, Scalar)> = Vec::new();
    alpha_vec.push((Scalar::one(), (3 as usize).to_scalar()));
    alpha_vec.push(((2 as usize).to_scalar(), (9 as usize).to_scalar()));
    beta_vec.push((Scalar::one(), (3 as usize).to_scalar()));
    beta_vec.push(((2 as usize).to_scalar(), (3 as usize).to_scalar()));

    let mut random_tape = RandomTape::new(b"proof");
    let mut prover_transcript = Transcript::new(b"example");
    let (proof, l_matrix_new) = Pi_cs_Proof::prove(
      &gens,
      &mut prover_transcript,
      &mut random_tape,
      &x_vec,
      &y_vec_raw,
      &out_vec,
      &alpha_vec,
      &beta_vec,
      &l_matrix,
    );

    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &l_matrix_new)
      .is_ok());
  }
}
