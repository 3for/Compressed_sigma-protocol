//! This module is an adaptation of code from the bulletproofs crate.
//! See NOTICE.md for more details
#![allow(non_snake_case)]
#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
use super::super::errors::ProofVerifyError;
use super::super::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::super::math::Math;
use super::super::scalar::Scalar;
use super::super::transcript::ProofTranscript;
use core::iter;
use merlin::Transcript;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct NoZKNoInvBulletReductionProof {
  L_vec: Vec<CompressedGroup>,
  R_vec: Vec<CompressedGroup>,
  a: Vec<Scalar>,
  b: Vec<Scalar>,
  G: Vec<GroupElement>,
}

impl NoZKNoInvBulletReductionProof {
  /// Create an inner-product proof.
  ///
  /// The proof is created with respect to the bases \\(G\\).
  ///
  /// The `transcript` is passed in as a parameter so that the
  /// challenges depend on the *entire* transcript (including parent
  /// protocols).
  ///
  /// The lengths of the vectors must all be the same, and must all be
  /// either 0 or a power of 2.
  pub fn nozk_prove(
    transcript: &mut Transcript,
    Q: &GroupElement,
    G_vec: &[GroupElement],
    H: &GroupElement,
    a_vec: &[Scalar],
    b_vec: &[Scalar],
  ) -> NoZKNoInvBulletReductionProof {
    // Create slices G, H, a, b backed by their respective
    // vectors.  This lets us reslice as we compress the lengths
    // of the vectors in the main loop below.
    let mut G = &mut G_vec.to_owned()[..];
    let mut a = &mut a_vec.to_owned()[..];
    let mut b = &mut b_vec.to_owned()[..];

    // All of the input vectors must have a length that is a power of two.
    let mut n = G.len();
    assert!(n.is_power_of_two());
    let lg_n = n.log2()-1;

    let G_factors: Vec<Scalar> = iter::repeat(Scalar::one()).take(n).collect();

    // All of the input vectors must have the same length.
    assert_eq!(G.len(), n);
    assert_eq!(a.len(), n);
    assert_eq!(b.len(), n);
    assert_eq!(G_factors.len(), n);

    //transcript.innerproduct_domain_sep(n as u64);

    let mut L_vec = Vec::with_capacity(lg_n);
    let mut R_vec = Vec::with_capacity(lg_n);
    println!("zyd prove n:{:?}, lg_n:{:?}", n, lg_n);

    while n != 2 {
      n /= 2;
      let (a_L, a_R) = a.split_at_mut(n);
      let (b_L, b_R) = b.split_at_mut(n);
      let (G_L, G_R) = G.split_at_mut(n);

      let c_L = inner_product(&a_L, &b_R);
      let c_R = inner_product(&a_R, &b_L);

      let L = GroupElement::vartime_multiscalar_mul(
        a_L
          .iter()
          .chain(iter::once(&c_L)),
        G_R.iter().chain(iter::once(Q)),
      );

      let R = GroupElement::vartime_multiscalar_mul(
        a_R
          .iter()
          .chain(iter::once(&c_R)),
        G_L.iter().chain(iter::once(Q)),
      );

      transcript.append_point(b"L", &L.compress());
      transcript.append_point(b"R", &R.compress());

      let u = transcript.challenge_scalar(b"u");
      println!("zyd prove u:{:?}", u);

      for i in 0..n {
        a_L[i] = a_L[i] + u * a_R[i];
        b_L[i] = b_L[i] * u + b_R[i];
        G_L[i] = GroupElement::vartime_multiscalar_mul(&[u, Scalar::one()], &[G_L[i], G_R[i]]);
      }


      L_vec.push(L.compress());
      R_vec.push(R.compress());

      a = a_L;
      b = b_L;
      G = G_L;
    }
    println!("zyd prove L_vec.len:{:?}", L_vec.len());
    NoZKNoInvBulletReductionProof { L_vec, R_vec, a: a.to_vec(), b: b.to_vec(), G: G.to_vec()}
  }

  /// Computes three vectors of verification scalars \\([u\_{i}^{2}]\\), \\([u\_{i}^{-2}]\\) and \\([s\_{i}]\\) for combined multiscalar multiplication
  /// in a parent protocol. See [inner product protocol notes](index.html#verification-equation) for details.
  /// The verifier must provide the input length \\(n\\) explicitly to avoid unbounded allocation within the inner product proof.
  fn verification_scalars(
    &self,
    n: usize,
    transcript: &mut Transcript,
  ) -> Result<(Vec<Scalar>, Vec<Scalar>, Vec<Scalar>), ProofVerifyError> {
    let lg_n = self.L_vec.len();
    if lg_n >= 32 {
      // 4 billion multiplications should be enough for anyone
      // and this check prevents overflow in 1<<lg_n below.
      return Err(ProofVerifyError::InternalError);
    }
    println!("zyd verify n:{:?}, lg_n:{:?}, self.a.len():{:?}", n, lg_n, self.a.len());
    if n/2 != (1 << lg_n) {
      return Err(ProofVerifyError::InternalError);
    }

    // 1. Recompute x_k,...,x_1 based on the proof transcript
    let mut challenges = Vec::with_capacity(lg_n);
    for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
      transcript.append_point(b"L", L);
      transcript.append_point(b"R", R);
      challenges.push(transcript.challenge_scalar(b"u"));
    }
    println!("zyd challenges:{:?}", challenges);

    // 2. Compute the ML_n Distribution mentioned in 
    // <Updatable Inner Product Argument with Logarithmic Verifier and Applications>
    // as (1,u_1,u_2,u_1u_2,u_3,u_1u_3,u_2u_3,\cdots,u_1u_2\cdots u_k)
    let mut ml_challenges: Vec<Scalar> = Vec::with_capacity(lg_n);
    ml_challenges.push(Scalar::one());
    for i in (0..challenges.len()).rev() {
      let len_ml = ml_challenges.len();
      for j in 0..len_ml {
        ml_challenges.push(challenges[i] * ml_challenges[j]);
      }
    }
    //reverse of ml_challenges
    let mut rev_ml_challenges: Vec<Scalar> = Vec::with_capacity(lg_n);
    for i in (0..ml_challenges.len()).rev() {
      rev_ml_challenges.push(ml_challenges[i]);      
    }

    println!("zyd verify ml_challenges:{:?}\n, rev_ml_challenges:{:?}", ml_challenges, rev_ml_challenges);

    // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1
    let mut challenges_inv = challenges.clone();
    let allinv = Scalar::batch_invert(&mut challenges_inv);

    // 3. Compute u_i^2 and (1/u_i)^2
    for i in 0..lg_n {
      challenges[i] = challenges[i].square();
      challenges_inv[i] = challenges_inv[i].square();
    }
    let challenges_sq = challenges;
    let challenges_inv_sq = challenges_inv;

    // 4. Compute s values inductively.
    let mut s = Vec::with_capacity(n);
    s.push(allinv);
    /*for i in 1..n {
      let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
      let k = 1 << lg_i;
      // The challenges are stored in "creation order" as [u_k,...,u_1],
      // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
      let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
      s.push(s[i - k] * u_lg_i_sq);
    }*/

    Ok((ml_challenges, rev_ml_challenges, s))
  }

  /// This method is for testing that proof generation work,
  /// but for efficiency the actual protocols would use `verification_scalars`
  /// method to combine inner product verification with other checks
  /// in a single multiscalar multiplication.
  pub fn nozk_verify(
    &self,
    n: usize,
    b: &[Scalar],
    transcript: &mut Transcript,
    Gamma: &GroupElement,
    Q: &GroupElement,
    G: &[GroupElement],
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(n, b.len());
    let (u_sq, rev_ml_challenges, s) = self.verification_scalars(n, transcript)?;
    println!("zyd verify aaaa");
    let Ls = self
      .L_vec
      .iter()
      .map(|p| p.decompress().ok_or(ProofVerifyError::InternalError))
      .collect::<Result<Vec<_>, _>>()?;
    println!("zyd verify bbbb");
    let Rs = self
      .R_vec
      .iter()
      .map(|p| p.decompress().ok_or(ProofVerifyError::InternalError))
      .collect::<Result<Vec<_>, _>>()?;
    println!("zyd verify cccc");
    //let G_hat = GroupElement::vartime_multiscalar_mul(rev_ml_challenges.iter(), G.iter());
    let mut b_odd: Vec<Scalar> = Vec::with_capacity(n/2);
    let mut b_even: Vec<Scalar> = Vec::with_capacity(n/2);
    for i in 0..b.len() {
      if i%2 == 0 {
        b_odd.push(b[i]);
      } else {
        b_even.push(b[i]);
      }
    }
    let b_L_hat = inner_product(&b_odd, &rev_ml_challenges);
    let b_R_hat = inner_product(&b_even, &rev_ml_challenges);
    assert_eq!(self.b[0], b_L_hat);
    assert_eq!(self.b[1], b_R_hat);

    let mut G_odd: Vec<GroupElement> = Vec::with_capacity(n/2);
    let mut G_even: Vec<GroupElement> = Vec::with_capacity(n/2);
    for i in 0..G.len() {
      if i%2 == 0 {
        G_odd.push(G[i]);
      } else {
        G_even.push(G[i]);
      }
    }
    let G_L_hat = GroupElement::vartime_multiscalar_mul(rev_ml_challenges.iter(), G_odd.iter());
    let G_R_hat = GroupElement::vartime_multiscalar_mul(rev_ml_challenges.iter(), G_even.iter());
    assert_eq!(self.G[0], G_L_hat);
    assert_eq!(self.G[1], G_R_hat);


    println!("zyd verify ddd");

    let Gamma_hat = GroupElement::vartime_multiscalar_mul(
      u_sq
        .iter()
        .chain(rev_ml_challenges.iter())
        .chain(iter::once(&Scalar::one())),
      Ls.iter().chain(Rs.iter()).chain(iter::once(Gamma)),
    );

    /*assert_eq!(Gamma_hat, self.a * G_hat + self.a * b_hat * Q);
    if Gamma_hat == self.a * G_hat + self.a * b_hat * Q {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }*/
    Ok(())
  }
}

/// Computes an inner product of two vectors
/// \\[
///    {\langle {\mathbf{a}}, {\mathbf{b}} \rangle} = \sum\_{i=0}^{n-1} a\_i \cdot b\_i.
/// \\]
/// Panics if the lengths of \\(\mathbf{a}\\) and \\(\mathbf{b}\\) are not equal.
pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
  let mut out = Scalar::zero();
  if a.len() != b.len() {
    panic!("inner_product(a,b): lengths of vectors do not match");
  }
  for i in 0..a.len() {
    out += a[i] * b[i];
  }
  out
}