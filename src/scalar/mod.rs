use crate::polynomial::Field;
use core::fmt::Display;
use num_traits::{Zero, One};

mod ristretto255;

pub type Scalar = ristretto255::Scalar;
pub type ScalarBytes = curve25519_dalek::scalar::Scalar;

pub trait ScalarFromPrimitives {
  fn to_scalar(self) -> Scalar;
}

impl ScalarFromPrimitives for usize {
  #[inline]
  fn to_scalar(self) -> Scalar {
    (0..self).map(|_i| Scalar::one()).sum()
  }
}

impl ScalarFromPrimitives for bool {
  #[inline]
  fn to_scalar(self) -> Scalar {
    if self {
      Scalar::one()
    } else {
      Scalar::zero()
    }
  }
}

pub trait ScalarBytesFromScalar {
  fn decompress_scalar(s: &Scalar) -> ScalarBytes;
  fn decompress_vector(s: &[Scalar]) -> Vec<ScalarBytes>;
}

impl ScalarBytesFromScalar for Scalar {
  fn decompress_scalar(s: &Scalar) -> ScalarBytes {
    ScalarBytes::from_bytes_mod_order(s.to_bytes())
  }

  fn decompress_vector(s: &[Scalar]) -> Vec<ScalarBytes> {
    (0..s.len())
      .map(|i| Scalar::decompress_scalar(&s[i]))
      .collect::<Vec<ScalarBytes>>()
  }
}

impl Field for Scalar {
  fn square(&self) -> Self {
    let mut result = *self;
    result.square_in_place();
    result
  }

  fn square_in_place(&mut self) -> &mut Self {
    *self = self.square();
    self
  }

  fn inverse(&self) -> Self {
    let mut result = *self;
    result.inverse_in_place();
    result
  }

  fn inverse_in_place(&mut self) -> &mut Self {
    *self = self.unwrap().invert();
    Option<self>
  }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "Scalar{{\n\tbytes: {:?},\n}}", &self)
    }
}

impl Zero for Scalar {
    /// Returns the zero polynomial.
    fn zero() -> Self {
        Scalar::zero()
    }

    /// Checks if the given polynomial is zero.
    fn is_zero(&self) -> bool {
        *self == Scalar::zero()
    }
}

impl One for Scalar {
    /// Returns the zero polynomial.
    fn one() -> Self {
        Scalar::one()
    }

    /// Checks if the given polynomial is zero.
    fn is_one(&self) -> bool {
        *self == Scalar::one()
    }
}


