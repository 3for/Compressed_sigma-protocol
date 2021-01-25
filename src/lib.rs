#![allow(non_snake_case)]
#![feature(test)]
#![deny(missing_docs)]
#![feature(external_doc)]
#![doc(include = "../README.md")]

extern crate curve25519_dalek;
extern crate digest;
extern crate merlin;
extern crate rand;
extern crate sha3;

mod commitments;
mod errors;
mod group;
mod random;
mod transcript;
mod math;

mod scalar;
mod sigma_protocol;
mod nizk;
mod polynomial;


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
