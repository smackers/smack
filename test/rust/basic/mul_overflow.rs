#[macro_use]
extern crate smack;
use smack::*;

// @flag --integer-overflow
// @expect error

fn main() {
  let a: u8 = 128;
  let b: u8 = 2;
  let c = a * b;
}
