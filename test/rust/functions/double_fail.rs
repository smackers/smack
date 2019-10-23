#[macro_use]
mod smack;
use smack::*;

// @expect error

fn double(a: u32) -> u32 {
  a * 2
}

fn main() {
  let a = 2u32.nondet();
  let b = double(a);
  assert!(b != 2*a);
}
