#[macro_use]
mod smack;
use smack::*;

// @flag --integer-overflow
// @expect error

fn main() {
  let a: u8 = 128;
  let b: u8 = 128;
  let c = a + b;
}
