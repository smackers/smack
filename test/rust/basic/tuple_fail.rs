#[macro_use]
mod smack;
use smack::*;

// @expect error

fn main() {
  let t = (2u8.nondet(), 3u8.nondet());
  let (a, b) = t;
  assume!(a < 4);
  assume!(b < 5);
  assert!(t.0 + t.1 < 7);
}
