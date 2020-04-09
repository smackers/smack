#[macro_use]
mod smack;
use smack::*;

// @flag --unroll=10
// @expect error

fn main() {
  let mut sum = 0;
  let b = 7u64.nondet();
  assume!(b > 1);
  for i in 0..b as u64 {
    sum += i;
  }
  assert!(2*sum != b*(b-1));
}
