#[macro_use]
mod smack;
use smack::*;

// @flag --unroll=10
// @expect error

fn fac(n: u64) -> u64 {
  match n {
    0 => 1,
    1 => 1,
    _ => n*fac(n-1)
  }
}
fn main() {
  let mut a = 1;
  let n = 6u64.nondet();
  for i in 1..n+1 as u64 {
    a *= i;
  }
  assert!(a != fac(n)); // a should equal 6!
}
