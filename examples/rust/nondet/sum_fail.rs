#[macro_use]
mod smack;
use smack::*;

fn main() {
  let mut sum = 0;
  let b = 7u64.nondet();
  assume!(b > 1);
  for i in 0..b as u64 {
    sum += i;
  }
  assert!(sum != b*(b-1)/2);
}
