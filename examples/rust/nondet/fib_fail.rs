#[macro_use]
mod smack;
use smack::*;

fn main() {
  let (mut last, mut a, mut b) = (0, 0, 1);
  let c = 6u64.nondet();
  assume!(c > 0);
  for _ in 0..c as u64 {
    last = a;
    a = b;
    b = a + last;
  }
  assert!(a + last != b);
}
