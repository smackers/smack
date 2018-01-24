#[macro_use]
mod smack;
use smack::*;

fn main() {
  let bound = 7;
  let mut a = 0;
  let mut i = 0;
  while i < bound+1 {
    a += i;
    i += 1;
  }
  assert!(a != (bound+1)*bound/2);
}
