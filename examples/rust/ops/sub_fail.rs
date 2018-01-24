#[macro_use]
mod smack;
use smack::*;

fn main() {
  let a = 2;
  let b = 3;
  assert!(b-a != 1);
}
