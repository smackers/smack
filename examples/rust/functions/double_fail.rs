#[macro_use]
mod smack;
use smack::*;

fn double(a: u32) -> u32 {
  a * 2
}

fn main() {
  let a = 2;
  let b = double(a);
  assert!(b != 4);
}
