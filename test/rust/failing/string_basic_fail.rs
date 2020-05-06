#[macro_use]
mod smack;
use smack::*;

// @expect error

fn main() {
  let s = String::from("Hello, world!");
  assert!(s.capacity() < 5);
}
