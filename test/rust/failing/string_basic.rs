#[macro_use]
mod smack;
use smack::*;

// @expect verified

fn main() {
  let s = String::from("Hello, world!");
  assert!(s.capacity() >= 5);
}
