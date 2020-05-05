#[macro_use]
mod smack;
use smack::*;

// @expect verified

fn main() {
  let ar = [2u8.nondet(), 3u8.nondet(), 4u8.nondet()];
  let idx = 1usize.nondet();
  assume!(ar[0] < 4);
  assume!(ar[1] < 5);
  assume!(ar[2] < 6);
  assume!(idx < 3);
  assert!(ar[idx] <= 5);
}
