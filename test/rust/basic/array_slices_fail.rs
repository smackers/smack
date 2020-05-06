#[macro_use]
mod smack;
use smack::*;

// @expect error

fn main() {
  let mut ar = [2u8.nondet(), 3u8.nondet(), 4u8.nondet()];
  let idx = 1usize.nondet();
  assume!(ar[0] < 4);
  assume!(ar[1] < 5);
  assume!(ar[2] < 6);
  assume!(idx < 3 && idx > 1);
  let slice = &mut ar[..idx];
  slice[1] += 1;
  assert!(slice.is_empty() || slice[1] < 5);
}
