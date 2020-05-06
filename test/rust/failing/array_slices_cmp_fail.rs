#[macro_use]
mod smack;
use smack::*;

// see: https://github.com/smackers/smack/issues/575 
// @expect error

fn main() {
  let ar = [2u8.nondet(), 3u8.nondet(), 4u8.nondet(), 5u8.nondet()];
  assume!(ar[0] == ar[2]);
  assume!(ar[1] == ar[3]);
  let fh = &ar[0..2];
  let sh = &ar[2..4];
  assert!(fh != sh);
}
