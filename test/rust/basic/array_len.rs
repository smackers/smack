#[macro_use]
mod smack;
use smack::*;

// @expect verified

fn main() {
  let ar = [2u8.nondet(), 3u8.nondet(), 4u8.nondet()];
  let idx = 5usize.nondet();
  assume!(idx < 3);
  let fh = &ar[..idx];
  let sh = &ar[idx..];
  assert!(fh.len() + sh.len() == ar.len());
}
