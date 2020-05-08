#[macro_use]
mod smack;
use smack::*;

// @expect error

fn checked_addition(l: u8, r: u8) -> Option<u8> {
  let s = l + r;
  if s > 254 {
    None
  } else {
    Some(s)
  }
}

fn main() {
  let a = 1u8.nondet();
  let b = 2u8.nondet();
  assume!(a < 128);
  assume!(b < 127);
  let r = checked_addition(a, b);
  assert!(r.is_none()); 
}
