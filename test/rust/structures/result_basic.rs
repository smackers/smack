#[macro_use]
mod smack;
use smack::*;

// @expect verified

struct NaN;

fn checked_addition(l: u8, r: u8) -> Result<u8, NaN> {
  let s = l + r;
  if s > 254 {
    Err(NaN) 
  } else {
    Ok(s)
  }
}

fn main() {
  let a = 1u8.nondet();
  let b = 2u8.nondet();
  assume!(a < 128);
  assume!(b < 127);
  let r = checked_addition(a, b);
  assert!(r.is_ok() && r.unwrap_or(255) < 255); 
}
