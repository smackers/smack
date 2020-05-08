#[macro_use]
mod smack;
use smack::*;

// @expect verified

fn safe_div(x: u64, y: u64) -> Option<u64> {
  if y != 0 {
    Some(x/y)
  }
  else {
    None
  }
}

fn main() {
  let x = 2u64.verifier_nondet();
  assume!(x > 0);
  let a = safe_div(2*x,x);
  match a {
    Some(x) => assert!(x == 2),
    None => assert!(false)
  };
  let b = safe_div(x,0);
  match b {
    Some(x) => assert!(false),
    None => assert!(true)
  };
}
