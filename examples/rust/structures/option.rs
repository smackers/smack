#[macro_use]
mod smack;
use smack::*;

fn safe_div(x: u64, y: u64) -> Option<u64> {
  if y != 0 {
    Some(x/y)
  }
  else {
    None
  }
}

fn main() {
  let a = safe_div(4,2);
  match a {
    Some(x) => assert!(x == 2),
    None => assert!(false)
  };
  let b = safe_div(4,0);
  match b {
    Some(x) => assert!(false),
    None => assert!(true)
  };
}
