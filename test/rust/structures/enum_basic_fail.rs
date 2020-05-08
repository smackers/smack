#[macro_use]
mod smack;
use smack::*;

// @expect error

enum Heist {
  GetAway,
  LeaveWitnesses(u8),
}

fn main() {
  let w = 1u8.nondet();
  let h = if w == 0 {
    Heist::GetAway
  } else {
    Heist::LeaveWitnesses(w)
  };
  match h {
    Heist::GetAway => (),
    Heist::LeaveWitnesses(_) => assert!(0),
  };
}
