#[macro_use]
extern crate smack;
use smack::*;

// @expect verified

enum Heist {
    GetAway,
    LeaveWitnesses(u8),
}

fn main() {
    let w = 1u8.verifier_nondet();
    smack::assume!(w == 0);
    let h = if w == 0 {
        Heist::GetAway
    } else {
        Heist::LeaveWitnesses(w)
    };
    match h {
        Heist::GetAway => (),
        Heist::LeaveWitnesses(_) => smack::assert!(0),
    };
}
