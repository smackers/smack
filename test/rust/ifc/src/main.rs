#![feature(unique)]
pub mod label {
    use std::cmp::max;
    pub type Label = u64;
    pub fn combine_labels(l1: Label, l2: Label) -> Label {
        max(l1,l2)
    }
}

/*extern {
    pub fn __VERIFIER_assume(cond: i32);
}

#[macro_export]
macro_rules! assume {
    ( $x : expr ) => {unsafe{__VERIFIER_assume($x as i32)}};
}*/

#[macro_use]
mod verify;
pub mod sec_vec;

use sec_vec::sec_vec::*;
use std::marker::PhantomData;
use verify::SVec;

fn main() {
    let mut nd1: u64;
    let mut nd2: u64;
    let mut nd3: u64;
    let mut nd4: u64;

    if cfg!(verifier = "smack") {
        nd1 = nondet_u64();
        nd2 = nondet_u64();
        nd3 = nondet_u64();
        nd4 = nondet_u64();
        assume!(nd1 > 4 && nd2 > 4);
        assume!(nd1 <= nd3 && nd2 == nd4);
        assume!(nd3 < nd2);
    }
    else {
        nd1 = 5;
        nd2 = 6;
        nd3 = 5;
        nd4 = 6;
    }
    let mut s = SecVec::new();
    let lsecret = svec![1,2,3 => nd1];
    let hsecret = svec![4,5,6 => nd2];
//    println!("Adding secrets");
    s.push(lsecret, nd1);
/*    match s.get(0, 10) {
        None => {
            let label2 = 17;
            assert!(false)},
        Some(v) => {
            let label = v.l;
            assert!(label == 5);
//            println!("{}", label);
        }
    };*/
    s.update(0, hsecret, nd2);
//    assert!(false);

//    assert!(s.get(0,10).unwrap().l == 6);


//    println!("s: {:?}", s);

//    println!("Reading secrets with low authority");
    match s.get(0, nd3) {
        None    => println!("Access forbidden"),
        Some(v) => {
            let label1 = v;
            check_label!(label1,nd3)
        }
    }

//    println!("Reading secrets with high authority");
    match s.get(0, nd4) {
        None      => println!("Access forbidden"),
        Some(sec) => {
            let label2 = sec;
            check_label!(label2,nd4);
            println!("Secret value: {:?}", sec);
        }
    }
}
