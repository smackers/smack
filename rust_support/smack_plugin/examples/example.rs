#![feature(plugin, custom_attribute)]
#![plugin(extension)]

fn main() {
    let x = true;
    let y = false;
    assert!(x || y);
}

extern {
    fn __VERIFIER_assert(a: bool);
    fn __VERIFIER_assume(a: bool);
}
