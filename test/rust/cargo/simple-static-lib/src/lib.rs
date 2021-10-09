#![crate_name = "toylib"]
#![crate_type = "staticlib"]
#[macro_use]
extern crate smack;
use smack::*;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

#[no_mangle]
pub extern "C" fn helloworld() {
    verifier_assert!(1 + 1 == 2);
}
