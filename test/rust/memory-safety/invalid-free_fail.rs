use std::alloc::{alloc, Layout, System};
use std::ptr;

pub struct File {
    buf: Box<u8>,
}


pub unsafe fn fdopen() -> * mut File {
    let layout = Layout::new::<File>();
    let f = alloc(layout) as * mut File;
    // Rust will run drop on *f when it is assigned to, causing an invalid
    // free on the member buf.
    *f = File{buf: Box::new(0)};
    //ptr::write(f, File{buf: vec!{0u8; 100}});
    f
}

fn main() {
    let x = unsafe { fdopen() };
}
