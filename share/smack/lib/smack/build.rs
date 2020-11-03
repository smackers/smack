// build.rs

fn main() {
    cc::Build::new()
        .file("src/smack-rust.c")
        .define("CARGO_BUILD", None)
        .include("src")
        .compiler("clang")
        .compile("libsmack.a");
    println!("cargo:rerun-if-changed=src/smack-rust.c");
}

