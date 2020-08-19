// build.rs

fn main() {
    cc::Build::new()
        .file("src/smack.c")
        .define("RUST_EXEC", None)
        .include("src")
        .compiler("clang")
        .compile("libsmack.a");
    println!("cargo:rerun-if-changed=src/smack.c");
}

