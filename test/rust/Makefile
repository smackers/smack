
incr_test.ll: incr.ll incr_test_rust.ll
	llvm-link incr.ll incr_test_rust.ll smack.ll -o incr_test.ll

incr.ll: incr.c
	clang -S -emit-llvm -c incr.c

incr_test_rust.ll: incr_test_rust.rs
	rustc --emit llvm-ir incr_test_rust.rs
