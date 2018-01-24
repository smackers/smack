#[cfg(verifier = "smack")]
extern {
  pub fn __VERIFIER_assert(x: i32);
  pub fn __VERIFIER_assume(x: i32);
  pub fn __VERIFIER_nondet_signed_char() -> i8;
  pub fn __VERIFIER_nondet_unsigned_char() -> u8;
  pub fn __VERIFIER_nondet_signed_short() -> i16;
  pub fn __VERIFIER_nondet_unsigned_short() -> u16;
  pub fn __VERIFIER_nondet_signed_int() -> i32;
  pub fn __VERIFIER_nondet_unsigned_int() -> u32;
  pub fn __VERIFIER_nondet_signed_long_long() -> i64;
  pub fn __VERIFIER_nondet_unsigned_long_long() -> u64;

}


#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! assert {
  ( $cond:expr ) =>
    (
      unsafe { __VERIFIER_assert($cond as i32); };
    )
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! assert_eq {
  ( $lhs:expr, $rhs:expr ) => ( assert!($lhs == $rhs); )
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! assert_neq {
  ( $lhs:expr, $rhs:expr ) => ( assert!($lhs != $rhs); )
}

#[macro_export]
macro_rules! assume {
  ( $cond:expr ) =>
    (
      #[cfg(verifier = "smack")]
      unsafe { __VERIFIER_assume($cond as i32); }

      #[cfg(not(verifier = "smack"))]
      ();
    )
}

#[macro_export]
macro_rules! nondet {
  ($e:expr) =>
    (
      #[cfg(verifier = "smack")]
      $e.nondet()

      #[cfg(not(verifier = "smack"))]
      $e
    )
}

pub trait NonDet {
  fn nondet(self) -> Self;
}

#[macro_export]
macro_rules! make_nondet {
  ($typ:ident, $nondet:ident) =>
    (
      impl NonDet for $typ {
        #[cfg(verifier = "smack")]
        fn nondet(self) -> Self {
          unsafe { $nondet() as Self }
        }

        #[cfg(not(verifier = "smack"))]
        fn nondet(self) -> Self {
          self
        }
      }
    );
}

/* Instantiate nondet for all integer types. */
make_nondet!(i8, __VERIFIER_nondet_signed_char);
make_nondet!(u8, __VERIFIER_nondet_unsigned_char);
make_nondet!(i16, __VERIFIER_nondet_signed_short);
make_nondet!(u16, __VERIFIER_nondet_unsigned_short);
make_nondet!(i32, __VERIFIER_nondet_signed_int);
make_nondet!(u32, __VERIFIER_nondet_unsigned_int);
make_nondet!(i64, __VERIFIER_nondet_signed_long_long);
make_nondet!(u64, __VERIFIER_nondet_unsigned_long_long);
