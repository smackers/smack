#![crate_type = "staticlib"]

use std::alloc::Layout;

#[cfg(verifier = "smack")]
extern "C" {
    pub fn __VERIFIER_assert(x: i32);
    pub fn __VERIFIER_assume(x: i32);
    pub fn __VERIFIER_nondet_i8() -> i8;
    pub fn __VERIFIER_nondet_u8() -> u8;
    pub fn __VERIFIER_nondet_i16() -> i16;
    pub fn __VERIFIER_nondet_u16() -> u16;
    pub fn __VERIFIER_nondet_i32() -> i32;
    pub fn __VERIFIER_nondet_u32() -> u32;
    pub fn __VERIFIER_nondet_i64() -> i64;
    pub fn __VERIFIER_nondet_u64() -> u64;
    pub fn __VERIFIER_nondet_float() -> f32;
    pub fn __VERIFIER_nondet_double() -> f64;
    pub fn malloc(size: usize) -> *mut u8;
    pub fn __VERIFIER_memcpy(dest: *mut u8, src: *mut u8, count: usize) -> *mut u8;
    pub fn free(ptr: *mut u8);
    pub fn memset(ptr: *mut u8, ch: i32, count: usize);
    pub fn realloc(ptr: *mut u8, new_size: usize) -> *mut u8;
}

#[macro_export]
macro_rules! verifier_assert {
    ( $cond:expr ) => {
        unsafe {
            __VERIFIER_assert($cond as i32);
        };
    };
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! print {
  ($fmt:expr) => ();
  ($fmt:expr, $($arg:expr),*) => ( $($arg);* )
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! println {
  ($($arg:tt)*) => ( print!($($arg)*) )
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! eprint {
  ($($arg:tt)*) => ( print!($($arg)*) )
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! eprintln {
  ($($arg:tt)*) => ( print!($($arg)*) )
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! assert {
    ( $cond:expr ) => {
        verifier_assert!($cond);
    };
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! assert_eq {
    ( $lhs:expr, $rhs:expr ) => {
        smack::assert!($lhs == $rhs);
    };
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! assert_neq {
    ( $lhs:expr, $rhs:expr ) => {
        smack::assert!($lhs != $rhs);
    };
}

#[macro_export]
macro_rules! verifier_assume {
    ( $cond:expr ) => {
        #[cfg(verifier = "smack")]
        unsafe {
            __VERIFIER_assume($cond as i32);
        }

        #[cfg(not(verifier = "smack"))]
        ();
    };
}

#[macro_export]
macro_rules! assume {
    ( $cond:expr ) => {
        verifier_assume!($cond);
    };
}

#[macro_export]
macro_rules! verifier_nondet {
  ($e:expr) =>
    (
      #[cfg(verifier = "smack")]
      $e.verifier_nondet()

      #[cfg(not(verifier = "smack"))]
      $e
    )
}

pub trait VerifierNonDet {
    fn verifier_nondet(self) -> Self;
}

#[macro_export]
macro_rules! make_verifier_nondet {
    ($typ:ident, $nondet:ident) => {
        impl VerifierNonDet for $typ {
            #[cfg(verifier = "smack")]
            fn verifier_nondet(self) -> Self {
                unsafe { $nondet() as Self }
            }

            #[cfg(not(verifier = "smack"))]
            fn verifier_nondet(self) -> Self {
                self
            }
        }
    };
}

/* Instantiate nondet for all integer types. */
make_verifier_nondet!(i8, __VERIFIER_nondet_i8);
make_verifier_nondet!(u8, __VERIFIER_nondet_u8);
make_verifier_nondet!(i16, __VERIFIER_nondet_i16);
make_verifier_nondet!(u16, __VERIFIER_nondet_u16);
make_verifier_nondet!(i32, __VERIFIER_nondet_i32);
make_verifier_nondet!(u32, __VERIFIER_nondet_u32);
make_verifier_nondet!(i64, __VERIFIER_nondet_i64);
make_verifier_nondet!(u64, __VERIFIER_nondet_u64);
make_verifier_nondet!(isize, __VERIFIER_nondet_i64);
make_verifier_nondet!(usize, __VERIFIER_nondet_u64);
make_verifier_nondet!(f32, __VERIFIER_nondet_float);
make_verifier_nondet!(f64, __VERIFIER_nondet_double);

/* Rust memory function models. */
#[no_mangle]
pub unsafe fn __smack_rust_std_alloc(layout: Layout) -> *mut u8 {
    __smack_rust_prim_alloc(layout.size(), layout.align())
}

#[no_mangle]
pub unsafe fn __smack_rust_std_alloc_zeroed(layout: Layout) -> *mut u8 {
    __smack_rust_prim_alloc(layout.size(), layout.align())
}

#[no_mangle]
pub unsafe fn __smack_rust_std_dealloc(ptr: *mut u8, layout: Layout) {
    __smack_rust_prim_dealloc(ptr, layout.size(), layout.align())
}

#[no_mangle]
pub unsafe fn __smack_rust_std_realloc(ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
    __smack_rust_prim_realloc(ptr, layout.size(), layout.align(), new_size)
}

#[no_mangle]
pub unsafe fn __smack_rust_prim_alloc(size: usize, _align: usize) -> *mut u8 {
    // Currently ignores alignment
    malloc(size)
}

#[no_mangle]
pub unsafe fn __smack_rust_prim_alloc_zeroed(size: usize, _align: usize) -> *mut u8 {
    // Currently ignores alignment
    let result = malloc(size);
    memset(result, 0, size);
    result
}

#[no_mangle]
pub unsafe fn __smack_rust_prim_dealloc(ptr: *mut u8, _size: usize, _align: usize) {
    // Currently ignoring size and alignment
    free(ptr);
}

#[no_mangle]
pub unsafe fn __smack_rust_prim_realloc(
    ptr: *mut u8,
    _old_size: usize,
    _align: usize,
    new_size: usize,
) -> *mut u8 {
    // Needs proper implementation of realloc
    // Ignores size and alignment
    realloc(ptr, new_size)
}

#[cfg(not(verifier = "smack"))]
#[cfg(feature = "std")]
#[allow(dead_code)]
use std::Vec;
/* Vector class.
Based on https://doc.rust-lang.org/nomicon/vec-final.html */
#[cfg(verifier = "smack")]
#[allow(dead_code)]
fn sized_realloc(orig_ptr: *mut u8, orig_size: usize, new_size: usize) -> *mut u8 {
    unsafe {
        let result: *mut u8 = malloc(new_size);
        __VERIFIER_memcpy(result, orig_ptr, orig_size);
        result
    }
}

#[cfg(verifier = "smack")]
use std::mem;
#[cfg(verifier = "smack")]
use std::ops::{Deref, DerefMut};
#[cfg(verifier = "smack")]
use std::ptr::{self, null};

#[cfg(verifier = "smack")]
#[allow(dead_code)]
pub struct PhantomData<T> {
    _place_holder: *const T,
    _padding: u64,
}

#[cfg(verifier = "smack")]
impl<T> Default for PhantomData<T> {
    fn default() -> Self {
        PhantomData::<T> {
            _place_holder: ptr::null(),
            _padding: 0,
        }
    }
}

#[cfg(verifier = "smack")]
#[allow(dead_code)]
struct Unique<T: Sized> {
    //  _marker: PhantomData<T>,    // For the drop checker
    ptr: *const T, // *const for variance
    _marker: u64,
}

#[cfg(verifier = "smack")]
impl<T: Sized> Unique<T> {
    pub fn new(ptr: *mut T) -> Self {
        Unique {
            ptr: ptr,
            _marker: Default::default(),
        }
    }

    pub fn as_ptr(&self) -> *mut T {
        self.ptr as *mut T
    }
}

#[cfg(verifier = "smack")]
#[allow(dead_code)]
struct RawVec<T: Sized> {
    ptr: Unique<T>,
    cap: usize,
}

#[cfg(verifier = "smack")]
#[allow(dead_code)]
impl<T: Sized> RawVec<T> {
    fn new() -> Self {
        let elem_size = mem::size_of::<T>();
        let cap = 32;
        let ptr = unsafe { Unique::new(malloc(cap * elem_size) as *mut T) };
        RawVec { ptr: ptr, cap: cap }
    }

    fn new_with_capacity(cap: usize) -> Self {
        let elem_size = mem::size_of::<T>();
        let ptr = unsafe { Unique::new(malloc(cap * elem_size) as *mut T) };
        RawVec { ptr: ptr, cap: cap }
    }

    fn grow(&mut self) {
        let elem_size = mem::size_of::<T>();
        let new_cap = 2 * self.cap;
        let ptr = sized_realloc(
            self.ptr.as_ptr() as *mut _,
            self.cap * elem_size,
            new_cap * elem_size,
        );

        self.ptr = Unique::new(ptr as *mut _);
        self.cap = new_cap;
    }
}

#[cfg(verifier = "smack")]
impl<T: Sized> Drop for RawVec<T> {
    fn drop(&mut self) {
        unsafe { free(self.ptr.ptr as *mut _) };
    }
}

#[cfg(verifier = "smack")]
pub struct Vec<T: Sized> {
    buf: RawVec<T>,
    len: usize,
}

#[cfg(verifier = "smack")]
impl<T: Sized> Vec<T> {
    fn ptr(&self) -> *mut T {
        self.buf.ptr.as_ptr()
    }

    #[allow(dead_code)]
    fn cap(&self) -> usize {
        self.buf.cap
    }

    pub fn new() -> Self {
        Vec {
            buf: RawVec::new(),
            len: 0,
        }
    }

    #[allow(dead_code)]
    pub fn with_capacity(cap: usize) -> Self {
        Vec {
            buf: RawVec::new_with_capacity(cap),
            len: 0,
        }
    }

    #[allow(dead_code)]
    pub fn push(&mut self, elem: T) {
        if self.len == self.cap() {
            self.buf.grow();
        }

        unsafe {
            ptr::write(self.ptr().offset(self.len as isize), elem);
        }

        self.len += 1;
    }

    #[allow(dead_code)]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe { Some(ptr::read(self.ptr().offset(self.len as isize))) }
        }
    }

    #[allow(dead_code)]
    pub fn append(&mut self, other: &mut Vec<T>) {
        let mut i: usize = 0;
        let olen = other.len();
        let mut drain = Vec::new();
        while i < olen {
            drain.push(other.pop().unwrap());
            i += 1;
        }
        // Empty other
        i = 0;
        while i < olen {
            self.push(drain.pop().unwrap());
            i += 1;
        }
    }

    #[allow(dead_code)]
    pub fn insert(&mut self, index: usize, elem: T) {
        assert!(index <= self.len);
        if self.cap() == self.len {
            self.buf.grow();
        }

        unsafe {
            if index < self.len {
                ptr::copy(
                    self.ptr().offset(index as isize),
                    self.ptr().offset(index as isize + 1),
                    self.len - index,
                );
            }
            ptr::write(self.ptr().offset(index as isize), elem);
            self.len += 1;
        }
    }

    #[allow(dead_code)]
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len);
        unsafe {
            self.len -= 1;
            let result = ptr::read(self.ptr().offset(index as isize));
            ptr::copy(
                self.ptr().offset(index as isize + 1),
                self.ptr().offset(index as isize),
                self.len - index,
            );
            result
        }
    }

    #[allow(dead_code)]
    pub fn into_iter(self) -> IntoIter<T> {
        unsafe {
            let iter = RawValIter::new(&self);
            let buf = ptr::read(&self.buf);
            mem::forget(self);

            IntoIter {
                iter: iter,
                _buf: buf,
            }
        }
    }
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.len
    }
}

#[cfg(verifier = "smack")]
impl<T: Default> Default for Vec<T> {
    fn default() -> Self {
        Vec::new()
    }
}

#[cfg(verifier = "smack")]
impl<T: Sized> Drop for Vec<T> {
    fn drop(&mut self) {
        while let Some(_) = self.pop() {}
        // allocation is handled by RawVec
    }
}

#[cfg(verifier = "smack")]
impl<T: Sized> Deref for Vec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        unsafe { ::std::slice::from_raw_parts(self.buf.ptr.ptr, self.len) }
    }
}

#[cfg(verifier = "smack")]
impl<T: Sized> DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { ::std::slice::from_raw_parts_mut(self.buf.ptr.ptr as *mut T, self.len) }
    }
}

#[cfg(verifier = "smack")]
struct RawValIter<T> {
    start: *const T,
    end: *const T,
}

#[cfg(verifier = "smack")]
impl<T> RawValIter<T> {
    unsafe fn new(slice: &[T]) -> Self {
        RawValIter {
            start: slice.as_ptr(),
            end: if mem::size_of::<T>() == 0 {
                ((slice.as_ptr() as usize) + slice.len()) as *const _
            } else if slice.len() == 0 {
                slice.as_ptr()
            } else {
                slice.as_ptr().offset(slice.len() as isize)
            },
        }
    }
}

#[cfg(verifier = "smack")]
impl<T> Iterator for RawValIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                let result = ptr::read(self.start);
                self.start = if mem::size_of::<T>() == 0 {
                    (self.start as usize + 1) as *const _
                } else {
                    self.start.offset(1)
                };
                Some(result)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let elem_size = mem::size_of::<T>();
        let len =
            (self.end as usize - self.start as usize) / if elem_size == 0 { 1 } else { elem_size };
        (len, Some(len))
    }
}

#[cfg(verifier = "smack")]
impl<T> DoubleEndedIterator for RawValIter<T> {
    fn next_back(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                self.end = if mem::size_of::<T>() == 0 {
                    (self.end as usize - 1) as *const _
                } else {
                    self.end.offset(-1)
                };
                Some(ptr::read(self.end))
            }
        }
    }
}

#[cfg(verifier = "smack")]
pub struct IntoIter<T: Sized> {
    _buf: RawVec<T>, // we don't actually care about this. Just need it to live.
    iter: RawValIter<T>,
}

#[cfg(verifier = "smack")]
impl<T: Sized> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[cfg(verifier = "smack")]
impl<T: Sized> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back()
    }
}

#[cfg(verifier = "smack")]
impl<T: Sized> Drop for IntoIter<T> {
    fn drop(&mut self) {
        for _ in &mut *self {}
    }
}

#[cfg(verifier = "smack")]
#[macro_export]
macro_rules! vec {
  ( $val:expr ; $count:expr ) =>
    ({
      let mut result = Vec::new();
      let mut i = 0u64;
      while i < $count {
        result.push($val);
        i += 1;
      }
      result
    });
  ( $( $xs:expr ),* ) => {
    {
      let mut result = Vec::new();
      $(
        result.push($xs);
      )*
      result
    }
  };
}

#[cfg(verifier = "smack")]
#[allow(dead_code)]
pub struct Box<T: Sized> {
    ptr: Unique<T>,
}

#[cfg(verifier = "smack")]
#[allow(dead_code)]
impl<T: Sized> Box<T> {
    pub fn new(item: T) -> Box<T> {
        let elem_size = mem::size_of::<T>();
        let ptr = unsafe { Unique::new(malloc(elem_size) as *mut T) };
        unsafe { ptr::write(ptr.as_ptr().offset(0), item) };
        Box { ptr: ptr }
    }
}

#[cfg(verifier = "smack")]
#[allow(dead_code)]
impl<T: Sized> Deref for Box<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { mem::transmute::<*mut T, &T>(self.ptr.as_ptr()) }
    }
}
