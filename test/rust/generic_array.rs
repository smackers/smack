#![feature(alloc)]
extern crate alloc;

use alloc::heap::deallocate;
use alloc::heap::reallocate;
use alloc::heap::allocate;
use std::mem::size_of;
use std::clone::Clone;

struct Arr<T: Clone> {
    len: usize,
    sz: usize,
    data: *mut T,
}

impl<T: Clone> Arr<T> {
    fn new(sz: usize) -> Arr<T> {
        if sz == 0 {panic!("")};
        let dt = unsafe{allocate(sz*size_of::<T>() as usize, 4)} as *mut T;
        /*for i in 0..sz {
            unsafe{(*(dt.offset(i as isize))) = 0};
        }*/
        Arr{len: 0, sz: sz, data: dt}
    }

    fn in_bytes(&self, ind: usize) -> isize { ((ind*(size_of::<T>())) as isize) }

    fn get(&self, ind: usize) -> T {
        if ind >= self.len {panic!("{} {}", ind, self.len)}
        //return unsafe{&(*(self.data.offset(ind as isize)))}
        unsafe{let ref result = *self.data.offset(ind as isize);
        return Clone::clone(result);
        }
    }

    fn set(&mut self, ind: usize, val: T) {
        if ind >= self.len {panic!("")}
        unsafe{(*(self.data.offset(ind as isize))) = val};
    }

    fn push(&mut self, val: T) {
        if self.len >= self.sz {
            // Double the length of the array
            println!("Reallocating");
            self.data = unsafe{reallocate(self.data as *mut u8, self.in_bytes(self.sz) as usize, self.in_bytes(2*self.sz) as usize,4)} as *mut T;
            if self.data as usize == 0 {panic!{"Failed to reallocate"}};
            self.sz *= 2;
        }
        unsafe{(*(self.data.offset(self.len as isize))) = val};
        self.len += 1;
    }
}

impl<T: Clone> Drop for Arr<T> {
    fn drop(&mut self) {
        // Check null pointer
//        assert!((self.data as isize) != 0);
        println!("Dropping");
        if (self.data as isize) == 0 {
            panic!("Null pointer while dropping array!");
        }
        unsafe{deallocate((self.data as *mut u8), self.in_bytes(self.sz) as usize, 4)};
        self.data = 0 as *mut T;
    }
}


fn main()
{
    let mut sz = 8;
    let mut arr32:Arr<i32> = Arr::new(sz);
    arr32.push(0);
    arr32.push(1);
    arr32.push(2);
    arr32.push(3);
    arr32.push(3);
    assert!(arr32.get(0) == 0 );
    assert!(arr32.get(1) == 1 );
    assert!(arr32.get(2) == 2 );
    assert!(arr32.get(3) == 3 );
}
