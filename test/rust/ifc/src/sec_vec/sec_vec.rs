//#![feature(alloc)]
//#![feature(heap_api)]
//#![feature(no_std)]
#![feature(unique)]
use std::marker::PhantomData;
use std::ptr::{Unique, self};
use std::mem;

use label::*;
use verify::SVec;
use std::fmt;

pub type Secret = SVec<u64>;


#[derive(Clone)]
pub struct Labeled<V> {
    pub label: Label,
    val: V
}


pub struct Arr {
    pub len: usize,
    _0: Labeled<Secret>,
    _1: Labeled<Secret>,
    _2: Labeled<Secret>,
    _3: Labeled<Secret>,
}

impl fmt::Debug for Arr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Arr {{ len: {}; {} }}",
               self.len, self._0.label)
    }
}

impl Arr {
    fn new() -> Arr {
        Arr{len: 0,
            _0: Labeled{label: 0,
                        val: Secret{l: 0, phantom: PhantomData}},
            _1: Labeled{label: 0,
                        val: Secret{l: 0, phantom: PhantomData}},
            _2: Labeled{label: 0,
                        val: Secret{l: 0, phantom: PhantomData}},
            _3: Labeled{label: 0,
                        val: Secret{l: 0, phantom: PhantomData}}}

    }
    
    fn get<'a>(&'a self, ind: usize) -> Option<&'a Labeled<Secret>> {
        if ind >= self.len {None}
        else{
            Some(match ind {
                0 => &self._0,
                1 => &self._1,
                2 => &self._2,
                3 => &self._3,
                _ => unreachable!()
            })
        }
    }
    
    fn get_mut<'a>(&'a mut self, ind: usize) -> Option<&'a mut Labeled<Secret>> {
        if ind >= self.len {None}
        else{
            Some(match ind {
                0 => &mut self._0,
                1 => &mut self._1,
                2 => &mut self._2,
                3 => &mut self._3,
                _ => unreachable!()
            })
        }
    }
    
    fn set(&mut self, ind: usize, val: Labeled<Secret>) {
        if ind >= self.len {panic!("")}
        match ind {
            0 => self._0 = val,
            1 => self._1 = val,
            2 => self._2 = val,
            3 => self._3 = val,
            _ => unreachable!()
        }
    }
    
    fn push(&mut self, val: Labeled<Secret>) {
//        println!("Pushing vector");
        match self.len {
            0 => self._0 = val,
            1 => self._1 = val,
            2 => self._2 = val,
            3 => self._3 = val,
            _ => panic!()
        }
        self.len += 1;
    }
    fn append(&mut self, other: &mut Arr) {
        for i in 0..other.len {
            self.push((*(other.get(i).unwrap())).clone());
        }
    }
    pub fn is_null(&self) -> bool {
        false
    }
}

// End MB addition
// End arr

#[macro_export]
macro_rules! arr {
    ( $( $x:expr ),* ) => {
            {
                let mut temp_vec = Arr::new();
                assert!(temp_vec.data as usize != 0);
                $(
                    temp_vec.push($x);
                )*
                    temp_vec
            }
    };
} 


#[derive(Debug)]
pub struct SecVec {
    pub m: Arr
}

impl SecVec {
    pub fn new() -> SecVec {
        SecVec {
            m: Arr::new()
        }
    }
    pub fn push(&mut self, v: Secret, l:Label) {
	self.m.push(Labeled{label:l, val:v})
    }

    pub fn update(&mut self, k: usize, mut v: Secret /*l*/, l:Label) {
        match self.m.get_mut(k) {
            Some(old) => {
		old.val.append(&mut v);
		old.label = combine_labels(l, old.label);
            },
            None    => {}
        }
    }

    pub fn get<'a>(&'a self, k:usize, l:Label) -> Option<&'a Secret>/*l*/ {
        let result = 
            match self.m.get(k) {
                Some(v) => if v.label > l {
                    None
                } else {
                    Some(&v.val)/*l*/
                },
                None    => None
            };
        result
    }

//    pub fn take(&mut self, k:u32, l:Label) -> Option<Secret>/*l*/ {
//        match self.m.remove(&k) {
//            Some(v) => {
//                let Labeled{label, val} = v;
//                if label > l {
//                    None
//                } else {
//                    Some(val)/*l*/
//                }
//            },
//            None    => None
//        }
//    }
}

/*
#[derive(Debug)]
enum Document<V> {
    Unclassified(V),
    Classified(V)
}


use self::Document::*;

pub struct StaticSecHashMap {
    m: HashMap<u32,Document<Secret>>
}

impl StaticSecHashMap {
    pub fn new() -> StaticSecHashMap {
        StaticSecHashMap {
            m: HashMap::new()
        }
    }

    pub fn update_u(&mut self, k: u32, mut v: Secret) {
        match self.m.remove(&k) {
            Some(Classified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Classified(val));
            },
            Some(Unclassified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Unclassified(val));
            },
            None => {self.m.insert(k, Unclassified(v));}
        }
    }

    pub fn update_c(&mut self, k: u32, mut v: Secret) {
        match self.m.remove(&k) {
            Some(Classified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Classified(val));
            },
            Some(Unclassified(mut val)) => {
                val.append(&mut v);
                self.m.insert(k, Classified(val));
            },
            None    => {self.m.insert(k, Classified(v));}
        }
    }

    pub fn get_u(&self, k:u32) -> Option<&Secret> {
        match self.m.get(&k) {
            Some(&Unclassified(ref v)) => Some(&v),
            _                          => None
        }
    }

    pub fn get_c(&self, k:u32) -> Option<&Secret> {
        match self.m.get(&k) {
            Some(&Unclassified(ref v)) => Some(&v),
            Some(&Classified(ref v))   => Some(&v),
            _                          => None
        }
    }
}*/
