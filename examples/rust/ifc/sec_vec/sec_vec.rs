use std::vec::Vec;

use label::*;
use verify::SVec;

type Secret = SVec<u32>;


#[derive(Debug)]
pub struct Labeled<V> {
  pub label: Label,
  val: V
}

#[derive(Debug)]
pub struct SecVec {
  m: Vec<Labeled<Secret>>
}

impl SecVec {
  pub fn new() -> SecVec {
    SecVec {
      m: Vec::new()
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

  pub fn get(&self, k:usize, l:Label) -> Option<&Secret>/*l*/ {
    match self.m.get(k) {
      Some(v) => if v.label > /* < */ l {
        None
      } else {
        Some(&v.val)/*l*/
      },
      None    => None
    }
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
