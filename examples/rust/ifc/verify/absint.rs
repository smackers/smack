pub use std::marker::PhantomData;
use label::*;

#[derive(Debug)]
pub struct SVec<T> {
    pub l: Label,
    pub phantom: PhantomData<T>
}

impl<T> SVec<T> {
    pub fn append(&mut self, other: &mut Self) {
        self.l = combine_labels(self.l, other.l);
    }
}

#[macro_export]
macro_rules! svec {
    ( $elem : expr ; $n : expr => $l : expr) => {SVec{l: $l, phantom: PhantomData}};
    ( $ ( $x : expr ) , * => $l : expr) => {SVec{l:$l, phantom: PhantomData}};
    ( $ ( $x : expr , ) * => $l : expr) => {SVec{l:$l, phantom: PhantomData}};
}

#[macro_export]
macro_rules! check_label {
    ( $x : expr, $l : expr ) => {assert!($x.l == $l)};
}
