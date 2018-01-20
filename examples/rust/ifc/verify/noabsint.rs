use std::vec::Vec;

pub type SVec<T> = Vec<T>;

#[macro_export]
macro_rules! svec {
    ( $elem : expr ; $n : expr => $l : expr) => {vec!($elem; $n)};
    ( $ ( $x : expr ) , * => $l : expr) => {vec!($($x),*)};
    ( $ ( $x : expr , ) * => $l : expr) => {vec!($($x,)*)};
}

#[macro_export]
macro_rules! check_label {
    ( $x : expr, $l : expr ) => {assert!(true)};
}
