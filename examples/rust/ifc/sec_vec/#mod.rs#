pub mod sec_vec;

#[cfg(test)]
mod tests {
  use sec_vec::sec_vec::*;
  use std::marker::PhantomData;
  use verify::SVec;
  #[test]
  fn it_works() {

    let nd1 = 5;
    let nd2 = 6;
    let nd3 = 5;
    let nd4 = 6;

    let mut s = SecVec::new();
    let lsecret = svec![1,2,3 => nd1];
    let hsecret = svec![4,5,6 => nd2];

    println!("Adding secrets");
    s.push(lsecret, nd1);
    s.update(0, hsecret, nd2);

    println!("s: {:?}", s);

    println!("Reading secrets with low authority");
    match s.get(0, nd3) {
      None    => println!("Access forbidden"),
      Some(v) => check_label!(v,nd3)
    }

    println!("Reading secrets with high authority");
    match s.get(0, nd4) {
      None      => println!("Access forbidden"),
      Some(sec) => {
        check_label!(sec,nd4);
        println!("Secret value: {:?}", sec);
      }
    }
  }
}
