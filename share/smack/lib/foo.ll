define { i32, i1 } @smackreplacement.llvm.smul.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }* %0, i32 0, i32 0
  %2 = mul i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %3 = getelementptr { i32, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smackreplacement.llvm.umul.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }* %0, i32 0, i32 0
  %2 = mul i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %3 = getelementptr { i32, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smackreplacement.llvm.sadd.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }* %0, i32 0, i32 0
  %2 = add i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %3 = getelementptr { i32, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }* %0
  ret { i32, i1 } %4
}

define { i32, i1 } @smackreplacement.llvm.uadd.with.overflow.i32(i32 %bar.coerce0, i32 %bar.coerce1) #0 {
entry:
  %0 = alloca { i32, i1 }
  %1 = getelementptr { i32, i1 }* %0, i32 0, i32 0
  %2 = add i32 %bar.coerce0, %bar.coerce1 
  store i32 %2, i32* %1
  %3 = getelementptr { i32, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i32, i1 }* %0
  ret { i32, i1 } %4
}

define { i64, i1 } @smackreplacement.llvm.smul.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1 }* %0, i32 0, i32 0
  %2 = mul i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %3 = getelementptr { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smackreplacement.llvm.umul.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1 }* %0, i32 0, i32 0
  %2 = mul i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %3 = getelementptr { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smackreplacement.llvm.sadd.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1 }* %0, i32 0, i32 0
  %2 = add i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %3 = getelementptr { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1 }* %0
  ret { i64, i1 } %4
}

define { i64, i1 } @smackreplacement.llvm.uadd.with.overflow.i64(i64 %bar.coerce0, i64 %bar.coerce1) #0 {
entry:
  %0 = alloca { i64, i1 }
  %1 = getelementptr { i64, i1 }* %0, i32 0, i32 0
  %2 = add i64 %bar.coerce0, %bar.coerce1 
  store i64 %2, i64* %1
  %3 = getelementptr { i64, i1 }* %0, i32 0, i32 1
  store i1 0, i1* %3
  %4 = load { i64, i1 }* %0
  ret { i64, i1 } %4
}




