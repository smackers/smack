//
// This file is distributed under the MIT License. See LICENSE for details.
//

// shamelessly stole these macro definitions from
// https://github.com/pfultz2/Cloak/wiki/C-Preprocessor-tricks,-tips,-and-idioms
#define PRIMITIVE_CAT(a, ...) a ## __VA_ARGS__

#define DEC_BYTE(x) PRIMITIVE_CAT(DEC_BYTE_, x)
#define DEC_BYTE_0 0
#define DEC_BYTE_8 0
#define DEC_BYTE_16 8
#define DEC_BYTE_24 16
#define DEC_BYTE_32 24
#define DEC_BYTE_40 32
#define DEC_BYTE_48 40
#define DEC_BYTE_56 48
#define DEC_BYTE_64 56
#define DEC_BYTE_72 64
#define DEC_BYTE_80 72
#define DEC_BYTE_88 80
#define DEC_BYTE_96 88
#define DEC_BYTE_104 96
#define DEC_BYTE_112 104
#define DEC_BYTE_120 112
#define DEC_BYTE_128 120

#define EVAL(...)  EVAL1(EVAL1(EVAL1(__VA_ARGS__)))
#define EVAL1(...) EVAL2(EVAL2(EVAL2(__VA_ARGS__)))
#define EVAL2(...) EVAL3(EVAL3(EVAL3(__VA_ARGS__)))
#define EVAL3(...) EVAL4(EVAL4(EVAL4(__VA_ARGS__)))
#define EVAL4(...) __VA_ARGS__

#define IIF(c) PRIMITIVE_CAT(IIF_, c)
#define IIF_0(t, ...) __VA_ARGS__
#define IIF_1(t, ...) t

#define CHECK_N(x, n, ...) n
#define CHECK(...) CHECK_N(__VA_ARGS__, 0,)
#define PROBE(x) x, 1,

#define NOT(x) CHECK(PRIMITIVE_CAT(NOT_, x))
#define NOT_0 PROBE(~)

#define COMPL(b) PRIMITIVE_CAT(COMPL_, b)
#define COMPL_0 1
#define COMPL_1 0

#define BOOL(x) COMPL(NOT(x))
#define IF(c) IIF(BOOL(c))

#define EAT(...)
#define EXPAND(...) __VA_ARGS__
#define WHEN(c) IF(c)(EXPAND, EAT)

#define EMPTY()
#define DEFER(id) id EMPTY()
#define OBSTRUCT(...) __VA_ARGS__ DEFER(EMPTY)()

#define BITAND(x) PRIMITIVE_CAT(BITAND_, x)
#define BITAND_0(y) 0
#define BITAND_1(y) y

#define BV_TYPE(bw) PRIMITIVE_CAT(bv, bw)

#define COMBINE(count1, count2, direction, macro) \
    WHEN(BITAND(BOOL(count1))(BOOL(count2))) \
    ( \
          OBSTRUCT(COMBINE_INDIRECT) () \
          ( \
              count1, direction(count2), direction, macro \
          ) \
          OBSTRUCT(macro) \
          ( \
              count1, count2 \
          ) \
     ) \
     WHEN(BITAND(NOT(BOOL(count2)))(BOOL(count1))) \
     ( \
          OBSTRUCT(COMBINE_INDIRECT) () \
          ( \
            direction(count1), direction(direction(count1)), direction, macro \
          ) \
     )
#define COMBINE_INDIRECT() COMBINE

#define UNSAFE_LOAD_OP(type,name,body) \
  function {:inline} name.type(M: [ref] bv8, p: ref) returns (type) body

#define UNSAFE_STORE_OP(type,name,body) \
  function {:inline} name.type(M: [ref] bv8, p: ref, v: type) returns ([ref] bv8) body

#define DECLARE_UNSAFE_LOAD(bw1,bw2) \
  WHEN(BOOL(DEC_BYTE(bw2))) \
  ( \
    DECLARE(UNSAFE_LOAD_OP, BV_TYPE(bw2), $load.bytes, {$load.bytes.BV_TYPE(DEC_BYTE(bw2))(M, $add.ref(p, $1.ref)) ++ $load.bytes.bv8(M,p)}); \
  )

#define DECLARE_UNSAFE_STORE(bw1,bw2) \
  WHEN(BOOL(DEC_BYTE(bw2))) \
  ( \
    DECLARE(UNSAFE_STORE_OP, BV_TYPE(bw2), $store.bytes, {$store.bytes.BV_TYPE(DEC_BYTE(bw2))(M, $add.ref(p, $1.ref), v[bw2:8])[p := v[8:0]]}); \
  )

#define DECLARE_UNSAFE_LOADS \
  EVAL(COMBINE(8,128,DEC_BYTE,DECLARE_UNSAFE_LOAD))

#define DECLARE_UNSAFE_STORES \
  EVAL(COMBINE(8,128,DEC_BYTE,DECLARE_UNSAFE_STORE))
