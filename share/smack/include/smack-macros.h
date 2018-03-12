//
// This file is distributed under the MIT License. See LICENSE for details.
//

// shamelessly stole these macro definitions from
// https://github.com/pfultz2/Cloak/wiki/C-Preprocessor-tricks,-tips,-and-idioms
#define PRIMITIVE_CAT(a, ...) a ## __VA_ARGS__

#define DEC(x) PRIMITIVE_CAT(DEC_, x)
#define DEC_0   0
#define DEC_1   0
#define DEC_8   1
#define DEC_16  8
#define DEC_24  16
#define DEC_32  24
#define DEC_40  32
#define DEC_48  40
#define DEC_56  48
#define DEC_64  56
#define DEC_88  64
#define DEC_96  88
#define DEC_128 96

#define INC(x) PRIMITIVE_CAT(INC_, x)
#define INC_1   8
#define INC_8   16
#define INC_16  24
#define INC_24  32
#define INC_32  40
#define INC_40  48
#define INC_48  56
#define INC_56  64
#define INC_64  88
#define INC_88  96
#define INC_96  128
#define INC_128 0
#define INC_0 0

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

#define REPEAT(count, macro, M, args...) \
    WHEN(count) \
    ( \
        OBSTRUCT(REPEAT_INDIRECT) () \
        ( \
            DEC(count), macro, M, args \
        ) \
        OBSTRUCT(macro) \
        ( \
            count, M, args \
        ) \
    )
#define REPEAT_INDIRECT() REPEAT

#define INT_TYPE(bw) i ## bw
#define BV_TYPE(bw) bv ## bw

#define APPLY_MACRO_ON_BV(bw,M,args...) \
  D(xstr(M(BV_TYPE(bw),args)));

#define APPLY_MACRO_ON_INT(bw,M,args...) \
  D(xstr(M(INT_TYPE(bw),args)));

#define DECLARE_EACH_BV_TYPE(M,args...) \
  EVAL(REPEAT(128,APPLY_MACRO_ON_BV,M,args))

#define DECLARE_EACH_INT_TYPE(M,args...) \
  EVAL(REPEAT(128,APPLY_MACRO_ON_INT,M,args))

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

#define DECLARE_BV_TRUNC(bw1, bw2) \
  DECLARE(INLINE_CONVERSION,BV_TYPE(bw1),BV_TYPE(bw2),$trunc,{i[bw2:0]});

#define DECLARE_BV_TRUNCS \
  EVAL(COMBINE(128,96,DEC,DECLARE_BV_TRUNC))

#define DECLARE_INT_TRUNC(bw1, bw2) \
  DECLARE(INLINE_CONVERSION,INT_TYPE(bw1),INT_TYPE(bw2),$trunc,{i});

#define DECLARE_INT_TRUNCS \
  EVAL(COMBINE(128,96,DEC,DECLARE_INT_TRUNC))

#define DECLARE_INT_ZEXT(bw1, bw2) \
  DECLARE(INLINE_CONVERSION,INT_TYPE(bw1),INT_TYPE(bw2),$zext,{i});

#define DECLARE_INT_ZEXTS \
  EVAL(COMBINE(1,8,INC,DECLARE_INT_ZEXT))

#define DECLARE_INT_SEXT(bw1, bw2) \
  DECLARE(INLINE_CONVERSION,INT_TYPE(bw1),INT_TYPE(bw2),$sext,{i});

#define DECLARE_INT_SEXTS \
  EVAL(COMBINE(1,8,INC,DECLARE_INT_SEXT))
