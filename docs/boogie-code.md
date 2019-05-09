## Inline Boogie Code


In order to pass custom Boogie code through SMACK's translation from C code,
SMACK interprets calls to the following procedures (declared in `smack.h`)
specially:

* `void __SMACK_code(const char *fmt, ...);`

* `void __SMACK_decl(const char *fmt, ...);`

* `void __SMACK_top_decl(const char *fmt, ...);`

SMACK translates the call `__SMACK_code("assume x == y;")` directly into the
Boogie statement `assume x == y;`. For variable declarations, SMACK translates
the call `__SMACK_decl("var x: int;")` into a declaration `var x: int;` in the
calling procedure, and the call `__SMACK_top_decl("var y: int;")` into a global
declaration `var y: int`. This last form can in fact be used for any kind of
global declaration, for instance,
````
__SMACK_top_decl("function f(int,int) returns (int);")
__SMACK_top_decl("axiom f(0,0) == 10;")
````
declares a Boogie function `f` constrained by the axiom `f(0,0) == 10`.

Given this functionality, it can also be useful to write custom Boogie code
which uses program values defined in the source-level C code. This is made
possible by interpreting the string passed as the first argument to
`__SMACK_code`, `__SMACK_decl`, and `__SMACK_top_decl` as a format string, in
which each occurrence of the `@` symbol is replaced by a subsequent argument.
For instance, consider the following implementations of `smack.h`
````
void assert(bool v) {
  __SMACK_code("assert @ != 0;", v);
}
void assume(bool v) {
  __SMACK_code("assume @ != 0;", v);
}
````
SMACK interprets the `@` symbol by inserting the value of the C variable `v`.
Since the arguments of variadic functions may be promoted, SMACK allows users
to append a format character to the `@` symbol as an indicator that the argument,
rather than its promoted form, should be used in the format string. The format
characters are given in the following table along with their corresponding C
types and their effective types within SMACK:

| Format | Original C Type | SMACK Type |
|--------|-----------------|------------|
| c      | char            | i8         |
| b      | signed char     | i8         |
| B      | unsigned char   | i8         |
| h      | signed short    | i16        |
| H      | unsigned short  | i16        |
| i      | signed int      | i32        |
| I      | unsigned int    | i32        |
| f      | float           | float      |

For example, without using such annotations, the definition of the `floorf`
function is:
```C
float floorf(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd($rmode, $round.bvfloat(RTN, dtf($rmode, @)));", ret, x);
   return ret;
 }
```
where the `ftd` and `dtf` functions are conversions between `float` and `double`
variables that are needed to deal with the promotion of the arguments.
Whereas a better definition using these annotations is:
```C
float floorf(float x) {
  float ret = __VERIFIER_nondet_float();
  __SMACK_code("@f := $round.bvfloat(RTN, @f);", ret, x);
   return ret;
 }
 ```

One application of this functionality which has been valuable to the authors of
SMACK is in encoding concurrency primitives into the generated Boogie code. The
following generates four procedure calls marked as _asynchronous_:
````
__SMACK_decl("var x: int;");
__SMACK_code("call {:async} @(@);", Push, 1);
__SMACK_code("call {:async} @(@);", Push, 2);
__SMACK_code("call {:async} x := @();", Pop);
__SMACK_code("call {:async} x := @();", Pop);
````
While the `{:async}` attributes have no intrinsic meaning in Boogie, they can be
used as directives for other tools that interpret concurrency primitives, such
as Corral.

