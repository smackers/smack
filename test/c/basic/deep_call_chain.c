#include "smack.h"
#include <assert.h>

// @expect verified

// Pointer-passing call chains deeper than the old fixed 100-pass cap must
// still translate: the Phase-3 bound now scales with the number of
// functions. Callers are defined before callees so call-site mapping
// propagates one level per pass (the adverse order).

static void f1(int *p);
static void f2(int *p);
static void f3(int *p);
static void f4(int *p);
static void f5(int *p);
static void f6(int *p);
static void f7(int *p);
static void f8(int *p);
static void f9(int *p);
static void f10(int *p);
static void f11(int *p);
static void f12(int *p);
static void f13(int *p);
static void f14(int *p);
static void f15(int *p);
static void f16(int *p);
static void f17(int *p);
static void f18(int *p);
static void f19(int *p);
static void f20(int *p);
static void f21(int *p);
static void f22(int *p);
static void f23(int *p);
static void f24(int *p);
static void f25(int *p);
static void f26(int *p);
static void f27(int *p);
static void f28(int *p);
static void f29(int *p);
static void f30(int *p);
static void f31(int *p);
static void f32(int *p);
static void f33(int *p);
static void f34(int *p);
static void f35(int *p);
static void f36(int *p);
static void f37(int *p);
static void f38(int *p);
static void f39(int *p);
static void f40(int *p);
static void f41(int *p);
static void f42(int *p);
static void f43(int *p);
static void f44(int *p);
static void f45(int *p);
static void f46(int *p);
static void f47(int *p);
static void f48(int *p);
static void f49(int *p);
static void f50(int *p);
static void f51(int *p);
static void f52(int *p);
static void f53(int *p);
static void f54(int *p);
static void f55(int *p);
static void f56(int *p);
static void f57(int *p);
static void f58(int *p);
static void f59(int *p);
static void f60(int *p);
static void f61(int *p);
static void f62(int *p);
static void f63(int *p);
static void f64(int *p);
static void f65(int *p);
static void f66(int *p);
static void f67(int *p);
static void f68(int *p);
static void f69(int *p);
static void f70(int *p);
static void f71(int *p);
static void f72(int *p);
static void f73(int *p);
static void f74(int *p);
static void f75(int *p);
static void f76(int *p);
static void f77(int *p);
static void f78(int *p);
static void f79(int *p);
static void f80(int *p);
static void f81(int *p);
static void f82(int *p);
static void f83(int *p);
static void f84(int *p);
static void f85(int *p);
static void f86(int *p);
static void f87(int *p);
static void f88(int *p);
static void f89(int *p);
static void f90(int *p);
static void f91(int *p);
static void f92(int *p);
static void f93(int *p);
static void f94(int *p);
static void f95(int *p);
static void f96(int *p);
static void f97(int *p);
static void f98(int *p);
static void f99(int *p);
static void f100(int *p);
static void f101(int *p);
static void f102(int *p);
static void f103(int *p);
static void f104(int *p);
static void f105(int *p);
static void f106(int *p);
static void f107(int *p);
static void f108(int *p);
static void f109(int *p);
static void f110(int *p);
static void f111(int *p);
static void f112(int *p);
static void f113(int *p);
static void f114(int *p);
static void f115(int *p);
static void f116(int *p);
static void f117(int *p);
static void f118(int *p);
static void f119(int *p);
static void f120(int *p) { *p = 42; }
static void f1(int *p) { f2(p); }
static void f2(int *p) { f3(p); }
static void f3(int *p) { f4(p); }
static void f4(int *p) { f5(p); }
static void f5(int *p) { f6(p); }
static void f6(int *p) { f7(p); }
static void f7(int *p) { f8(p); }
static void f8(int *p) { f9(p); }
static void f9(int *p) { f10(p); }
static void f10(int *p) { f11(p); }
static void f11(int *p) { f12(p); }
static void f12(int *p) { f13(p); }
static void f13(int *p) { f14(p); }
static void f14(int *p) { f15(p); }
static void f15(int *p) { f16(p); }
static void f16(int *p) { f17(p); }
static void f17(int *p) { f18(p); }
static void f18(int *p) { f19(p); }
static void f19(int *p) { f20(p); }
static void f20(int *p) { f21(p); }
static void f21(int *p) { f22(p); }
static void f22(int *p) { f23(p); }
static void f23(int *p) { f24(p); }
static void f24(int *p) { f25(p); }
static void f25(int *p) { f26(p); }
static void f26(int *p) { f27(p); }
static void f27(int *p) { f28(p); }
static void f28(int *p) { f29(p); }
static void f29(int *p) { f30(p); }
static void f30(int *p) { f31(p); }
static void f31(int *p) { f32(p); }
static void f32(int *p) { f33(p); }
static void f33(int *p) { f34(p); }
static void f34(int *p) { f35(p); }
static void f35(int *p) { f36(p); }
static void f36(int *p) { f37(p); }
static void f37(int *p) { f38(p); }
static void f38(int *p) { f39(p); }
static void f39(int *p) { f40(p); }
static void f40(int *p) { f41(p); }
static void f41(int *p) { f42(p); }
static void f42(int *p) { f43(p); }
static void f43(int *p) { f44(p); }
static void f44(int *p) { f45(p); }
static void f45(int *p) { f46(p); }
static void f46(int *p) { f47(p); }
static void f47(int *p) { f48(p); }
static void f48(int *p) { f49(p); }
static void f49(int *p) { f50(p); }
static void f50(int *p) { f51(p); }
static void f51(int *p) { f52(p); }
static void f52(int *p) { f53(p); }
static void f53(int *p) { f54(p); }
static void f54(int *p) { f55(p); }
static void f55(int *p) { f56(p); }
static void f56(int *p) { f57(p); }
static void f57(int *p) { f58(p); }
static void f58(int *p) { f59(p); }
static void f59(int *p) { f60(p); }
static void f60(int *p) { f61(p); }
static void f61(int *p) { f62(p); }
static void f62(int *p) { f63(p); }
static void f63(int *p) { f64(p); }
static void f64(int *p) { f65(p); }
static void f65(int *p) { f66(p); }
static void f66(int *p) { f67(p); }
static void f67(int *p) { f68(p); }
static void f68(int *p) { f69(p); }
static void f69(int *p) { f70(p); }
static void f70(int *p) { f71(p); }
static void f71(int *p) { f72(p); }
static void f72(int *p) { f73(p); }
static void f73(int *p) { f74(p); }
static void f74(int *p) { f75(p); }
static void f75(int *p) { f76(p); }
static void f76(int *p) { f77(p); }
static void f77(int *p) { f78(p); }
static void f78(int *p) { f79(p); }
static void f79(int *p) { f80(p); }
static void f80(int *p) { f81(p); }
static void f81(int *p) { f82(p); }
static void f82(int *p) { f83(p); }
static void f83(int *p) { f84(p); }
static void f84(int *p) { f85(p); }
static void f85(int *p) { f86(p); }
static void f86(int *p) { f87(p); }
static void f87(int *p) { f88(p); }
static void f88(int *p) { f89(p); }
static void f89(int *p) { f90(p); }
static void f90(int *p) { f91(p); }
static void f91(int *p) { f92(p); }
static void f92(int *p) { f93(p); }
static void f93(int *p) { f94(p); }
static void f94(int *p) { f95(p); }
static void f95(int *p) { f96(p); }
static void f96(int *p) { f97(p); }
static void f97(int *p) { f98(p); }
static void f98(int *p) { f99(p); }
static void f99(int *p) { f100(p); }
static void f100(int *p) { f101(p); }
static void f101(int *p) { f102(p); }
static void f102(int *p) { f103(p); }
static void f103(int *p) { f104(p); }
static void f104(int *p) { f105(p); }
static void f105(int *p) { f106(p); }
static void f106(int *p) { f107(p); }
static void f107(int *p) { f108(p); }
static void f108(int *p) { f109(p); }
static void f109(int *p) { f110(p); }
static void f110(int *p) { f111(p); }
static void f111(int *p) { f112(p); }
static void f112(int *p) { f113(p); }
static void f113(int *p) { f114(p); }
static void f114(int *p) { f115(p); }
static void f115(int *p) { f116(p); }
static void f116(int *p) { f117(p); }
static void f117(int *p) { f118(p); }
static void f118(int *p) { f119(p); }
static void f119(int *p) { f120(p); }

int main(void) {
  int x = 0;
  f1(&x);
  assert(x == 42);
  return 0;
}
