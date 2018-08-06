UNINTERPRETED_UNARY_OP = "function {0}.{1}(i: {1}) returns ({1});\n"
UNINTERPRETED_BINARY_OP = "function {0}.{1}(i1: {1}, i2: {1}) returns ({1});\n"
INLINE_BINARY_OP = "function {{:inline}} {0}.{2}(i1: {2}, i2: {2}) returns ({2}) {1}\n"
BUILTIN_BINARY_OP =  "function {{:builtin \"{0}\"}} {1}.{2}(i1: {2}, i2: {2}) returns ({2}) ;\n"
BVBUILTIN_UNARY_OP = "function {{:bvbuiltin \"{0}\"}} {1}.{2}(i: {2}) returns ({2}) ;\n"
BVBUILTIN_BINARY_OP = "function {{:bvbuiltin \"{0}\"}} {1}.{2}(i1: {2}, i2: {2}) returns ({2}) ;\n"
INLINE_BINARY_COMP = "function {{:inline}} {0}.{2}.bool(i1: {2}, i2: {2}) returns (bool) {1}"
BVBUILTIN_BINARY_COMP = "function {{:bvbuiltin \"{0}\"}} {1}.{2}.bool(i1: {2}, i2: {2}) returns (bool) ;"
INLINE_BINARY_PRED = "%s %s\n" % (INLINE_BINARY_COMP, "function {{:inline}} {0}.{2}(i1: {2}, i2: {2}) returns (i1) {{if {0}.{2}.bool(i1,i2) then 1 else 0}}")
INLINE_BINARY_BV_PRED = "%s %s\n" % (INLINE_BINARY_COMP, "function {{:inline}} {0}.{2}(i1: {2}, i2: {2}) returns (bv1) {{if {0}.{2}.bool(i1,i2) then 1bv1 else 0bv1}}")
SAFE_LOAD_OP = "function {{:inline}} $load.{1}(M: [ref] {1}, p: ref) returns ({1}) {0}\n"
SAFE_STORE_OP = "function {{:inline}} $store.{1}(M: [ref] {1}, p: ref, v: {1}) returns ([ref] {1}) {0}\n"
INLINE_BVBUILTIN_BINARY_SELECT = "function {{:inline}} {0}.{2}(i1: {2}, i2: {2}) returns ({2}) {{if {1}.{2}.bool(i1,i2) then i1 else i2}}\n"
INLINE_BVBUILTIN_BINARY_PRED = "%s %s\n" % (BVBUILTIN_BINARY_COMP, "function {{:inline}} {1}.{2}(i1: {2}, i2: {2}) returns (bv1) {{if {1}.{2}.bool(i1,i2) then 1bv1 else 0bv1}}")
INLINE_CONVERSION = "function {{:inline}} {0}.{2}.{3}(i: {2}) returns ({3}) {1}\n"
TRUNC_OP = "function {{:inline}} $trunc.{0}.{1}(i: {0}) returns ({1}) {{i}}\n"
TRUNC_BV_OP = "function {{:inline}} $trunc.{0}.{1}(i: {0}) returns ({1}) {{i[{2}:0]}}\n"

sizes = [1, 8, 16, 24, 32, 40, 48, 56, 64, 88, 96, 128]

def declare_each_type(prefix, func_decl, *args):
  bpl = ""
  for size in sizes:
    t = "%s%s" % (prefix, size)
    tmp = (args + (t,))
    bpl += func_decl.format(*tmp)
  return bpl

def declare_each_type_nested(prefix, func_decl, *args):
  bpl = ""
  for i in range(len(sizes)):
    for j in range(0,i):
      t1 = "%s%s" % (prefix, sizes[i])
      t2 = "%s%s" % (prefix, sizes[j])
      if "trunc" not in func_decl:
        t1, t2 = t2, t1
      tmp = args + (t1, t2, sizes[j])
      bpl += func_decl.format(*tmp)
  return bpl

def generate_prelude(args):
  with open(args.bpl_file, 'a+') as f:
    bpl = declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvadd", "$add")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvsub", "$sub")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvmul", "$mul")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvudiv", "$udiv")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvsdiv", "$sdiv")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvsmod", "$smod")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvsrem", "$srem")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvurem", "$urem")

    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_SELECT, "$min", "$slt")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_SELECT, "$max", "$sgt")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_SELECT, "$umin", "$ult")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_SELECT, "$umax", "$ugt")

    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvshl", "$shl")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvlshr", "$lshr")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvashr", "$ashr")
    bpl += declare_each_type("bv", BVBUILTIN_UNARY_OP, "bvnot", "$not")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvand", "$and")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvor", "$or")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvxor", "$xor")
    bpl += declare_each_type("bv", BVBUILTIN_BINARY_OP, "bvnand", "$nand")

    bpl += declare_each_type("bv", INLINE_BINARY_BV_PRED, "$eq", "{i1 == i2}")
    bpl += declare_each_type("bv", INLINE_BINARY_BV_PRED, "$ne", "{i1 != i2}")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvule", "$ule")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvult", "$ult")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvuge", "$uge")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvugt", "$ugt")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvsle", "$sle")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvslt", "$slt")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvsge", "$sge")
    bpl += declare_each_type("bv", INLINE_BVBUILTIN_BINARY_PRED, "bvsgt", "$sgt")

    bpl += declare_each_type_nested("bv", TRUNC_BV_OP)

    bpl += declare_each_type("i", INLINE_BINARY_OP, "$add", "{i1 + i2}")
    bpl += declare_each_type("i", INLINE_BINARY_OP, "$sub", "{i1 - i2}")
    bpl += declare_each_type("i", INLINE_BINARY_OP, "$mul", "{i1 * i2}")

    bpl += declare_each_type("i", BUILTIN_BINARY_OP, "div", "$sdiv")
    bpl += declare_each_type("i", BUILTIN_BINARY_OP, "mod", "$smod")
    bpl += declare_each_type("i", BUILTIN_BINARY_OP, "rem", "$srem")
    bpl += declare_each_type("i", BUILTIN_BINARY_OP, "div", "$udiv")
    bpl += declare_each_type("i", BUILTIN_BINARY_OP, "rem", "$urem")

    bpl += declare_each_type("i", INLINE_BINARY_OP, "$smin", "{$min(i1,i2)}")
    bpl += declare_each_type("i", INLINE_BINARY_OP, "$smax", "{$max(i1,i2)}")
    bpl += declare_each_type("i", INLINE_BINARY_OP, "$umin", "{$min(i1,i2)}")
    bpl += declare_each_type("i", INLINE_BINARY_OP, "$umax", "{$max(i1,i2)}")

    bpl += declare_each_type("i", UNINTERPRETED_BINARY_OP, "$shl")
    bpl += declare_each_type("i", UNINTERPRETED_BINARY_OP, "$lshr")
    bpl += declare_each_type("i", UNINTERPRETED_BINARY_OP, "$ashr")
    bpl += declare_each_type("i", UNINTERPRETED_UNARY_OP, "$not")
    bpl += declare_each_type("i", UNINTERPRETED_BINARY_OP, "$and")
    bpl += declare_each_type("i", UNINTERPRETED_BINARY_OP, "$or")
    bpl += declare_each_type("i", UNINTERPRETED_BINARY_OP, "$xor")
    bpl += declare_each_type("i", UNINTERPRETED_BINARY_OP, "$nand")

    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$eq", "{i1 == i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$ne", "{i1 != i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$ule", "{i1 <= i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$ult", "{i1 < i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$uge", "{i1 >= i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$ugt", "{i1 > i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$sle", "{i1 <= i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$slt", "{i1 < i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$sge", "{i1 >= i2}")
    bpl += declare_each_type("i", INLINE_BINARY_PRED, "$sgt", "{i1 > i2}")

    bpl += declare_each_type_nested("i", TRUNC_OP)

    bpl += declare_each_type_nested("i", INLINE_CONVERSION, "$zext", "{i}")
    bpl += declare_each_type_nested("i", INLINE_CONVERSION, "$sext", "{i}")

    bpl += declare_each_type("i", SAFE_LOAD_OP, "{ M[p] }")
    bpl += declare_each_type("bv", SAFE_LOAD_OP, "{ M[p] }")
    bpl += declare_each_type("i", SAFE_STORE_OP, "{ M[p := v] }")
    bpl += declare_each_type("bv", SAFE_STORE_OP, "{ M[p := v] }")

    f.write(bpl)
