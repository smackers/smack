class Function:
  def __init__(self, attr, attr_arg, name, arg_types, ret_type, body):
    self.attr = attr
    self.attr_arg = attr_arg
    self.name = name
    self.arg_types = arg_types
    self.ret_type = ret_type
    self.vars = map(lambda i : 'i' + str(i), range(len(arg_types)))
    self.body = body

  def toStr(self):
    func_str = 'function '
    if self.attr is not None:
      func_str += '{:' + self.attr
      if self.attr_arg is not None:
        func_str += ' \"' + self.attr_arg + '\"'
      func_str += '} '
    func_str += self.name + '('
    for i in range(len(self.arg_types)):
      func_str += 'i' + str(i + 1) + ': ' + self.arg_types[i]
      if i < len(self.arg_types) - 1:
        func_str += ', '
    func_str += ') returns (' + self.ret_type + ')'
    if self.body is not None:
      func_str += ' {'+ self.body + '}'
    else:
      func_str += ';'
    func_str += '\n'
    return func_str

mk_int = lambda bitwidth: 'i' + str(bitwidth)
mk_bv = lambda bitwidth: 'bv' + str(bitwidth)

UNINTERPRETED_UNARY_OP = lambda bitwidth, name: Function(None,
  None,
  '.'.join([name, mk_int(bitwidth)]),
  [mk_int(bitwidth)],
  mk_int(bitwidth),
  None)
UNINTERPRETED_BINARY_OP = lambda bitwidth, name: Function(None,
  None,
  '.'.join([name, mk_int(bitwidth)]),
  [mk_int(bitwidth), mk_int(bitwidth)],
  mk_int(bitwidth),
  None)
INLINE_BINARY_OP = lambda bitwidth, name, body: Function('inline',
  None,
  '.'.join([name, mk_int(bitwidth)]),
  [mk_int(bitwidth), mk_int(bitwidth)],
  mk_int(bitwidth),
  body)
BUILTIN_BINARY_OP = lambda bitwidth, builtin_name, name: Function('builtin',
  builtin_name,
  '.'.join([name, mk_int(bitwidth)]),
  [mk_int(bitwidth), mk_int(bitwidth)],
  mk_int(bitwidth),
  None)
BVBUILTIN_UNARY_OP = lambda bitwidth, builtin_name, name: Function('bvbuiltin',
  builtin_name,
  '.'.join([name, mk_bv(bitwidth)]),
  [mk_bv(bitwidth)],
  mk_bv(bitwidth),
  None)
BVBUILTIN_BINARY_OP = lambda bitwidth, builtin_name, name: Function('bvbuiltin',
  builtin_name,
  '.'.join([name, mk_bv(bitwidth)]),
  [mk_bv(bitwidth), mk_bv(bitwidth)],
  mk_bv(bitwidth),
  None)
INLINE_BINARY_COMP = lambda bitwidth, name, body: Function('inline',
  None,
  '.'.join([name, mk_int(bitwidth), 'bool']),
  [mk_int(bitwidth), mk_int(bitwidth)],
  'bool',
  body)
INLINE_BINARY_BV_COMP = lambda bitwidth, name, body: Function('inline',
  None,
  '.'.join([name, mk_bv(bitwidth), 'bool']),
  [mk_bv(bitwidth), mk_bv(bitwidth)],
  'bool',
  body)
BVBUILTIN_BINARY_COMP = lambda bitwidth, builtin_name, name: Function('bvbuiltin',
  builtin_name,
  '.'.join([name, mk_bv(bitwidth), 'bool']),
  [mk_bv(bitwidth), mk_bv(bitwidth)],
  'bool',
  None)
INLINE_BINARY_PRED = lambda bitwidth, name: Function('inline',
  None,
  '.'.join([name, mk_int(bitwidth)]),
  [mk_int(bitwidth), mk_int(bitwidth)],
  'i1',
  'if ' + '.'.join([name, mk_int(bitwidth), 'bool']) + '(i1, i2) then 1 else 0')
INLINE_BINARY_BV_PRED = lambda bitwidth, name: Function('inline',
  None,
  '.'.join([name, mk_bv(bitwidth)]),
  [mk_bv(bitwidth), mk_bv(bitwidth)],
  'bv1',
  'if ' + '.'.join([name, mk_bv(bitwidth), 'bool']) + '(i1, i2) then 1bv1 else 0bv1')
SAFE_LOAD_OP = lambda bitwidth, body: Function('inline',
  None,
  '.'.join(['$load', mk_int(bitwidth)]),
  ['[ref] ' + mk_int(bitwidth), 'ref'],
  mk_int(bitwidth),
  body)
SAFE_STORE_OP = lambda bitwidth, body: Function('inline',
  None,
  '.'.join(['$store', mk_int(bitwidth)]),
  ['[ref] ' + mk_int(bitwidth), 'ref', mk_int(bitwidth)],
  '[ref] ' + mk_int(bitwidth),
  body)
SAFE_LOAD_BV_OP = lambda bitwidth, body: Function('inline',
  None,
  '.'.join(['$load', mk_bv(bitwidth)]),
  ['[ref] ' + mk_bv(bitwidth), 'ref'],
  mk_bv(bitwidth),
  body)
SAFE_STORE_BV_OP = lambda bitwidth, body: Function('inline',
  None,
  '.'.join(['$store', mk_bv(bitwidth)]),
  ['[ref] ' + mk_bv(bitwidth), 'ref', mk_bv(bitwidth)],
  '[ref] ' + mk_bv(bitwidth),
  body)
INLINE_BVBUILTIN_BINARY_SELECT = lambda bitwidth, name, name2: Function('inline',
  None,
  '.'.join([name, mk_bv(bitwidth)]),
  [mk_bv(bitwidth), mk_bv(bitwidth)],
  mk_bv(bitwidth),
  'if ' + '.'.join([name2, mk_bv(bitwidth), 'bool']) + '(i1, i2) then i1 else i2')
INLINE_BVBUILTIN_BINARY_PRED = lambda bitwidth, name: Function('inline',
  None,
  '.'.join([name, mk_bv(bitwidth)]),
  [mk_bv(bitwidth), mk_bv(bitwidth)],
  'bv1',
  'if ' + '.'.join([name, mk_bv(bitwidth), 'bool']) + '(i1,i2) then 1bv1 else 0bv1')
INLINE_CONVERSION = lambda bitwidth2, bitwidth1, name, body: Function('inline',
  None,
  '.'.join([name, mk_int(bitwidth1), mk_int(bitwidth2)]),
  [mk_int(bitwidth1)],
  mk_int(bitwidth2),
  body)
TRUNC_OP = lambda bitwidth1, bitwidth2: Function('inline',
  None,
  '.'.join(['$trunc', mk_int(bitwidth1), mk_int(bitwidth2)]),
  [mk_int(bitwidth1)],
  mk_int(bitwidth2),
  'i1')
TRUNC_BV_OP = lambda bitwidth1, bitwidth2: Function('inline',
  None,
  '.'.join(['$trunc', mk_bv(bitwidth1), mk_bv(bitwidth2)]),
  [mk_bv(bitwidth1)],
  mk_bv(bitwidth2),
  'i1[' + str(bitwidth2) + ':0]')

sizes = [1, 8, 16, 24, 32, 40, 48, 56, 64, 88, 96, 128]
binary_ops = ['add', 'sub', 'mul', 'sdiv', 'smod', 'srem', 'udiv', 'urem', 'shl', 'lshr', 'ashr', 'and', 'or', 'xor', 'nand']
binary_ops_body = ['i1 + i2', 'i1 - i2', 'i1 * i2']
comp_ops = ['ule', 'ult', 'uge', 'ugt', 'sle', 'slt', 'sge', 'sgt']
comp_ops_body = ['i1 <= i2', 'i1 < i2', 'i1 >= i2', 'i1 > i2', 'i1 <= i2', 'i1 < i2', 'i1 >= i2', 'i1 > i2']
eq_ops = ['eq', 'ne']
eq_ops_body = ['i1 == i2', 'i1 != i2']

def declare_each_type(func_decl, *args):
  bpl = ''
  for i in sizes:
    tmp = ((i,) + args)
    bpl += func_decl(*tmp).toStr()
  return bpl

def declare_each_type_nested(func_decl, *args):
  bpl = ''
  for i in range(len(sizes)):
    for j in range(0,i):
      tmp = (sizes[i], sizes[j]) + args
      bpl += func_decl(*tmp).toStr()
  return bpl

def generate_prelude(args):
  bpl = ''
  for i in range(len(binary_ops)):
    op_name = '$' + binary_ops[i]
    bpl += declare_each_type(BVBUILTIN_BINARY_OP, 'bv' + binary_ops[i], op_name)
    if 0 <= i <= 2:
      bpl += declare_each_type(INLINE_BINARY_OP, op_name, binary_ops_body[i])
    elif 3 <= i <= 7:
      bpl += declare_each_type(BUILTIN_BINARY_OP, binary_ops[i][1:], op_name)
    else:
      bpl += declare_each_type(UNINTERPRETED_BINARY_OP, op_name)

  for i in range(len(comp_ops)):
    op_name = '$' + comp_ops[i]
    bpl += declare_each_type(BVBUILTIN_BINARY_COMP, 'bv' + comp_ops[i], op_name)
    bpl += declare_each_type(INLINE_BVBUILTIN_BINARY_PRED, op_name)
    bpl += declare_each_type(INLINE_BINARY_COMP, op_name, comp_ops_body[i])
    bpl += declare_each_type(INLINE_BINARY_PRED, op_name)

  for i in range(len(eq_ops)):
    op_name = '$' + eq_ops[i]
    bpl += declare_each_type(INLINE_BINARY_BV_COMP, op_name, eq_ops_body[i])
    bpl += declare_each_type(INLINE_BINARY_BV_PRED, op_name)
    bpl += declare_each_type(INLINE_BINARY_COMP, op_name, eq_ops_body[i])
    bpl += declare_each_type(INLINE_BINARY_PRED, op_name)

  bpl += declare_each_type(INLINE_BVBUILTIN_BINARY_SELECT, '$min', '$slt')
  bpl += declare_each_type(INLINE_BVBUILTIN_BINARY_SELECT, '$max', '$sgt')
  bpl += declare_each_type(INLINE_BVBUILTIN_BINARY_SELECT, '$umin', '$ult')
  bpl += declare_each_type(INLINE_BVBUILTIN_BINARY_SELECT, '$umax', '$ugt')

  bpl += declare_each_type(INLINE_BINARY_OP, '$smin', '$min(i1,i2)')
  bpl += declare_each_type(INLINE_BINARY_OP, '$smax', '$max(i1,i2)')
  bpl += declare_each_type(INLINE_BINARY_OP, '$umin', '$min(i1,i2)')
  bpl += declare_each_type(INLINE_BINARY_OP, '$umax', '$max(i1,i2)')

  bpl += declare_each_type(BVBUILTIN_UNARY_OP, 'bvnot', '$not')
  bpl += declare_each_type(UNINTERPRETED_UNARY_OP, '$not')

  bpl += declare_each_type_nested(TRUNC_BV_OP)
  bpl += declare_each_type_nested(TRUNC_OP)

  bpl += declare_each_type_nested(INLINE_CONVERSION, '$zext', 'i1')
  bpl += declare_each_type_nested(INLINE_CONVERSION, '$sext', 'i1')

  bpl += declare_each_type(SAFE_LOAD_OP, 'i1[i2]')
  bpl += declare_each_type(SAFE_LOAD_BV_OP, 'i1[i2]')
  bpl += declare_each_type(SAFE_STORE_OP, 'i1[i2 := i3]')
  bpl += declare_each_type(SAFE_STORE_BV_OP, 'i1[i2 := i3]')

  f = open(args.bpl_file, 'a+')
  f.write(bpl)
