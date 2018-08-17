import itertools

class Attribute:
  def __init__(self, name, arguments = []):
    self.name = name
    self.arguments = arguments

  def __str__(self):
    attribute_str = []
    attribute_str += '{:' + self.name
    for i, argument in enumerate(self.arguments):
      attribute_str += ' ' + str(argument)
      if i < len(self.arguments) - 1:
        attribute_str += ','
    attribute_str += '}'
    return ''.join(attribute_str)

class Argument:
  def __init__(self, name, type):
    self.name = name
    self.type = type

  def __str__(self):
    return self.name + ': ' + self.type

class Expr:
  def __init__(self, op):
    self.op = op

  def __str__(self):
    return 'i1 ' + self.op + ' i2'

class Function:
  def __init__(self, name, attributes = [], arguments = [], return_type = None, body = None):
    self.name = name
    self.attributes = attributes
    self.arguments = arguments
    self.return_type = return_type
    self.body = body

  def __str__(self):
    function_str = []
    function_str += 'function'
    for attribute in self.attributes:
      function_str += ' ' + str(attribute)
    function_str += ' ' + self.name + '('
    for i, argument in enumerate(self.arguments):
      function_str += str(argument)
      if i < len(self.arguments) - 1:
        function_str += ', '
    function_str += ')'
    if self.return_type is not None:
      function_str += ' returns (' + self.return_type + ')'
    if self.body is not None:
      function_str += ' {'+ self.body + '}'
    else:
      function_str += ';'
    function_str += '\n'
    return ''.join(function_str)

def int(width):
  return 'i' + str(width)

def bv(width):
  return 'bv' + str(width)

def mk_args(type, num):
  return [Argument('i' + str(i + 1), type) for i in range(num)]

def uninterpreted_unary_op(width, name):
  type = int(width)
  return Function(
    name = name + '.' + type,
    arguments = mk_args(type, 1),
    return_type = type,
  )

def uninterpreted_binary_op(width, name):
  type = int(width)
  return Function(
    name = name + '.' + type,
    arguments = mk_args(type, 2),
    return_type = type
  )

def inline_binary_op(width, name, body):
  type = int(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 2),
    return_type = type,
    body = body
  )

def builtin_binary_op(width, builtin_name, name):
  type = int(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('builtin', arguments = [builtin_name])],
    arguments = mk_args(type, 2),
    return_type = type
  )

def bvbuiltin_unary_op(width, builtin_name, name):
  type = bv(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('bvbuiltin', arguments = [builtin_name])],
    arguments = mk_args(type, 1),
    return_type = type
  )

def bvbuiltin_binary_op(width, builtin_name, name):
  type = bv(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('bvbuiltin', arguments = [builtin_name])],
    arguments = mk_args(type, 2),
    return_type = type
  )

def inline_binary_comp(width, name, body):
  type = int(width)
  return Function(
    name = name + '.' + type + '.bool',
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 2),
    return_type = 'bool',
    body = body
  )

def inline_binary_bv_comp(width, name, body):
  type = bv(width)
  return Function(
    name = name + '.' + type + '.bool',
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 2),
    return_type = 'bool',
    body = body
  )

def bvbuiltin_binary_comp(width, builtin_name, name):
  type = bv(width)
  return Function(
    name = name + '.' + type + '.bool',
    attributes = [Attribute('bvbuiltin', arguments = [builtin_name])],
    arguments = mk_args(type, 2),
    return_type = 'bool'
  )

def inline_binary_pred(width, name):
  type = int(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 2),
    return_type = 'i1',
    body = 'if ' + name + '.' + type + '.bool(i1, i2) then 1 else 0'
  )

def inline_binary_bv_pred(width, name):
  type = bv(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 2),
    return_type = 'bv1',
    body = 'if ' + name + '.' + type + '.bool(i1, i2) then 1bv1 else 0bv1'
  )

def safe_load_op(width, body):
  type = int(width)
  return Function(
    name = '$load.' + type,
    attributes = [Attribute('inline')],
    arguments = [Argument('M', '[ref] ' + type), Argument('p', 'ref')],
    return_type = type,
    body = body
  )

def safe_store_op(width, body):
  type = int(width)
  return Function(
    name = '$store.' + type,
    attributes = [Attribute('inline')],
    arguments = [Argument('M', '[ref] ' + type), Argument('p', 'ref'), Argument('v', type)],
    return_type = '[ref] ' + type,
    body = body
  )

def safe_load_bv_op(width, body):
  type = bv(width)
  return Function(
    name = '$load.' + type,
    attributes = [Attribute('inline')],
    arguments = [Argument('M', '[ref] ' + type), Argument('p', 'ref')],
    return_type = type,
    body = body
  )

def safe_store_bv_op(width, body):
  type = bv(width)
  return Function(
    name = '$store.' + type,
    attributes = [Attribute('inline')],
    arguments = [Argument('M', '[ref] ' + type), Argument('p', 'ref'), Argument('v', type)],
    return_type = '[ref] ' + type,
    body = body
  )

def inline_bvbuiltin_binary_select(width, name, name_2):
  type = bv(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 2),
    return_type = type,
    body = 'if ' + name_2 + '.' + type + '.bool(i1, i2) then i1 else i2'
  )

def inline_bvbuiltin_binary_pred(width, name):
  type = bv(width)
  return Function(
    name = name + '.' + type,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 2),
    return_type = 'bv1',
    body = 'if ' + name + '.' + type + '.bool(i1, i2) then 1bv1 else 0bv1'
  )

def inline_conversion(width, width_2, name, body):
  type = int(width)
  type_2 = int(width_2)
  return Function(
    name = name + '.' + type + '.' + type_2,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 1),
    return_type = type_2,
    body = body
  )

def trunc_op(width, width_2):
  type = int(width)
  type_2 = int(width_2)
  return Function(
    name = '$trunc.' + type + '.' + type_2,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 1),
    return_type = type_2,
    body = 'i1'
  )

def trunc_bv_op(width, width_2):
  type = bv(width)
  type_2 = bv(width_2)
  return Function(
    name = '$trunc.' + type + '.' + type_2,
    attributes = [Attribute('inline')],
    arguments = mk_args(type, 1),
    return_type = type_2,
    body = 'i1[' + str(width_2) + ':0]'
  )

sizes = [1, 8, 16, 24, 32, 40, 48, 56, 64, 80, 88, 96, 128]

binary_ops = ['add', 'sub', 'mul', 'sdiv', 'smod', 'srem', 'udiv', 'urem', 'shl', 'lshr', 'ashr', 'and', 'or', 'xor', 'nand']
comp_ops = ['ule', 'ult', 'uge', 'ugt', 'sle', 'slt', 'sge', 'sgt']
eq_ops = ['eq', 'ne']

binary_ops_body = ['+', '-', '*']
comp_ops_body = ['<=', '<', '>=', '>', '<=', '<', '>=', '>']
eq_ops_body = ['==', '!=']

def get_prelude():
  bpl = []

  for size in sizes:
    for i, op in enumerate(binary_ops):
      bpl.append(bvbuiltin_binary_op(width = size, builtin_name = '\"bv' + op + '\"', name = '$' + op))
      if 0 <= i <= 2:
        bpl.append(inline_binary_op(width = size, name = '$' + op, body = str(Expr(binary_ops_body[i]))))
      elif 3 <= i <= 7:
        bpl.append(builtin_binary_op(width = size, builtin_name = '\"' + op[1:] + '\"', name = '$' + op))
      else:
        bpl.append(uninterpreted_binary_op(width = size, name = '$' + op))

    for i, op in enumerate(comp_ops):
      bpl.append(bvbuiltin_binary_comp(width = size, builtin_name = '\"bv' + op + '\"', name = '$' + op))
      bpl.append(inline_bvbuiltin_binary_pred(width = size, name = '$' + op))
      bpl.append(inline_binary_comp(width = size, name = '$' + op, body = str(Expr(comp_ops_body[i]))))
      bpl.append(inline_binary_pred(width = size, name = '$' + op))

    for i, op in enumerate(eq_ops):
      bpl.append(inline_binary_bv_comp(width = size, name = '$' + op, body = str(Expr(eq_ops_body[i]))))
      bpl.append(inline_binary_bv_pred(width = size, name = '$' + op))
      bpl.append(inline_binary_comp(width = size, name = '$' + op, body = str(Expr(eq_ops_body[i]))))
      bpl.append(inline_binary_pred(width = size, name = '$' + op))

    bpl.append(inline_bvbuiltin_binary_select(width = size, name = '$min', name_2 = '$slt'))
    bpl.append(inline_bvbuiltin_binary_select(width = size, name = '$max', name_2 = '$sgt'))
    bpl.append(inline_bvbuiltin_binary_select(width = size, name = '$umin', name_2 = '$ult'))
    bpl.append(inline_bvbuiltin_binary_select(width = size, name = '$umax', name_2 = '$ugt'))

    bpl.append(inline_binary_op(width = size, name = '$smin', body = '$min(i1,i2)'))
    bpl.append(inline_binary_op(width = size, name = '$smax', body = '$max(i1,i2)'))
    bpl.append(inline_binary_op(width = size, name = '$umin', body = '$min(i1,i2)'))
    bpl.append(inline_binary_op(width = size, name = '$umax', body = '$max(i1,i2)'))

    bpl.append(bvbuiltin_unary_op(width = size, builtin_name = '\"bvnot\"', name = '$not'))
    bpl.append(uninterpreted_unary_op(width = size, name = '$not'))

    bpl.append(safe_load_op(width = size, body = 'M[p]'))
    bpl.append(safe_load_bv_op(width = size, body = 'M[p]'))
    bpl.append(safe_store_op(width = size, body = 'M[p := v]'))
    bpl.append(safe_store_bv_op(width = size, body = 'M[p := v]'))

  for size_pair in itertools.combinations(sizes, 2):
    bpl.append(trunc_bv_op(width = size_pair[1], width_2 = size_pair[0]))
    bpl.append(trunc_op(width = size_pair[1], width_2 = size_pair[0]))

    bpl.append(inline_conversion(width = size_pair[0], width_2 = size_pair[1], name = '$zext', body = 'i1'))
    bpl.append(inline_conversion(width = size_pair[0], width_2 = size_pair[1], name = '$sext', body = 'i1'))

  return ''.join([str(x) for x in bpl])

def append_prelude(args):
  f = open(args.bpl_file, 'a+')
  f.write(get_prelude())
