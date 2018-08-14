import itertools

class Attribute:
  def __init__(self, attribute, attribute_arg = None):
    self.attribute = attribute
    self.attribute_arg = attribute_arg

  def toStr(self):
    attribute_str = '{:' + self.attribute
    if self.attribute_arg is not None:
      attribute_str += ' \"' + self.attribute_arg + '\"'
    attribute_str += '}'
    return attribute_str

class Argument:
  def __init__(self, name, type):
    self.name = name
    self.type = type

  def toStr(self):
    return self.name + ': ' + self.type

class Function:
  def __init__(self, name, attributes = [], arguments = [], return_type = None, body = None):
    self.name = name
    self.attributes = attributes
    self.arguments = arguments
    self.return_type = return_type
    self.body = body

  def toStr(self):
    function_str = 'function'
    for attribute in self.attributes:
      function_str += ' ' + attribute.toStr()
    function_str += ' ' + self.name + '('
    for i, argument in enumerate(self.arguments):
      function_str += argument.toStr()
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
    return function_str


def int(bit_width):
  return 'i' + str(bit_width)

def bv(bit_width):
  return 'bv' + str(bit_width)

def uninterpreted_unary_op(bit_width, base_name):
  return Function(
    name = base_name + '.' + int(bit_width),
    arguments = [Argument(name = 'i', type = int(bit_width))],
    return_type = int(bit_width),
  )

def uninterpreted_binary_op(bit_width, base_name):
  return Function(
    name = base_name + '.' + int(bit_width),
    arguments = [Argument(name = 'i1', type = int(bit_width)), Argument(name = 'i2', type = int(bit_width))],
    return_type = int(bit_width)
  )

def inline_binary_op(bit_width, base_name, body):
  return Function(
    name = base_name + '.' + int(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i1', type = int(bit_width)), Argument(name = 'i2', type = int(bit_width))],
    return_type = int(bit_width),
    body = body
  )

def builtin_binary_op(bit_width, builtin_name, base_name):
  return Function(
    name = base_name + '.' + int(bit_width),
    attributes = [Attribute(attribute = 'builtin', attribute_arg = builtin_name)],
    arguments = [Argument(name = 'i1', type = int(bit_width)), Argument(name = 'i2', type = int(bit_width))],
    return_type = int(bit_width)
  )

def bvbuiltin_unary_op(bit_width, builtin_name, base_name):
  return Function(
    name = base_name + '.' + bv(bit_width),
    attributes = [Attribute(attribute = 'bvbuiltin', attribute_arg = builtin_name)],
    arguments = [Argument(name = 'i', type = bv(bit_width))],
    return_type = bv(bit_width)
  )

def bvbuiltin_binary_op(bit_width, builtin_name, base_name):
  return Function(
    name = base_name + '.' + bv(bit_width),
    attributes = [Attribute(attribute = 'bvbuiltin', attribute_arg = builtin_name)],
    arguments = [Argument(name = 'i1', type = bv(bit_width)), Argument(name = 'i2', type = bv(bit_width))],
    return_type = bv(bit_width)
  )

def inline_binary_comp(bit_width, base_name, body):
  return Function(
    name = base_name + '.' + int(bit_width) + '.bool',
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i1', type = int(bit_width)), Argument(name = 'i2', type = int(bit_width))],
    return_type = 'bool',
    body = body
  )

def inline_binary_bv_comp(bit_width, base_name, body):
  return Function(
    name = base_name + '.' + bv(bit_width) + '.bool',
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i1', type = bv(bit_width)), Argument(name = 'i2', type = bv(bit_width))],
    return_type = 'bool',
    body = body
  )

def bvbuiltin_binary_comp(bit_width, builtin_name, base_name):
  return Function(
    name = base_name + '.' + bv(bit_width) + '.bool',
    attributes = [Attribute(attribute = 'bvbuiltin', attribute_arg = builtin_name)],
    arguments = [Argument(name = 'i1', type = bv(bit_width)), Argument(name = 'i2', type = bv(bit_width))],
    return_type = 'bool'
  )

def inline_binary_pred(bit_width, base_name):
  return Function(
    name = base_name + '.' + int(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i1', type = int(bit_width)), Argument(name = 'i2', type = int(bit_width))],
    return_type = 'i1',
    body = 'if ' + base_name + '.' + int(bit_width) + '.bool(i1, i2) then 1 else 0'
  )

def inline_binary_bv_pred(bit_width, base_name):
  return Function(
    name = base_name + '.' + bv(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i1', type = bv(bit_width)), Argument(name = 'i2', type = bv(bit_width))],
    return_type = 'bv1',
    body = 'if ' + base_name + '.' + bv(bit_width) + '.bool(i1, i2) then 1bv1 else 0bv1'
  )

def safe_load_op(bit_width, body):
  return Function(
    name = '$load.' + int(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'M', type = '[ref] ' + int(bit_width)), Argument(name = 'p', type = 'ref')],
    return_type = int(bit_width),
    body = body
  )

def safe_store_op(bit_width, body):
  return Function(
    name = '$store.' + int(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'M', type = '[ref] ' + int(bit_width)), Argument(name = 'p', type = 'ref'), Argument(name = 'v', type = int(bit_width))],
    return_type = '[ref]' + int(bit_width),
    body = body
  )

def safe_load_bv_op(bit_width, body):
  return Function(
    name = '$load.' + bv(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'M', type = '[ref] ' + bv(bit_width)), Argument(name = 'p', type = 'ref')],
    return_type = bv(bit_width),
    body = body
  )

def safe_store_bv_op(bit_width, body):
  return Function(
    name = '$store.' + bv(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'M', type = '[ref] ' + bv(bit_width)), Argument(name = 'p', type = 'ref'), Argument(name = 'v', type = bv(bit_width))],
    return_type = '[ref]' + bv(bit_width),
    body = body
  )

def inline_bvbuiltin_binary_select(bit_width, base_name, base_name_2):
  return Function(
    name = base_name + '.' + bv(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i1', type = bv(bit_width)), Argument(name = 'i2', type = bv(bit_width))],
    return_type = bv(bit_width),
    body = 'if ' + base_name_2 + '.' + bv(bit_width) + '.bool(i1, i2) then i1 else i2'
  )

def inline_bvbuiltin_binary_pred(bit_width, base_name):
  return Function(
    name = base_name + '.' + bv(bit_width),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i1', type = bv(bit_width)), Argument(name = 'i2', type = bv(bit_width))],
    return_type = 'bv1',
    body = 'if ' + base_name + '.' + bv(bit_width) + '.bool(i1, i2) then 1bv1 else 0bv1'
  )

def inline_conversion(bit_width, bit_width_2, base_name, body):
  return Function(
    name = base_name + '.' + int(bit_width) + '.' + int(bit_width_2),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i', type = int(bit_width))],
    return_type = int(bit_width_2),
    body = body
  )

def trunc_op(bit_width, bit_width_2):
  return Function(
    name = '$trunc.' + int(bit_width) + '.' + int(bit_width_2),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i', type = int(bit_width))],
    return_type = int(bit_width_2),
    body = 'i'
  )

def trunc_bv_op(bit_width, bit_width_2):
  return Function(
    name = '$trunc.' + bv(bit_width) + '.' + bv(bit_width_2),
    attributes = [Attribute(attribute = 'inline')],
    arguments = [Argument(name = 'i', type = bv(bit_width))],
    return_type = bv(bit_width_2),
    body = 'i[' + str(bit_width_2) + ':0]'
  )

sizes = [1, 8, 16, 24, 32, 40, 48, 56, 64, 88, 96, 128]

binary_ops = ['add', 'sub', 'mul', 'sdiv', 'smod', 'srem', 'udiv', 'urem', 'shl', 'lshr', 'ashr', 'and', 'or', 'xor', 'nand']
comp_ops = ['ule', 'ult', 'uge', 'ugt', 'sle', 'slt', 'sge', 'sgt']
eq_ops = ['eq', 'ne']

binary_ops_body = ['i1 + i2', 'i1 - i2', 'i1 * i2']
comp_ops_body = ['i1 <= i2', 'i1 < i2', 'i1 >= i2', 'i1 > i2', 'i1 <= i2', 'i1 < i2', 'i1 >= i2', 'i1 > i2']
eq_ops_body = ['i1 == i2', 'i1 != i2']

def get_prelude():
  bpl = []
  for i, op in enumerate(binary_ops):
    bpl += map(lambda size: bvbuiltin_binary_op(bit_width = size, builtin_name = 'bv' + op, base_name = '$' + op).toStr(), sizes)
    if 0 <= i <= 2:
      bpl += map(lambda size: inline_binary_op(bit_width = size, base_name = '$' + op, body = binary_ops_body[i]).toStr(), sizes)
    elif 3 <= i <= 7:
      bpl += map(lambda size: builtin_binary_op(bit_width = size, builtin_name = op[1:], base_name = '$' + op).toStr(), sizes)
    else:
      bpl += map(lambda size: uninterpreted_binary_op(bit_width = size, base_name = '$' + op).toStr(), sizes)

  for i, op in enumerate(comp_ops):
    bpl += map(lambda size: bvbuiltin_binary_comp(bit_width = size, builtin_name = 'bv' + op, base_name = '$' + op).toStr(), sizes)
    bpl += map(lambda size: inline_bvbuiltin_binary_pred(bit_width = size, base_name = '$' + op).toStr(), sizes)
    bpl += map(lambda size: inline_binary_comp(bit_width = size, base_name = '$' + op, body = comp_ops_body[i]).toStr(), sizes)
    bpl += map(lambda size: inline_binary_pred(bit_width = size, base_name = '$' + op).toStr(), sizes)

  for i, op in enumerate(eq_ops):
    bpl += map(lambda size: inline_binary_bv_comp(bit_width = size, base_name = '$' + op, body = eq_ops_body[i]).toStr(), sizes)
    bpl += map(lambda size: inline_binary_bv_pred(bit_width = size, base_name = '$' + op).toStr(), sizes)
    bpl += map(lambda size: inline_binary_comp(bit_width = size, base_name = '$' + op, body = eq_ops_body[i]).toStr(), sizes)
    bpl += map(lambda size: inline_binary_pred(bit_width = size, base_name = '$' + op).toStr(), sizes)

  bpl += map(lambda size: inline_bvbuiltin_binary_select(bit_width = size, base_name = '$min', base_name_2 = '$slt').toStr(), sizes)
  bpl += map(lambda size: inline_bvbuiltin_binary_select(bit_width = size, base_name = '$max', base_name_2 = '$sgt').toStr(), sizes)
  bpl += map(lambda size: inline_bvbuiltin_binary_select(bit_width = size, base_name = '$umin', base_name_2 = '$ult').toStr(), sizes)
  bpl += map(lambda size: inline_bvbuiltin_binary_select(bit_width = size, base_name = '$umax', base_name_2 = '$ugt').toStr(), sizes)

  bpl += map(lambda size: inline_binary_op(bit_width = size, base_name = '$smin', body = '$min(i1,i2)').toStr(), sizes)
  bpl += map(lambda size: inline_binary_op(bit_width = size, base_name = '$smax', body = '$max(i1,i2)').toStr(), sizes)
  bpl += map(lambda size: inline_binary_op(bit_width = size, base_name = '$umin', body = '$min(i1,i2)').toStr(), sizes)
  bpl += map(lambda size: inline_binary_op(bit_width = size, base_name = '$umax', body = '$max(i1,i2)').toStr(), sizes)

  bpl += map(lambda size: bvbuiltin_unary_op(bit_width = size, builtin_name = 'bvnot', base_name = '$not').toStr(), sizes)
  bpl += map(lambda size: uninterpreted_unary_op(bit_width = size, base_name = '$not').toStr(), sizes)

  bpl += map(lambda size_pair: trunc_bv_op(bit_width = size_pair[1], bit_width_2 = size_pair[0]).toStr(), itertools.combinations(sizes, 2))
  bpl += map(lambda size_pair: trunc_op(bit_width = size_pair[1], bit_width_2 = size_pair[0]).toStr(), itertools.combinations(sizes, 2))

  bpl += map(lambda size_pair: inline_conversion(bit_width = size_pair[0], bit_width_2 = size_pair[1], base_name = '$zext', body = 'i').toStr(), itertools.combinations(sizes, 2))
  bpl += map(lambda size_pair: inline_conversion(bit_width = size_pair[0], bit_width_2 = size_pair[1], base_name = '$sext', body = 'i').toStr(), itertools.combinations(sizes, 2))

  bpl += map(lambda size: safe_load_op(bit_width = size, body = 'M[p]').toStr(), sizes)
  bpl += map(lambda size: safe_load_bv_op(bit_width = size, body = 'M[p]').toStr(), sizes)
  bpl += map(lambda size: safe_store_op(bit_width = size, body = 'M[p := v]').toStr(), sizes)
  bpl += map(lambda size: safe_store_bv_op(bit_width = size, body = 'M[p := v]').toStr(), sizes)

  return ''.join(bpl)

def append_prelude(args):
  f = open(args.bpl_file, 'a+')
  f.write(get_prelude())
