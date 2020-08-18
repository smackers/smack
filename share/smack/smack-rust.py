#! /usr/bin/env python3

import sys
import os
import subprocess

# rustc --help -v
#
# Usage: rustc [OPTIONS] INPUT
#
# Options:
#     -h, --help          Display this message
#         --cfg SPEC      Configure the compilation environment
#     -L [KIND=]PATH      Add a directory to the library search path. The
#                         optional KIND can be one of dependency, crate, native,
#                         framework, or all (the default).
#     -l [KIND=]NAME      Link the generated crate(s) to the specified native
#                         library NAME. The optional KIND can be one of
#                         static, framework, or dylib (the default).
#         --crate-type [bin|lib|rlib|dylib|cdylib|staticlib|proc-macro]
#                         Comma separated list of types of crates
#                         for the compiler to emit
#         --crate-name NAME
#                         Specify the name of the crate being built
#         --edition 2015|2018
#                         Specify which edition of the compiler to use when
#                         compiling code.
#         --emit [asm|llvm-bc|llvm-ir|obj|metadata|link|dep-info|mir]
#                         Comma separated list of types of output for the
#                         compiler to emit
#         --print [crate-name|file-names|sysroot|cfg|target-list|target-cpus|target-features|relocation-models|code-models|tls-models|target-spec-json|native-static-libs]
#                         Compiler information to print on stdout
#     -g                  Equivalent to -C debuginfo=2
#     -O                  Equivalent to -C opt-level=2
#     -o FILENAME         Write output to <filename>
#         --out-dir DIR   Write output to compiler-chosen filename in <dir>
#         --explain OPT   Provide a detailed explanation of an error message
#         --test          Build a test harness
#         --target TARGET Target triple for which the code is compiled
#     -W, --warn OPT      Set lint warnings
#     -A, --allow OPT     Set lint allowed
#     -D, --deny OPT      Set lint denied
#     -F, --forbid OPT    Set lint forbidden
#         --cap-lints LEVEL
#                         Set the most restrictive lint level. More restrictive
#                         lints are capped at this level
#     -C, --codegen OPT[=VALUE]
#                         Set a codegen option
#     -V, --version       Print version info and exit
#     -v, --verbose       Use verbose output
#         --extern NAME=PATH
#                         Specify where an external rust library is located
#         --extern-private NAME=PATH
#                         Specify where an extern rust library is located,
#                         marking it as a private dependency
#         --sysroot PATH  Override the system root
#         --error-format human|json|short
#                         How errors and other messages are produced
#         --color auto|always|never
#                         Configure coloring of output:
#                         auto = colorize, if output goes to a tty (default);
#                         always = always colorize output;
#                         never = never colorize output
#         --remap-path-prefix FROM=TO
#                         Remap source names in all output (compiler messages
#                         and output files)
#
# Additional help:
#     -C help             Print codegen options
#     -W help             Print 'lint' options and default settings
#     -Z help             Print unstable compiler options

class Arguments:
  def __init__(self):
    self.crate_type = set()
    self.emit = set()
    self.codegen = dict()
    self.others = []

  def __str__(self):
    return " ".join(self.str_list())

  def str_list(self):
    res = []
    if len(self.emit):
      res.append('--emit='+','.join(self.emit))
    if len(self.crate_type):
      res.extend(['--crate-type', ','.join(self.crate_type)])
    for opt in self.codegen.items():
      if opt[1] is not None:
        res.extend(['-C', "{}={}".format(opt[0],opt[1])])
      else:
        res.extend(['-C', "{}".format(opt[0],opt[1])])
    res.extend(self.others)
    return res
  
  def get_codegen_opts(self):
    res = dict()
    for opt in self.codegen:
      k,v = opt.split('=')
      res[k] = v
    return res

  def get_smack_form(self):
    crate_type = self.crate_type
    emit = self.emit
    codegen = self.codegen
    others = self.others
    codegen['opt-level'] = '0'
    others.aappend('-g')
  
def has_equals(arg):
  if '=' in arg:
    s = arg.split('=')
    return s[-1]
  return None
    
def parse_args(argv = sys.argv):
  i = 0
  args = Arguments()
  while i < len(argv):
    arg = argv[i]
    # --crate-type [bin|lib|rlib|dylib|cdylib|staticlib|proc-macro]
    if arg.startswith('--crate-type'):
      opt = has_equals(arg)
      if not opt:
        i += 1
        opt = argv[i]
      for op in opt.split(','):
        args.crate_type.add(op)
    # --emit [asm|llvm-bc|llvm-ir|obj|metadata|link|dep-info|mir]
    elif arg.startswith('--emit'):
      opt = has_equals(arg)
      if not opt:
        i += 1
        opt = argv[i]
      for op in opt.split(','):
        args.emit.add(op)
    elif arg in ('-g', '-O'):
      # Ignore
      pass
    elif arg == '-C':
      i += 1
      if '=' in argv[i]:
        k,v = argv[i].split('=')
      else:
        k = argv[i]
        v = None
      args.codegen[k] = v
    else:
      args.others.append(arg)
    i += 1
  return args
  
args = parse_args(sys.argv[1:])
  
#print(args.get_codegen_opts())

#print(args.str_list())

autocfg=False
for i in args.str_list():
  if 'autocfg' in i:
    autocfg=True
    break

if autocfg:
  with open('/Users/marksb/src/smack/half-rs/newlog.txt', 'a') as f:
    f.write('original: rustc ' + ' '.join(sys.argv[1:]) + '\n')
    f.write('rewrite:  rustc ' + ' '.join(args.str_list()) + '\n')
    f.write('-'*80 + '\n')


proc = subprocess.run(['rustc'] + args.str_list(), env=os.environ)
#proc = subprocess.run(['rustc'] + sys.argv[1:], env=os.environ)

exit(proc.returncode)
