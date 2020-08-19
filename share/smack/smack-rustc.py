#! /usr/bin/env python3

import sys
import os
import subprocess

# $ rustc --help -v
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

def smack_overrides(args):
  args['codegen_opts'].update({'debuginfo': '2',
                               'opt-level': '0',
                               'no-prepopulate-passes': None,
                               'passes':'name-anon-globals'})


def process_equals_arg(argv, i):
  if '=' in argv[i]:
    arg = argv[i].split('=')[-1]
  else:
    assert(len(argv) > i+1)
    i += 1
    arg = argv[i]
  return set(arg.split(',')), i
      
def parse_args(argv = sys.argv):
  crate_types = set()
  emit_types = {'llvm-bc'}
  other_args = []
  codegen_opts = dict()  
  i = 0
  while i < len(argv):
    arg = argv[i]
    # --crate-type [bin|lib|rlib|dylib|cdylib|staticlib|proc-macro]
    if False and arg.startswith('--crate-type'):
      args, i = process_equals_arg(argv,i)
      crate_types |= args
    # --emit [asm|llvm-bc|llvm-ir|obj|metadata|link|dep-info|mir]
    elif arg.startswith('--emit'):
      args, i = process_equals_arg(argv,i)
      emit_types |= args
    # codegen options -C opt, -C opt=opt -Copt  
    elif arg.startswith('-C'):
      if arg == '-C':
        i += 1
        arg = argv[i]
      else:
        arg = arg[2:]
        
      if len(arg.split('=')) == 2:
        a, v = arg.split('=')
      else:
        a, v = arg, None
      codegen_opts[a] = v
    else:
      other_args.append(argv[i])
    i += 1
  return {'crate_types': crate_types,
          'other_args' : other_args,
          'emit_types': emit_types,
          'codegen_opts': codegen_opts}
    
args = parse_args(sys.argv[1:])

smack_overrides(args)

argv = []
for x in args['crate_types']:
  argv.extend(['--crate-type', x])
argv.append('--emit='+','.join(args['emit_types']))
for a,v in args['codegen_opts'].items():
  argv.extend(['-C', a+'='+v if v else a])
argv.extend(args['other_args'])

with open('/Users/marksb/src/smack/half-rs/newlog.txt', 'a') as f:
  f.write('original: rustc ' + ' '.join(sys.argv[1:]) + '\n')
  f.write('rewrite:  rustc ' + ' '.join(argv) + '\n')
  f.write('-'*80 + '\n')
    
#proc = subprocess.run(['rustc'] + args.str_list(), env=os.environ)
#proc = subprocess.run(['rustc'] + sys.argv[1:], env=os.environ)
proc = subprocess.run(['rustc'] + argv, env=os.environ)

exit(proc.returncode)
