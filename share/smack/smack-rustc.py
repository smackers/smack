#! /usr/bin/env python3

import sys
import os
import subprocess


def smack_overrides(args):
    args['codegen_opts'].update({'debuginfo': '2',
                                 'opt-level': '0',
                                 'no-prepopulate-passes': None,
                                 'passes': 'name-anon-globals'})


def process_equals_arg(argv, i):
    if '=' in argv[i]:
        arg = argv[i].split('=')[-1]
    else:
        assert(len(argv) > i+1)
        i += 1
        arg = argv[i]
    return set(arg.split(',')), i


def parse_args(argv=sys.argv):
    crate_types = set()
    emit_types = {'llvm-bc'}
    other_args = []
    codegen_opts = dict()
    i = 0
    while i < len(argv):
        arg = argv[i]
        # --crate-type [bin|lib|rlib|dylib|cdylib|staticlib|proc-macro]
        if False and arg.startswith('--crate-type'):
            args, i = process_equals_arg(argv, i)
            crate_types |= args
        # --emit [asm|llvm-bc|llvm-ir|obj|metadata|link|dep-info|mir]
        elif arg.startswith('--emit'):
            args, i = process_equals_arg(argv, i)
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
            'other_args': other_args,
            'emit_types': emit_types,
            'codegen_opts': codegen_opts}


args = parse_args(sys.argv[1:])

smack_overrides(args)

argv = []

for x in args['crate_types']:
    argv.extend(['--crate-type', x])

argv.append('--emit='+','.join(args['emit_types']))

for a, v in args['codegen_opts'].items():
    argv.extend(['-C', a+'='+v if v else a])

argv.extend(args['other_args'])

proc = subprocess.run(['rustc'] + argv, env=os.environ)

exit(proc.returncode)
