'''
TODO: add a docstring
'''

import argparse
import json
import os
import re
import sys
import shlex
import subprocess
from smack.svcomp.utils import verify_bpl_svcomp
from smack.utils import temporary_file, try_command, remove_temp_files
from smack.replay import replay_error_trace
from smack.frontend import link_bc_files, frontends, languages, extra_libs

VERSION = '2.0.0'

llvm2bpl_forwarded_opts = []

def results(args):
    """A dictionary of the result output messages."""
    return {
        'verified': 'SMACK found no errors.' if args.modular else \
            'SMACK found no errors with unroll bound %s.' % args.unroll,
        'error': 'SMACK found an error.',
        'invalid-deref': 'SMACK found an error: invalid pointer dereference.',
        'invalid-free': 'SMACK found an error: invalid memory deallocation.',
        'invalid-memtrack': 'SMACK found an error: memory leak.',
        'overflow': 'SMACK found an error: integer overflow.',
        'timeout': 'SMACK timed out.',
        'unknown': 'SMACK result is unknown.'}

def inlined_procedures():
    '''A list of inlined procedures'''
    return [
        '$galloc',
        '$alloc',
        '$malloc',
        '$free',
        '$memset',
        '$memcpy',
        '__VERIFIER_',
        '$initialize',
        '__SMACK_static_init',
        '__SMACK_init_func_memory_model',
        '__SMACK_check_overflow']

class ForwardAction(argparse.Action):
    def __init__(self, option_strings, dest, **kwargs):
        super(ForwardAction, self).__init__(option_strings, dest, **kwargs)
    def __call__(self, parser, namespace, values, option_string=None):
        llvm2bpl_forwarded_opts.append(option_string)
        if self.nargs == 0:
            setattr(namespace, self.dest, True)
        else:
            llvm2bpl_forwarded_opts.append(values)
            setattr(namespace, self.dest, values)

def exit_with_error(error):
    sys.exit('Error: %s.' % error)

def validate_input_file(input_file):
    """Check whether the given input file is valid, returning a reason if not."""

    file_extension = os.path.splitext(input_file)[1][1:]
    if not os.path.isfile(input_file):
        exit_with_error("Cannot find file %s" % input_file)

    if not os.access(input_file, os.R_OK):
        exit_with_error("Cannot read file %s" % input_file)

    elif file_extension not in languages():
        exit_with_error("Unexpected source file extension '%s'" % file_extension)

def validate_output_file(output_file):
    dir_name = os.path.dirname(os.path.abspath(output_file))
    if not os.path.isdir(dir_name):
        exit_with_error("directory %s doesn't exist" % dir_name)
    if not os.access(dir_name, os.W_OK):
        exit_with_error("file %s may not be writeable" % output_file)
    #try:
    #  with open(file, 'w') as f:
    #    pass
    #except IOError:
    #  exit_with_error("file %s may not be writeable" % file)

def checked_type(arg_type, check_func, nargs=None):
    def apply_and_check_type(arg):
        arg = arg_type(arg)
        if nargs:
            map(check_func, arg.split())
        else:
            check_func(arg)
        return arg
    return apply_and_check_type

def arguments():
    """Parse command-line arguments"""
    def add_group_arg_func(group):
        return group.add_argument

    parser = argparse.ArgumentParser()

    parser.add_argument('input_files', metavar='input-files', nargs='+',
                        type=checked_type(str, validate_input_file, '+'),
                        help='source file to be translated/verified')

    parser.add_argument('--version', action='version',
                        version='SMACK version ' + VERSION)

    add_noise_arg = add_group_arg_func(parser.add_mutually_exclusive_group())

    add_noise_arg('-q', '--quiet', action='store_true', default=False,
                  help='enable quiet output')

    add_noise_arg('-v', '--verbose', action='store_true', default=False,
                  help='enable verbose output')

    add_noise_arg('-d', '--debug', action=ForwardAction, nargs=0, default=False,
                  help='enable debugging output')

    add_noise_arg('--debug-only', metavar=ForwardAction, default=None,
                  type=str, help='limit debugging output to given MODULES')

    add_noise_arg('--warn', default="unsound",
                  choices=['silent', 'unsound', 'info'],
                  help='''enable certain type of warning messages
                  (silent: no warning messages;
                  unsound: warnings about unsoundness;
                  info: warnings about unsoundness and translation information)''' +
                  '[default: %(default)s]')

    parser.add_argument('-t', '--no-verify', action="store_true", default=False,
                        help='perform only translation, without verification.')

    parser.add_argument('-w', '--error-file', metavar='FILE', default=None,
                        type=str, help='save error trace/witness to FILE')


    add_frontend_arg = add_group_arg_func(parser.add_argument_group('front-end options'))

    add_frontend_arg('-x', '--language', metavar='LANG',
                     choices=frontends().keys(), default=None,
                     help='Treat input files as having type LANG.')

    add_frontend_arg('-bc', '--bc-file', metavar='FILE', default=None,
                     type=checked_type(str, validate_output_file),
                     help='save initial LLVM bitcode to FILE')

    add_frontend_arg('--linked-bc-file', metavar='FILE', default=None,
                     type=str, help=argparse.SUPPRESS)

    add_frontend_arg('--replay-harness', metavar='FILE', default='replay-harness.c',
                     type=str, help=argparse.SUPPRESS)

    add_frontend_arg('--replay-exe-file', metavar='FILE', default='replay-exe',
                     type=str, help=argparse.SUPPRESS)

    add_frontend_arg('-ll', '--ll-file', metavar='FILE', default=None,
                     type=checked_type(str, validate_output_file),
                     action=ForwardAction,
                     help='save final LLVM IR to FILE')

    add_frontend_arg('--clang-options', metavar='OPTIONS', default='',
                     help='''additional compiler arguments
                     (e.g., --clang-options="-w -g")''')


    add_translate_arg = add_group_arg_func(parser.add_argument_group('translation options'))

    add_translate_arg('-bpl', '--bpl-file', metavar='FILE', default=None,
                      type=checked_type(str, validate_output_file),
                      help='save (intermediate) Boogie code to FILE')

    add_translate_arg('--no-memory-splitting',
                      action=ForwardAction, nargs=0, default=False,
                      help='disable region-based memory splitting')

    add_translate_arg('--mem-mod', choices=['no-reuse', 'no-reuse-impls', 'reuse'],
                      default='no-reuse-impls',
                      help='''select memory model
                      (no-reuse=never reallocate the same address,
                      reuse=reallocate freed addresses) [default: %(default)s]''')

    add_translate_arg('--static-unroll', action=ForwardAction, nargs=0, default=False,
                      help='enable static LLVM loop unrolling pass as a preprocessing step')

    add_translate_arg('--pthread', action='store_true', default=False,
                      help='enable support for pthread programs')

    add_translate_arg('--bit-precise', action=ForwardAction, nargs=0, default=False,
                      help='model non-pointer values as bit vectors')

    add_translate_arg('--timing-annotations', action=ForwardAction, nargs=0, default=False,
                      help='enable timing annotations')

    add_translate_arg('--bit-precise-pointers',
                      action=ForwardAction, nargs=0, default=False,
                      help='model pointers and non-pointer values as bit vectors')

    add_translate_arg('--no-byte-access-inference',
                      action=ForwardAction, nargs=0, default=False,
                      help='disable bit-precision-related optimizations with DSA')

    add_translate_arg('--entry-points', metavar='PROC', nargs='+',
                      default=['main'], help='specify top-level procedures [default: %(default)s]')

    add_translate_arg('--memory-safety', action=ForwardAction, nargs=0, default=False,
                      help='enable memory safety checks')

    add_translate_arg('--only-check-valid-deref', action='store_true', default=False,
                      help='only enable valid dereference checks')

    add_translate_arg('--only-check-valid-free', action='store_true', default=False,
                      help='only enable valid free checks')

    add_translate_arg('--only-check-memleak', action='store_true', default=False,
                      help='only enable memory leak checks')

    add_translate_arg('--integer-overflow', action=ForwardAction, nargs=0, default=False,
                      help='enable integer overflow checks')

    add_translate_arg('--float', action=ForwardAction, nargs=0, default=False,
                      help='enable bit-precise floating-point functions')

    add_translate_arg('--strings', action='store_true', default=False,
                      help='enable support for string')

    add_verifier_arg = add_group_arg_func(parser.add_argument_group('verifier options'))

    add_verifier_arg('--verifier',
                     choices=['boogie', 'corral', 'symbooglix', 'svcomp'], default='corral',
                     help='back-end verification engine')

    add_verifier_arg('--unroll', metavar='N', default='1',
                     type=checked_type(int,
                                       lambda x: exit_with_error('Unroll bound has to be positive')
                                       if x <= 0 else None),
                     help='loop/recursion unroll bound [default: %(default)s]')

    add_verifier_arg('--loop-limit', metavar='N', default='1', type=int,
                     help='upper bound on minimum loop iterations [default: %(default)s]')

    add_verifier_arg('--context-bound', metavar='K', default='1', type=int,
                     help='bound on the number of thread contexts in Corral [default: %(default)s]')

    add_verifier_arg('--verifier-options', metavar='OPTIONS', default='',
                     help='''additional verifier arguments
                     (e.g., --verifier-options="/trackAllVars /staticInlining")''')

    add_verifier_arg('--time-limit', metavar='N', default='1200', type=int,
                     help='verifier time limit, in seconds [default: %(default)s]')

    add_verifier_arg('--max-violations', metavar='N', default='1', type=int,
                     help='maximum reported assertion violations [default: %(default)s]')

    add_verifier_arg('--smackd', action="store_true", default=False,
                     help='generate JSON-format output for SMACKd')

    add_verifier_arg('--svcomp-property', metavar='FILE', default=None,
                     type=str, help='load SVCOMP property to check from FILE')

    add_verifier_arg('--modular', action=ForwardAction, nargs=0, default=False,
                     help='enable contracts-based modular deductive verification (uses Boogie)')

    add_verifier_arg('--replay', action="store_true", default=False,
                     help='enable reply of error trace with test harness.')

    add_plugins_arg = add_group_arg_func(parser.add_argument_group('plugins'))

    add_plugins_arg('--transform-bpl', metavar='COMMAND', default=None,
                    type=str, help='transform generated Boogie code via COMMAND')

    add_plugins_arg('--transform-out', metavar='COMMAND', default=None,
                    type=str, help='transform verifier output via COMMAND')

    args = parser.parse_args()

    if not args.bc_file:
        args.bc_file = temporary_file('a', '.bc', args)

    if not args.linked_bc_file:
        args.linked_bc_file = temporary_file('b', '.bc', args)

    if not args.bpl_file:
        args.bpl_file = 'a.bpl' if args.no_verify else temporary_file('a', '.bpl', args)

    if args.only_check_valid_deref or args.only_check_valid_free or args.only_check_memleak:
        args.memory_safety = True

    if args.bit_precise_pointers:
        args.bit_precise = True

    # TODO are we (still) using this?
    # with open(args.input_file, 'r') as f:
    #   for line in f.readlines():
    #     m = re.match('.*SMACK-OPTIONS:[ ]+(.*)$', line)
    #     if m:
    #       return args = parser.parse_args(m.group(1).split() + sys.argv[1:])

    return args

def target_selection(args):
    """Determine the target architecture based on flags and source files."""
    # TODO more possible clang flags that determine the target?
    if not re.search('-target', args.clang_options):
        src = args.input_files[0]
        if os.path.splitext(src)[1] == '.bc':
            ll_file = temporary_file(os.path.splitext(os.path.basename(src))[0], '.ll', args)
            try_command(['llvm-dis', '-o', ll_file, src])
            src = ll_file
        if os.path.splitext(src)[1] == '.ll':
            with open(src, 'r') as input_file:
                for line in input_file:
                    triple = re.findall('^target triple = "(.*)"', line)
                    if len(triple) > 0:
                        args.clang_options += (" -target %s" % triple[0])
                        break

def generate_llvm_ir(args):
    """Generate the LLVM bitcode file."""
    bitcodes = []
    libs = set()
    noreturning_frontend = False

    def add_libs(lang):
        if lang in extra_libs():
            libs.add(extra_libs()[lang])

    if args.language:
        lang = languages()[args.language]
        if lang in ['boogie', 'svcomp', 'json']:
            noreturning_frontend = True

        add_libs(lang)
        frontend = frontends()[lang]
        for input_file in args.input_files:
            bitcode = frontend(input_file, args)
            if bitcode is not None:
                bitcodes.append(bitcode)

    else:
        for input_file in args.input_files:
            lang = languages()[os.path.splitext(input_file)[1][1:]]
            if lang in ['boogie', 'svcomp', 'json']:
                noreturning_frontend = True

            add_libs(lang)
            bitcode = frontends()[lang](input_file, args)
            if bitcode is not None:
                bitcodes.append(bitcode)

    if not noreturning_frontend:
        return link_bc_files(bitcodes, libs, args)

def llvm_to_bpl(args):
    """Translate the LLVM bitcode file to a Boogie source file."""

    cmd = ['llvm2bpl', args.linked_bc_file, '-bpl', args.bpl_file]
    cmd += ['-warn-type', args.warn]
    if sys.stdout.isatty():
        cmd += ['-colored-warnings']
    cmd += ['-source-loc-syms']
    for entry_point in args.entry_points:
        cmd += ['-entry-points', entry_point]
    if "impls" in args.mem_mod:
        cmd += ['-mem-mod-impls']
    cmd += llvm2bpl_forwarded_opts
    try_command(cmd, console=True)
    annotate_bpl(args)
    property_selection(args)
    transform_bpl(args)

def procedure_annotation(name, args):
    if name in args.entry_points:
        return "{:entrypoint}"
    elif args.modular and re.match("|".join(inlined_procedures()).replace("$", r"\$"), name):
        return "{:inline 1}"
    elif (not args.modular) and args.verifier == 'boogie':
        return "{:inline %s}" % args.unroll
    else:
        return ""

def annotate_bpl(args):
    """Annotate the Boogie source file with additional metadata."""

    proc_decl = re.compile(r'procedure\s+([^\s(]*)\s*\(')

    with open(args.bpl_file, 'r+') as bpl_file:
        bpl = "// generated by SMACK version %s for %s\n" % (VERSION, args.verifier)
        bpl += "// via %s\n\n" % " ".join(sys.argv)
        bpl += proc_decl.sub(
            lambda m: ("procedure %s %s(" % (procedure_annotation(m.group(1), args), m.group(1))),
            bpl_file.read())
        bpl_file.seek(0)
        bpl_file.truncate()
        bpl_file.write(bpl)

def property_selection(args):
    selected_props = []
    if args.only_check_valid_deref:
        selected_props.append('valid_deref')
    elif args.only_check_valid_free:
        selected_props.append('valid_free')
    elif args.only_check_memleak:
        selected_props.append('valid_memtrack')

    def replace_assertion(match):
        if len(selected_props) > 0:
            if match.group(2) and match.group(3) in selected_props:
                attrib = match.group(2)
                expr = match.group(4)
            else:
                attrib = ''
                expr = 'true'
            return match.group(1) + attrib + expr + ";"
        else:
            return match.group(0)

    with open(args.bpl_file, 'r+') as bpl_file:
        lines = bpl_file.readlines()
        bpl_file.seek(0)
        bpl_file.truncate()
        for line in lines:
            line = re.sub(r'^(\s*assert\s*)({:(.+)})?(.+);', replace_assertion, line)
            bpl_file.write(line)

def transform_bpl(args):
    if args.transform_bpl:
        with open(args.bpl_file, 'r+') as bpl:
            old = bpl.read()
            bpl.seek(0)
            bpl.truncate()
            proc = subprocess.Popen(shlex.split(args.transform_bpl),
                                    stdin=subprocess.PIPE,
                                    stdout=bpl)
            proc.communicate(input=old)

def transform_out(args, old):
    out = old
    if args.transform_out:
        proc = subprocess.Popen(shlex.split(args.transform_out),
                                stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        out, _ = proc.communicate(input=old)
    return out

def verification_result(verifier_output):
    if re.search(r'[1-9]\d* time out|Z3 ran out of resources|timed out|ERRORS_TIMEOUT',
                 verifier_output):
        return 'timeout'
    elif re.search(r'[1-9]\d* verified, 0 errors?|no bugs|NO_ERRORS_NO_TIMEOUT', verifier_output):
        return 'verified'
    elif re.search(r'\d* verified, [1-9]\d* errors?|can fail|ERRORS_NO_TIMEOUT', verifier_output):
        if re.search(r'ASSERTION FAILS assert {:valid_deref}', verifier_output):
            return 'invalid-deref'
        elif re.search(r'ASSERTION FAILS assert {:valid_free}', verifier_output):
            return 'invalid-free'
        elif re.search(r'ASSERTION FAILS assert {:valid_memtrack}', verifier_output):
            return 'invalid-memtrack'
        elif re.search(r'ASSERTION FAILS assert {:overflow}', verifier_output):
            return 'overflow'
        else:
            call_list = re.findall(r'\(CALL .+\)', verifier_output)
            if len(call_list) > 0 and re.search(r'free_', call_list[len(call_list)-1]):
                return 'invalid-free'
            else:
                return 'error'
    else:
        return 'unknown'

def verify_bpl(args):
    """Verify the Boogie source file with a back-end verifier."""

    if args.verifier == 'svcomp':
        verify_bpl_svcomp(args)
        return

    elif args.verifier == 'boogie' or args.modular:
        command = ["boogie"]
        command += [args.bpl_file]
        command += ["/nologo", "/noinfer", "/doModSetAnalysis"]
        command += ["/timeLimit:%s" % args.time_limit]
        command += ["/errorLimit:%s" % args.max_violations]
        if not args.modular:
            command += ["/loopUnroll:%d" % args.unroll]

    elif args.verifier == 'corral':
        command = ["corral"]
        command += [args.bpl_file]
        command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
        command += ["/k:%d" % args.context_bound]
        command += ["/useProverEvaluate"]
        command += ["/timeLimit:%s" % args.time_limit]
        command += ["/cex:%s" % args.max_violations]
        command += ["/maxStaticLoopBound:%d" % args.loop_limit]
        command += ["/recursionBound:%d" % args.unroll]

    elif args.verifier == 'symbooglix':
        command = ['symbooglix']
        command += [args.bpl_file]
        command += ["--file-logging=0"]
        command += ["--entry-points=%s" % ",".join(args.entry_points)]
        command += ["--timeout=%d" % args.time_limit]
        command += ["--max-loop-depth=%d" % args.unroll]

    if (args.bit_precise or args.float) and args.verifier != 'symbooglix':
        bopt = "bopt:" if args.verifier != 'boogie' else ""
        command += ["/%sproverOpt:OPTIMIZE_FOR_BV=true" % bopt]
        command += ["/%sboolControlVC" % bopt]

    if args.verifier_options:
        command += args.verifier_options.split()

    verifier_output = try_command(command, timeout=args.time_limit)
    verifier_output = transform_out(args, verifier_output)
    result = verification_result(verifier_output)

    if args.smackd:
        print smackd_output(verifier_output)

    elif result == 'verified':
        print results(args)[result]

    else:
        if result == 'error' or \
           result == 'invalid-deref' or \
           result == 'invalid-free' or \
           result == 'invalid-memtrack' or \
           result == 'overflow':
            error = error_trace(verifier_output)

            if args.error_file:
                with open(args.error_file, 'w') as err_file:
                    err_file.write(error)

            if not args.quiet:
                print error

            if args.replay:
                replay_error_trace(verifier_output, args)

        sys.exit(results(args)[result])

def error_step(step):
    file_name_pat = r'[\w#$~%.\/-]*'
    step = re.match(r"(\s*)(%s)\((\d+),\d+\): (.*)" % file_name_pat, step)
    if step:
        if re.match('.*[.]bpl$', step.group(2)):
            line_no = int(step.group(3))
            message = step.group(4)
            if re.match(r'.*\$bb\d+.*', message):
                message = ""
            with open(step.group(2)) as src_file:
                for line in src_file.read().splitlines(True)[line_no:line_no+10]:
                    src = re.match(r".*{:sourceloc \"(%s)\", (\d+), (\d+)}" % file_name_pat, line)
                    if src:
                        return "%s%s(%s,%s): %s" % \
                        (step.group(1), src.group(1), src.group(2), src.group(3), message)
        else:
            return corral_error_step(step.group(0))
    else:
        return None

def reformat_assignment(line):
    def repl(match):
        val = match.group(1)
        if 'bv' in val:
            return match.group(2)+'UL'
        else:
            sig_size = int(match.group(7))
            exp_size = int(match.group(8))
            # assume we can only handle double
            if sig_size > 53 or exp_size > 11:
                return match.group()

            sign_val = -1 if match.group(3) != '' else 1
            sig_val = match.group(4)
            exp_sign_val = -1 if match.group(5) != '' else 1
            # note that the exponent base is 16
            exp_val = 2**(4*exp_sign_val*int(match.group(6)))
            return str(sign_val*float.fromhex(sig_val)*exp_val)

    # Boogie FP const grammar: (-)0x[sig]e[exp]f[sigSize]e[expSize], where
    # sig = hexdigit {hexdigit} '.' hexdigit {hexdigit}
    # exp = digit {digit}
    # sigSize = digit {digit}
    # expSize = digit {digit}
    return re.sub(r'((\d+)bv\d+|(-?)0x([0-9a-fA-F]+\.[0-9a-fA-F]+)e(-?)(\d+)f(\d+)e(\d+))',
                  repl, line.strip())

def transform(info):
    return ','.join(map(reformat_assignment, filter(
        lambda x: not re.search(r'((CALL|RETURN from)\s+(\$|__SMACK))|Done|ASSERTION', x),
        info.split(','))))

def corral_error_step(step):
    match = re.match(r'([^\s]*)\s+Trace:\s+(Thread=\d+)\s+\((.*)[\)|;]', step)
    if match:
        path = match.group(1)
        tid = match.group(2)
        info = transform(match.group(3))
        return '{0}\t{1}  {2}'.format(path, tid, info)
    else:
        return step

def error_trace(verifier_output):
    trace = ""
    for line in verifier_output.splitlines(True):
        step = error_step(line)
        if step:
            match = re.match('(.*): [Ee]rror [A-Z0-9]+: (.*)', step)
            if match:
                trace += "%s: %s\nExecution trace:\n" % (match.group(1), match.group(2))
            else:
                trace += ('' if step[0] == ' ' else '    ') + step + "\n"

    return trace

def smackd_output(corral_output):
    file_name_pat = r'[\w#$~%.\/-]+'
    trace_pat = re.compile('(' + file_name_pat +
                           r')\((\d+),(\d+)\): Trace: Thread=(\d+)  (\((.*)[\);])?$')
    err_pat = re.compile('(' + file_name_pat + r')\((\d+),(\d+)\): (error .*)$')

    passed_match = re.search('Program has no bugs', corral_output)
    if passed_match:
        json_data = {
            'verifier': 'corral',
            'passed?': True}

    else:
        traces = []
        filename = ''
        lineno = 0
        colno = 0
        threadid = 0
        desc = ''
        for trace_line in corral_output.splitlines(True):
            trace_match = trace_pat.match(trace_line)
            if trace_match:
                filename = str(trace_match.group(1))
                lineno = int(trace_match.group(2))
                colno = int(trace_match.group(3))
                threadid = int(trace_match.group(4))
                desc = str(trace_match.group(6))
                for elem in desc.split(','):
                    elem = elem.strip()
                    assm = re.sub(r'=(\s*\d+)bv\d+', r'=\1', elem) if '=' in elem else ''
                    trace = {'threadid': threadid,
                             'file': filename,
                             'line': lineno,
                             'column': colno,
                             'description': elem,
                             'assumption': assm}
                    traces.append(trace)
            else:
                err_match = err_pat.match(trace_line)
                if err_match:
                    filename = str(err_match.group(1))
                    lineno = int(err_match.group(2))
                    colno = int(err_match.group(3))
                    desc = str(err_match.group(4))

        fails_at = {'file': filename, 'line': lineno, 'column': colno, 'description': desc}

        json_data = {
            'verifier': 'corral',
            'passed?': False,
            'failsAt': fails_at,
            'threadCount': 1,
            'traces': traces}

    json_string = json.dumps(json_data)
    return json_string

def main():
    try:
        global smack_args
        smack_args = arguments()

        target_selection(smack_args)

        if not smack_args.quiet:
            print "SMACK program verifier version %s" % VERSION

        generate_llvm_ir(smack_args)

        if smack_args.no_verify:
            if not smack_args.quiet:
                print "SMACK generated %s" % smack_args.bpl_file
        else:
            verify_bpl(smack_args)

    except KeyboardInterrupt:
        sys.exit("SMACK aborted by keyboard interrupt.")

    finally:
        remove_temp_files()
