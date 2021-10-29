import argparse
import os
import re
import sys
import shlex
import subprocess
import signal
import functools
from enum import Flag, auto
from .svcomp.utils import verify_bpl_svcomp
from .utils import temporary_file, try_command, remove_temp_files,\
    llvm_exact_bin
from .replay import replay_error_trace
from .frontend import link_bc_files, frontends, languages, extra_libs
from .errtrace import error_trace, json_output_str

VERSION = '2.8.0'


class VResult(Flag):
    '''
    This class represents verification results.
    `MEMSAFETY_ERROR` and `ERROR` do not correspond to any results. They are
    used to group certain results.
    '''

    VERIFIED = auto()
    ASSERTION_FAILURE = auto()
    INVALID_DEREF = auto()
    INVALID_FREE = auto()
    INVALID_MEMTRACK = auto()
    OVERFLOW = auto()
    RUST_PANIC = auto()
    TIMEOUT = auto()
    UNKNOWN = auto()
    MEMSAFETY_ERROR = INVALID_DEREF | INVALID_FREE | INVALID_MEMTRACK
    ERROR = (ASSERTION_FAILURE | INVALID_DEREF | INVALID_FREE
             | INVALID_MEMTRACK | OVERFLOW | RUST_PANIC)

    def __str__(self):
        return self.name.lower().replace('_', '-')

    def description(self):
        '''Return the description for certain result.'''

        descriptions = {
            VResult.ASSERTION_FAILURE: '',
            VResult.INVALID_DEREF: 'invalid pointer dereference',
            VResult.INVALID_FREE: 'invalid memory deallocation',
            VResult.INVALID_MEMTRACK: 'memory leak',
            VResult.OVERFLOW: 'integer overflow',
            VResult.RUST_PANIC: 'Rust panic'}

        if self in descriptions:
            return descriptions[self]
        else:
            raise RuntimeError('No description associated with result: %s'
                               % self)

    def return_code(self):
        '''Return the exit code for each result.'''

        return_codes = {
            VResult.VERIFIED: 0,
            VResult.ASSERTION_FAILURE: 1,
            VResult.INVALID_DEREF: 2,
            VResult.INVALID_FREE: 3,
            VResult.INVALID_MEMTRACK: 4,
            VResult.OVERFLOW: 5,
            VResult.RUST_PANIC: 6,
            VResult.TIMEOUT: 126,
            VResult.UNKNOWN: 127}

        if self in return_codes:
            return return_codes[self]
        else:
            raise RuntimeError('No return code associated with result: %s'
                               % self)

    def message(self, args):
        '''Return SMACK's output for each result.'''

        if self is VResult.VERIFIED:
            return ('SMACK found no errors'
                    + ('' if args.modular else ' with unroll bound %s'
                        % args.unroll) + '.')
        elif self in VResult.ERROR:
            description = self.description()
            return ('SMACK found an error'
                    + (': %s' % description if description else '') + '.')
        elif self is VResult.TIMEOUT:
            return 'SMACK timed out.'
        elif self is VResult.UNKNOWN:
            return 'SMACK result is unknown.'
        else:
            raise RuntimeError('No message associated with result: %s' % self)


class PropertyAction(argparse.Action):
    '''
    This class defines the argparse action when the arguments of the `--check`
    option are consumed.
    '''

    def __init__(self, option_strings, dest, **kwargs):
        super(PropertyAction, self).__init__(option_strings, dest, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        '''
        Fold the provided arguments with bitwise or. This is equivalent to
        extending the property list with the arguments.
        '''

        setattr(namespace, self.dest,
                functools.reduce(lambda x, y: x | y, values,
                                 getattr(namespace, self.dest)))


# Shaobo: shamelessly borrowed it from https://stackoverflow.com/a/55500795
class VProperty(Flag):
    '''
    This class defines the properties that SMACK verifies. `NONE` is a special
    value that does not correspond to any property. It's used simply to get
    around the default value issue when the action similar to `extend`.
    '''

    NONE = 0
    ASSERTIONS = auto()
    VALID_DEREF = auto()
    VALID_FREE = auto()
    MEMLEAK = auto()
    MEMORY_SAFETY = VALID_DEREF | VALID_FREE | MEMLEAK
    INTEGER_OVERFLOW = auto()
    RUST_PANICS = auto()

    def __str__(self):
        return self.name.lower().replace('_', '-')

    def __repr__(self):
        return str(self)

    @staticmethod
    def argparse(s):
        try:
            return VProperty[s.upper().replace('-', '_')]
        except KeyError:
            return s

    @staticmethod
    def mem_safe_subprops():
        return [VProperty.VALID_DEREF, VProperty.VALID_FREE, VProperty.MEMLEAK]

    def contains_mem_safe_props(self):
        '''
        Test if a property is either memory-safety or any of its subproperties.
        '''

        return bool(self & VProperty.MEMORY_SAFETY)

    def boogie_attr(self):
        '''
        Return the attribute of Boogie assert command for certain property.
        '''

        def get_attr_from_result(x):
            if x in VResult.MEMSAFETY_ERROR:
                return x.name.lower()[2:]
            else:
                return x.name.lower()

        attrs = {
            VProperty.VALID_DEREF: get_attr_from_result(VResult.INVALID_DEREF),
            VProperty.VALID_FREE: get_attr_from_result(VResult.INVALID_FREE),
            VProperty.MEMLEAK: get_attr_from_result(VResult.INVALID_MEMTRACK),
            VProperty.INTEGER_OVERFLOW: get_attr_from_result(VResult.OVERFLOW),
            VProperty.RUST_PANICS: get_attr_from_result(VResult.RUST_PANIC)}

        if self in attrs:
            return attrs[self]
        else:
            raise RuntimeError('No assertion Boogie attribute associated with'
                               'property: %s' % self)

    def result(self):
        '''Link SMACK properties with results'''

        res = {
            VProperty.VALID_DEREF: VResult.INVALID_DEREF,
            VProperty.VALID_FREE: VResult.INVALID_FREE,
            VProperty.MEMLEAK: VResult.INVALID_MEMTRACK,
            VProperty.INTEGER_OVERFLOW: VResult.OVERFLOW,
            VProperty.RUST_PANICS: VResult.RUST_PANIC}

        if self in res:
            return res[self]
        else:
            raise RuntimeError(('No SMACK result associated with property: %s'
                                % self))


def inlined_procedures():
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
        '__SMACK_loop_exit',
        '__SMACK_check_overflow'
    ]


class FileAction(argparse.Action):
    def __init__(self, option_strings, dest, **kwargs):
        super(FileAction, self).__init__(option_strings, dest, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        if option_string is None:
            validate_input_files(values)
        else:
            # presumably output files (e.g., .bc, .ll, etc)
            validate_output_file(values)
        setattr(namespace, self.dest, values)


def exit_with_error(error):
    sys.exit('Error: %s.' % error)


def validate_input_files(files):
    def validate_input_file(file):
        """
        Check whether the given input file is valid, returning a reason if not.
        """

        file_extension = os.path.splitext(file)[1][1:]
        if not os.path.isfile(file):
            exit_with_error("Cannot find file %s" % file)

        if not os.access(file, os.R_OK):
            exit_with_error("Cannot read file %s" % file)

        elif file_extension not in languages():
            exit_with_error(
                "Unexpected source file extension '%s'" %
                file_extension)
    list(map(validate_input_file, files))


def validate_output_file(file):
    dir_name = os.path.dirname(os.path.abspath(file))
    if not os.path.isdir(dir_name):
        exit_with_error("directory %s doesn't exist" % dir_name)
    if not os.access(dir_name, os.W_OK):
        exit_with_error("file %s may not be writeable" % file)
    # try:
    #  with open(file, 'w') as f:
    #    pass
    # except IOError:
    #  exit_with_error("file %s may not be writeable" % file)


def arguments():
    """Parse command-line arguments"""

    parser = argparse.ArgumentParser()

    parser.add_argument(
        'input_files',
        metavar='input-files',
        nargs='+',
        action=FileAction,
        type=str,
        help='source file to be translated/verified')

    parser.add_argument('--version', action='version',
                        version='SMACK version ' + VERSION)

    noise_group = parser.add_mutually_exclusive_group()

    noise_group.add_argument(
        '-q',
        '--quiet',
        action='store_true',
        default=False,
        help='enable quiet output')

    noise_group.add_argument(
        '-v',
        '--verbose',
        action='store_true',
        default=False,
        help='enable verbose output')

    noise_group.add_argument(
        '-d',
        '--debug',
        action="store_true",
        default=False,
        help='enable debugging output')

    noise_group.add_argument(
        '--debug-only',
        metavar='MODULES',
        default=None,
        type=str,
        help='limit debugging output to given MODULES')

    noise_group.add_argument('--warn', default="approximate",
                             choices=['silent', 'approximate', 'info'],
                             help='''enable certain type of warning messages
            (silent: no warning messages;
            approximate: warnings about introduced approximations;
            info: warnings about introduced approximations and
            translation information)
            [default: %(default)s]''')

    parser.add_argument(
        '-t',
        '--no-verify',
        action="store_true",
        default=False,
        help='perform only translation, without verification.')

    parser.add_argument('-w', '--error-file', metavar='FILE', default=None,
                        type=str, help='save error trace/witness to FILE')

    parser.add_argument('--json-file', metavar='FILE', default=None,
                        type=str, help='generate JSON output to FILE')

    frontend_group = parser.add_argument_group('front-end options')

    frontend_group.add_argument('-x', '--language', metavar='LANG',
                                choices=list(frontends().keys()), default=None,
                                help='Treat input files as having type LANG.')

    frontend_group.add_argument(
        '-bc',
        '--bc-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save initial LLVM bitcode to FILE')

    frontend_group.add_argument(
        '--linked-bc-file',
        metavar='FILE',
        default=None,
        type=str,
        help=argparse.SUPPRESS)

    frontend_group.add_argument(
        '--replay-harness',
        metavar='FILE',
        default='replay-harness.c',
        type=str,
        help=argparse.SUPPRESS)

    frontend_group.add_argument(
        '--replay-exe-file',
        metavar='FILE',
        default='replay-exe',
        type=str,
        help=argparse.SUPPRESS)

    frontend_group.add_argument(
        '-ll',
        '--ll-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save final LLVM IR to FILE')

    frontend_group.add_argument(
        '--clang-options',
        metavar='OPTIONS',
        default='',
        help='additional compiler arguments (e.g., --clang-options="-w -g")')

    translate_group = parser.add_argument_group('translation options')

    translate_group.add_argument(
        '-bpl',
        '--bpl-file',
        metavar='FILE',
        default=None,
        action=FileAction,
        type=str,
        help='save (intermediate) Boogie code to FILE')

    translate_group.add_argument(
        '--rewrite-bitwise-ops',
        action="store_true",
        default=False,
        help='''attempts to provide models for bitwise operations
                when integer encoding is used''')

    translate_group.add_argument(
        '--no-memory-splitting',
        action="store_true",
        default=False,
        help='disable region-based memory splitting')

    translate_group.add_argument(
        '--mem-mod',
        choices=[
            'no-reuse',
            'no-reuse-impls',
            'reuse'],
        default='no-reuse-impls',
        help='''select memory model
                (no-reuse=never reallocate the same address,
                reuse=reallocate freed addresses) [default: %(default)s]''')

    translate_group.add_argument(
        '--static-unroll',
        action="store_true",
        default=False,
        help='enable static LLVM loop unrolling pass as a preprocessing step')

    translate_group.add_argument(
        '--pthread',
        action='store_true',
        default=False,
        help='enable support for pthread programs')

    translate_group.add_argument(
        '--max-threads',
        default='32',
        type=int,
        help='bound on the number of threads [default: %(default)s]')

    translate_group.add_argument(
        '--integer-encoding',
        choices=['bit-vector', 'unbounded-integer', 'wrapped-integer'],
        default='unbounded-integer',
        help='''machine integer encoding
                (bit-vector=use SMT bit-vector theory,
                unbounded-integer=use SMT integer theory,
                wrapped-integer=use SMT integer theory but model wrap-around
                behavior) [default: %(default)s]''')

    translate_group.add_argument(
        '--timing-annotations',
        action="store_true",
        default=False,
        help='enable timing annotations')

    translate_group.add_argument(
        '--pointer-encoding',
        choices=['bit-vector', 'unbounded-integer'],
        default='unbounded-integer',
        help='''pointer encoding
                (bit-vector=use SMT bit-vector theory,
                ubounded-integer=use SMT integer theory)
                [default: %(default)s]''')

    translate_group.add_argument(
        '--no-byte-access-inference',
        action="store_true",
        default=False,
        help='disable bit-precision-related optimizations with DSA')

    translate_group.add_argument(
        '--entry-points',
        metavar='PROC',
        nargs='+',
        default=['main'],
        help='specify top-level procedures [default: %(default)s]')

    translate_group.add_argument(
        '--checked-functions',
        metavar='PROC',
        nargs='+',
        default=[],
        help='''specify functions on which to do property checking.
                These can be specified as extended regular expressions.
                NOTE: a regular expression must match the entire
                function name. [default: everything]''')

    translate_group.add_argument(
        '--check',
        metavar='PROPERTY',
        nargs='+',
        choices=list(VProperty),
        default=VProperty.NONE,
        type=VProperty.argparse,
        action=PropertyAction,
        help='''select properties to check
                [choices: %(choices)s; default: assertions]
                (note that memory-safety is the union of valid-deref,
                valid-free, memleak)''')

    translate_group.add_argument(
        '--llvm-assumes',
        choices=[
            'none',
            'use',
            'check'],
        default='none',
        help='''optionally enable generation of Boogie assume statements from
                LLVM assume statements (none=no generation [default],
                use=generate assume statements,
                check=check assume statements)''')

    translate_group.add_argument(
        '--float',
        action="store_true",
        default=False,
        help='enable bit-precise floating-point functions')

    translate_group.add_argument(
        '--strings',
        action='store_true',
        default=False,
        help='enable support for string')

    translate_group.add_argument(
        '--fail-on-loop-exit',
        action='store_true',
        default=False,
        help='''Add assert false to the end of each loop
                (useful for deciding how much unroll to use)''')

    verifier_group = parser.add_argument_group('verifier options')

    verifier_group.add_argument(
        '--verifier',
        choices=[
            'boogie',
            'corral',
            'symbooglix',
            'svcomp'],
        default='corral',
        help='back-end verification engine')

    verifier_group.add_argument('--solver',
                                choices=['z3', 'cvc4', "yices2"], default='z3',
                                help='back-end SMT solver')

    verifier_group.add_argument(
        '--unroll',
        metavar='N',
        default='1',
        type=lambda x: (int(x) if int(x) > 0 else
                        parser.error('Unroll bound has to be positive.')),
        help='loop/recursion unroll bound [default: %(default)s]')

    verifier_group.add_argument(
        '--loop-limit',
        metavar='N',
        default='1',
        type=int,
        help='upper bound on minimum loop iterations [default: %(default)s]')

    verifier_group.add_argument(
        '--context-bound',
        metavar='K',
        default='1',
        type=int,
        help='''bound on the number of thread contexts in Corral
                [default: %(default)s]''')

    verifier_group.add_argument(
        '--verifier-options',
        metavar='OPTIONS',
        default='',
        help='''additional verifier arguments
                (e.g., --verifier-options="/trackAllVars /staticInlining")''')

    verifier_group.add_argument(
        '--time-limit',
        metavar='N',
        default='1200',
        type=int,
        help='verifier time limit, in seconds [default: %(default)s]')

    verifier_group.add_argument(
        '--max-violations',
        metavar='N',
        default='1',
        type=int,
        help='maximum reported assertion violations [default: %(default)s]')

    verifier_group.add_argument(
        '--svcomp-property',
        metavar='FILE',
        default=None,
        type=str,
        help='load SVCOMP property to check from FILE')

    verifier_group.add_argument(
        '--modular',
        action="store_true",
        default=False,
        help='''enable contracts-based modular deductive verification
                (uses Boogie)''')

    verifier_group.add_argument(
        '--replay',
        action="store_true",
        default=False,
        help='enable replay of error trace with test harness.')

    plugins_group = parser.add_argument_group('plugins')

    plugins_group.add_argument(
        '--transform-bpl',
        metavar='COMMAND',
        default=None,
        type=str,
        help='transform generated Boogie code via COMMAND')

    plugins_group.add_argument(
        '--transform-out',
        metavar='COMMAND',
        default=None,
        type=str,
        help='transform verifier output via COMMAND')

    args = parser.parse_args()

    if not args.bc_file:
        args.bc_file = temporary_file('a', '.bc', args)

    if not args.linked_bc_file:
        args.linked_bc_file = temporary_file('b', '.bc', args)

    if not args.bpl_file:
        args.bpl_file = 'a.bpl' if args.no_verify else temporary_file(
            'a', '.bpl', args)

    if args.check == VProperty.NONE:
        args.check = VProperty.ASSERTIONS

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
            ll = temporary_file(
                os.path.splitext(
                    os.path.basename(src))[0],
                '.ll',
                args)
            try_command([llvm_exact_bin('llvm-dis'), '-o', ll, src])
            src = ll
        if os.path.splitext(src)[1] == '.ll':
            with open(src, 'r') as f:
                for line in f:
                    triple = re.findall('^target triple = "(.*)"', line)
                    if len(triple) > 0:
                        args.clang_options += (" -target %s" % triple[0])
                        break


def frontend(args):
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
    cmd += ['-sea-dsa=ci']
    # This flag can lead to unsoundness in Rust regressions.
    # cmd += ['-sea-dsa-type-aware']
    if sys.stdout.isatty():
        cmd += ['-colored-warnings']
    cmd += ['-source-loc-syms']
    for ep in args.entry_points:
        cmd += ['-entry-points', ep]
    for cf in args.checked_functions:
        cmd += ['-checked-functions', cf]
    if args.debug:
        cmd += ['-debug']
    if args.debug_only:
        cmd += ['-debug-only', args.debug_only]
    if args.ll_file:
        cmd += ['-ll', args.ll_file]
    if "impls" in args.mem_mod:
        cmd += ['-mem-mod-impls']
    if args.static_unroll:
        cmd += ['-static-unroll']
    if args.integer_encoding == 'bit-vector':
        cmd += ['-bit-precise']
    if args.integer_encoding == 'wrapped-integer':
        cmd += ['-wrapped-integer-encoding']
    if args.timing_annotations:
        cmd += ['-timing-annotations']
    if args.pointer_encoding == 'bit-vector':
        cmd += ['-bit-precise-pointers']
    if args.no_byte_access_inference:
        cmd += ['-no-byte-access-inference']
    if args.rewrite_bitwise_ops:
        cmd += ['-rewrite-bitwise-ops']
    if args.no_memory_splitting:
        cmd += ['-no-memory-splitting']
    if args.check.contains_mem_safe_props():
        cmd += ['-memory-safety']
    if VProperty.INTEGER_OVERFLOW in args.check:
        cmd += ['-integer-overflow']
    if VProperty.RUST_PANICS in args.check:
        cmd += ['-rust-panics']
    if args.fail_on_loop_exit:
        cmd += ['-fail-on-loop-exit']
    if args.llvm_assumes:
        cmd += ['-llvm-assumes=' + args.llvm_assumes]
    if args.float:
        cmd += ['-float']
    if args.modular:
        cmd += ['-modular']
    try_command(cmd, console=True)
    annotate_bpl(args)
    memsafety_subproperty_selection(args)
    transform_bpl(args)


def procedure_annotation(name, args):
    if name in args.entry_points:
        return "{:entrypoint}"
    elif (args.modular and
          re.match("|".join(inlined_procedures()).replace("$", r"\$"), name)):
        return "{:inline 1}"
    elif (not args.modular) and args.verifier == 'boogie':
        return ("{:inline %s}" % args.unroll)
    else:
        return ""


def annotate_bpl(args):
    """Annotate the Boogie source file with additional metadata."""

    proc_decl = re.compile(r'procedure\s+([^\s(]*)\s*\(')

    with open(args.bpl_file, 'r+') as f:
        bpl = "// generated by SMACK version %s for %s\n" % (
            VERSION, args.verifier)
        bpl += "// via %s\n\n" % " ".join(sys.argv)
        bpl += proc_decl.sub(
            lambda m: ("procedure %s %s(" %
                       (procedure_annotation(m.group(1), args), m.group(1))),
            f.read())
        f.seek(0)
        f.truncate()
        f.write(bpl)


def memsafety_subproperty_selection(args):
    if VProperty.MEMORY_SAFETY in args.check:
        return

    selected_props = [p.boogie_attr() for p in VProperty.mem_safe_subprops()
                      if p in args.check]

    def replace_assertion(m):
        if len(selected_props) > 0:
            if m.group(2) and m.group(3) in selected_props:
                attrib = m.group(2)
                expr = m.group(4)
            else:
                attrib = ''
                expr = 'true'
            return m.group(1) + attrib + expr + ";"
        else:
            return m.group(0)

    with open(args.bpl_file, 'r+') as f:
        lines = f.readlines()
        f.seek(0)
        f.truncate()
        for line in lines:
            line = re.sub(
                r'^(\s*assert\s*)({:(.+)})?(.+);',
                replace_assertion,
                line)
            f.write(line)


def transform_bpl(args):
    if args.transform_bpl:
        with open(args.bpl_file, 'r+') as bpl:
            old = bpl.read()
            bpl.seek(0)
            bpl.truncate()
            tx = subprocess.Popen(
                shlex.split(
                    args.transform_bpl),
                stdin=subprocess.PIPE,
                stdout=bpl,
                universal_newlines=True)
            tx.communicate(input=old)


def transform_out(args, old):
    out = old
    if args.transform_out:
        tx = subprocess.Popen(shlex.split(args.transform_out),
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, universal_newlines=True)
        out, err = tx.communicate(input=old)
    return out


def verification_result(verifier_output, verifier):
    if re.search(
        r'[1-9]\d* time out|Z3 ran out of resources|timed out|ERRORS_TIMEOUT',
            verifier_output):
        return VResult.TIMEOUT
    elif re.search((r'[1-9]\d* verified, 0 errors?|no bugs|'
                    r'NO_ERRORS_NO_TIMEOUT'), verifier_output):
        return VResult.VERIFIED
    elif re.search((r'\d* verified, [1-9]\d* errors?|can fail|'
                    r'ERRORS_NO_TIMEOUT'), verifier_output):
        attr = None
        attr_pat = r'assert {:(.+)}'

        if verifier == 'corral':
            corral_af_msg = re.search(r'ASSERTION FAILS %s' % attr_pat,
                                      verifier_output)
            if corral_af_msg:
                attr = corral_af_msg.group(1)

        elif verifier == 'boogie':
            boogie_af_msg = re.search(
                r'([\w#$~%.\/-]+)\((\d+),\d+\): '
                r'Error: This assertion might not hold', verifier_output)
            if boogie_af_msg:
                if re.match('.*[.]bpl$', boogie_af_msg.group(1)):
                    line_no = int(boogie_af_msg.group(2))
                    with open(boogie_af_msg.group(1), 'r') as f:
                        assert_line = re.search(
                                      attr_pat,
                                      f.read().splitlines(True)[line_no - 1])
                        if assert_line:
                            attr = assert_line.group(1)
        else:
            print('Warning: Unable to decide error type.')

        if attr is not None:
            for p in (VProperty.mem_safe_subprops()
                      + [VProperty.INTEGER_OVERFLOW]
                      + [VProperty.RUST_PANICS]):
                if p.boogie_attr() == attr:
                    return p.result()

        return VResult.ASSERTION_FAILURE
    else:
        return VResult.UNKNOWN


def verify_bpl(args):
    """Verify the Boogie source file with a back-end verifier."""

    if args.verifier == 'svcomp':
        verify_bpl_svcomp(args)
        return

    elif args.verifier == 'boogie' or args.modular:
        command = ["boogie"]
        command += [args.bpl_file]
        command += ["/doModSetAnalysis"]
        command += ["/useArrayTheory"]
        command += ["/timeLimit:%s" % args.time_limit]
        command += ["/errorLimit:%s" % args.max_violations]
        command += ["/proverOpt:O:smt.array.extensional=false"]
        command += ["/proverOpt:O:smt.qi.eager_threshold=100"]
        command += ["/proverOpt:O:smt.arith.solver=2"]
        if not args.modular:
            command += ["/loopUnroll:%d" % args.unroll]
        if args.solver == 'cvc4':
            command += ["/proverOpt:SOLVER=cvc4"]
        elif args.solver == 'yices2':
            command += ["/proverOpt:SOLVER=Yices2"]

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
        command += ["/bopt:proverOpt:O:smt.qi.eager_threshold=100"]
        command += ["/bopt:proverOpt:O:smt.arith.solver=2"]
        if args.solver == 'cvc4':
            command += ["/bopt:proverOpt:SOLVER=cvc4"]
        elif args.solver == 'yices2':
            command += ["/bopt:proverOpt:SOLVER=Yices2"]

    elif args.verifier == 'symbooglix':
        command = ['symbooglix']
        command += [args.bpl_file]
        command += ["--file-logging=0"]
        command += ["--entry-points=%s" % ",".join(args.entry_points)]
        command += ["--timeout=%d" % args.time_limit]
        command += ["--max-loop-depth=%d" % args.unroll]

    if args.verifier_options:
        command += args.verifier_options.split()

    verifier_output = try_command(command, timeout=args.time_limit)
    verifier_output = transform_out(args, verifier_output)
    result = verification_result(verifier_output, args.verifier)

    if args.json_file:
        with open(args.json_file, 'w') as f:
            f.write(json_output_str(result, verifier_output, args.verifier))

    if result in VResult.ERROR:
        error = error_trace(verifier_output, args.verifier)

        if args.error_file:
            with open(args.error_file, 'w') as f:
                f.write(error)

        if not args.quiet:
            print(error)

        if args.replay:
            replay_error_trace(verifier_output, args)
    print(result.message(args))
    return result.return_code()


def clean_up_upon_sigterm(main):
    def handler(signum, frame):
        remove_temp_files()
        sys.exit(0)
    signal.signal(signal.SIGTERM, handler)
    return main


@clean_up_upon_sigterm
def main():
    try:
        global args
        args = arguments()

        target_selection(args)

        if not args.quiet:
            print("SMACK program verifier version %s" % VERSION)

        frontend(args)

        if args.no_verify:
            if not args.quiet:
                print("SMACK generated %s" % args.bpl_file)
        else:
            return_code = verify_bpl(args)
            sys.exit(return_code)

    except KeyboardInterrupt:
        sys.exit("SMACK aborted by keyboard interrupt.")

    finally:
        remove_temp_files()
