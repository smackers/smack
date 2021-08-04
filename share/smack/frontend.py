import os
import sys
import re
import json
from .utils import temporary_file, try_command, temporary_directory,\
    llvm_exact_bin
from .versions import RUST_VERSION

# Needed for cargo operations
try:
    import toml
except ImportError:
    pass


def languages():
    """A dictionary of languages per file extension."""
    return {
        'c': 'c',
        'i': 'c',
        'cc': 'cxx',
        'cpp': 'cxx',
        'm': 'objc',
        'd': 'd',
        'json': 'json',
        'svcomp': 'svcomp',
        'bc': 'llvm',
        'll': 'llvm',
        'bpl': 'boogie',
        'f': 'fortran',
        'for': 'fortran',
        'f90': 'fortran',
        'f95': 'fortran',
        'f03': 'fortran',
        'rs': 'rust',
        'toml': 'cargo',
    }


def frontends():
    """A dictionary of front-ends per language."""

    # Avoid circular import
    from .svcomp.utils import svcomp_frontend

    return {
        'c': clang_frontend,
        'cxx': clang_plusplus_frontend,
        'objc': clang_objc_frontend,
        'd': d_frontend,
        'json': json_compilation_database_frontend,
        'svcomp': svcomp_frontend,
        'llvm': llvm_frontend,
        'boogie': boogie_frontend,
        'fortran': fortran_frontend,
        'rust': rust_frontend,
        'cargo': cargo_frontend,
    }


def extra_libs():
    """A dictionary of extra SMACK libraries required by languages."""
    return {
        'fortran': fortran_build_libs,
        'cxx': cplusplus_build_libs,
        'rust': rust_build_libs,
        # coming soon - libraries for OBJC, Rust, Swift, etc.
    }


def smack_root():
    return os.path.dirname(os.path.dirname(os.path.abspath(sys.argv[0])))


def smack_header_path():
    return os.path.join(smack_root(), 'share', 'smack', 'include')


def smack_headers(args):
    paths = []
    paths.append(smack_header_path())
    return paths


def smack_lib():
    return os.path.join(smack_root(), 'share', 'smack', 'lib')


def extern_entry_points(args, bcs):
    new_bcs = []
    for bc in bcs:
        new_bc = temporary_file(
            os.path.splitext(
                os.path.basename(bc))[0],
            '.bc',
            args)
        cmd = ['-in', bc, '-out', new_bc]
        for ep in args.entry_points:
            cmd += ['-entry-points', ep]

        try_command(['extern-statics'] + cmd, console=True)
        new_bcs.append(new_bc)
    return new_bcs


def default_clang_compile_command(args, lib=False):
    cmd = [
           llvm_exact_bin('clang'),
           '-c',
           '-emit-llvm',
           '-O0',
           '-g',
           '-gcolumn-info'
          ]
    # Starting from LLVM 5.0, we need the following two options
    # in order to enable optimization passes.
    # See: https://stackoverflow.com/a/46753969.
    cmd += ['-Xclang', '-disable-O0-optnone']
    cmd += ['-I' + path for path in smack_headers(args)]
    cmd += args.clang_options.split()
    cmd += ['-DMEMORY_MODEL_' + args.mem_mod.upper().replace('-', '_')]

    from .top import VProperty

    if args.check.contains_mem_safe_props():
        cmd += ['-DMEMORY_SAFETY']
    if VProperty.INTEGER_OVERFLOW in args.check:
        cmd += (['-fsanitize=signed-integer-overflow,shift']
                if not lib else ['-DSIGNED_INTEGER_OVERFLOW_CHECK'])
    if VProperty.ASSERTIONS not in args.check:
        cmd += ['-DDISABLE_SMACK_ASSERTIONS']
    if args.float:
        cmd += ['-DFLOAT_ENABLED']
    if args.pthread:
        cmd += ['-DSMACK_MAX_THREADS=' + str(args.max_threads)]
    if args.integer_encoding == 'bit-vector':
        cmd += ['-DBIT_PRECISE']
    if sys.stdout.isatty():
        cmd += ['-fcolor-diagnostics']
    return cmd


def compile_to_bc(input_file, compile_command, args):
    """Compile a source file to LLVM IR."""
    bc = temporary_file(
        os.path.splitext(
            os.path.basename(input_file))[0],
        '.bc',
        args)
    try_command(compile_command + ['-o', bc, input_file], console=True)
    return bc


def d_compile_to_bc(input_file, compile_command, args):
    """Compile a D source file to LLVM IR."""
    bc = temporary_file(
        os.path.splitext(
            os.path.basename(input_file))[0],
        '.bc',
        args)
    try_command(compile_command + ['-of=' + bc, input_file], console=True)
    return bc


def fortran_compile_to_bc(input_file, compile_command, args):
    """Compile a FORTRAN source file to LLVM IR."""

    #  This method only exists as a hack to get flang to work
    #  with SMACK. When we update to the latest flang on LLVM 5,
    #  this method will no longer be necessary. The hack is
    #  self-contained in this method.

    #  The Debug Info Version in flang is incompatible with
    #  the version that clang uses. The workaround is to use
    #  sed to change the file so llvm-link gives a warning
    #  and not an error.

    # compile to human-readable format in order to tweak the IR
    compile_command[1] = '-S'
    ll = temporary_file(
        os.path.splitext(
            os.path.basename(input_file))[0],
        '.ll',
        args)
    try_command(compile_command + ['-o', ll, input_file], console=True)
    # change the throw level of 'Debug Info Version' from error to warning in
    # the IR
    try_command(
        ['sed',
         '-i',
         's/i32 1, !\"Debug Info Version\"/i32 2, !\"Debug Info Version\"/g',
         ll])
    try_command([llvm_exact_bin('llvm-as'), ll])
    try_command(['rm', ll])
    bc = '.'.join(ll.split('.')[:-1] + ['bc'])
    return bc


# Frontend functions here

def llvm_frontend(input_file, args):
    """Return LLVM IR file. Exists for symmetry with other frontends."""

    return input_file


def clang_frontend(input_file, args):
    """Generate LLVM IR from C-language source(s)."""

    compile_command = default_clang_compile_command(args)
    return compile_to_bc(input_file, compile_command, args)


def clang_plusplus_frontend(input_file, args):
    """Generate LLVM IR from C++ language source(s)."""
    compile_command = default_clang_compile_command(args)
    compile_command[0] = llvm_exact_bin('clang++')
    return compile_to_bc(input_file, compile_command, args)


def clang_objc_frontend(input_file, args):
    """Generate LLVM IR from Objective-C language source(s)."""

    compile_command = default_clang_compile_command(args)
    if sys.platform in ['linux', 'linux2']:
        objc_flags = try_command(['gnustep-config', '--objc-flags'])
        compile_command += objc_flags.split()
    elif sys.platform == 'darwin':
        sys.exit("Objective-C not yet supported on macOS")
    else:
        sys.exit("Objective-C not supported for this operating system.")
    return compile_to_bc(input_file, compile_command, args)


def d_frontend(input_file, args):
    """Generate Boogie code from D programming language source(s)."""

    # note: -g and -O0 are not used here.
    # Right now, it works, and with these options, smack crashes.
    compile_command = ['ldc2', '-output-ll']
    compile_command += ['-I=' + path for path in smack_headers(args)]
    args.entry_points += ['_Dmain']
    return d_compile_to_bc(input_file, compile_command, args)


def fortran_frontend(input_file, args):
    """Generate Boogie code from Fortran language source(s)."""

    #  For a fortran file that includes smack.f90 as a module,
    #  it will not compile unless the file 'smack.mod' exists
    #  in the working directory. 'smack.mod' is a build artifact
    #  of compiling smack.f90. Therefore, the solution is to
    #  compile smack.f90 before the source files.
    fortran_build_libs(args)
    #  The result of this computation will be discarded when SMACK
    #  builds it's libraries later.

    # replace the default entry point with the fortran default 'MAIN_'
    args.entry_points += ['MAIN_']

    compile_command = default_clang_compile_command(args)
    compile_command[0] = 'flang'

    return fortran_compile_to_bc(input_file, compile_command, args)


def boogie_frontend(input_file, args):
    """Pass Boogie code to the verifier."""
    if len(args.input_files) > 1:
        raise RuntimeError("Expected a single Boogie file.")

    with open(args.bpl_file, 'a+') as out:
        with open(input_file) as f:
            out.write(f.read())


def json_compilation_database_frontend(input_file, args):
    """Generate Boogie code from a JSON compilation database."""

    if len(args.input_files) > 1:
        raise RuntimeError("Expected a single JSON compilation database.")

    output_flags = re.compile(r"-o ([^ ]*)[.]o\b")
    optimization_flags = re.compile(r"-O[1-9]\b")

    with open(input_file) as f:
        for cc in json.load(f):
            if 'objects' in cc:
                # TODO what to do when there are multiple linkings?
                bit_codes = [re.sub('[.]o$', '.bc', f) for f in cc['objects']]
                try_command([
                             llvm_exact_bin('llvm-link'),
                             '-o',
                             args.bc_file
                            ] + bit_codes)
                try_command([
                             llvm_exact_bin('llvm-link'),
                             '-o',
                             args.linked_bc_file,
                             args.bc_file
                            ] + default_build_libs(args))

            else:
                command = cc['command']
                command = output_flags.sub(r"-o \1.bc", command)
                command = optimization_flags.sub("-O0", command)
                command = command + " -emit-llvm"
                try_command(command.split(), cc['directory'], console=True)
    # import here to avoid a circular import
    from .top import llvm_to_bpl
    llvm_to_bpl(args)


def default_cargo_compile_command(args):
    compile_command = [
        'cargo',
        '+' + RUST_VERSION,
        'build']
    return compile_command + args


def cargo_frontend(input_file, args):
    """Generate LLVM bitcode from a cargo build."""

    def find_target(config, options=None):
        target_name = config['package']['name']
        # TODO: Shaobo: target selection can be done via Cargo options.
        # But we don't capture Cargo options for now.
        if options is None:
            if 'lib' in config and 'name' in config['lib']:
                target_name = config['lib']['name']
        return target_name.replace('-', '_')

    targetdir = temporary_directory(
        os.path.splitext(
            os.path.basename(input_file))[0],
        None,
        args)
    rustargs = (default_rust_compile_args(args) +
                ['--emit=llvm-bc', '-Clto', '-Cembed-bitcode=yes'])
    compile_command = default_cargo_compile_command(
        ['--target-dir', targetdir, '--manifest-path', input_file])
    try_command(compile_command, console=True,
                env={'RUSTFLAGS': " ".join(rustargs)})

    target_name = find_target(toml.load(input_file))

    # Find the name of the crate's bc file
    bcbase = targetdir + '/debug/deps/'
    entries = os.listdir(bcbase)
    bcs = []

    for entry in entries:
        if entry.startswith(target_name + '-') and entry.endswith('.bc'):
            bcs.append(bcbase + entry)

    bc_file = temporary_file(
        os.path.splitext(
            os.path.basename(input_file))[0],
        '.bc',
        args)
    try_command([llvm_exact_bin('llvm-link')] + bcs + ['-o', bc_file])
    return bc_file


def default_rust_compile_args(args):
    return ['-A',
            'unused-imports',
            '-C',
            'opt-level=0',
            '-C',
            'no-prepopulate-passes',
            '-g',
            '--cfg',
            'verifier="smack"',
            '-C',
            'passes=name-anon-globals']


def default_rust_compile_command(args):
    compile_command = (['rustc', '+' + RUST_VERSION] +
                       default_rust_compile_args(args))
    return compile_command + args


def rust_build_rlib(input_file, args):
    compile_command = default_rust_compile_command(
        ['--crate-type', 'rlib,lib'])
    rlib = temporary_file(
        'lib' +
        os.path.splitext(
            os.path.basename(input_file))[0],
        '.rlib',
        args)
    try_command(compile_command + ['-o', rlib, input_file], console=True)
    return rlib


def rust_frontend(input_file, args):
    """Generate Boogie code from Rust programming language source(s)."""
    rlib = rust_build_rlib(smack_lib() + '/smack.rs', args)
    compile_command = default_rust_compile_command(
        ['--emit=llvm-bc', '--extern', 'smack=' + rlib])

    return compile_to_bc(input_file, compile_command, args)

# Build libs functions here


def default_build_libs(args):
    """Generate LLVM bitcodes for SMACK libraries."""
    bitcodes = []
    libs = ['smack.c', 'stdlib.c', 'errno.c', 'smack-rust.c']

    if args.pthread:
        libs += ['pthread.c']

    if args.strings:
        libs += ['string.c']

    if args.float:
        libs += ['math.c']
        libs += ['fenv.c']

    compile_command = default_clang_compile_command(args, True)
    for c in [os.path.join(smack_lib(), c) for c in libs]:
        bc = compile_to_bc(c, compile_command, args)
        bitcodes.append(bc)

    return bitcodes


def fortran_build_libs(args):
    """Generate FORTRAN-specific LLVM bitcodes for SMACK libraries."""

    bitcodes = []
    libs = ['smack.f90']

    compile_command = default_clang_compile_command(args)
    compile_command[0] = 'flang'

    for c in [os.path.join(smack_lib(), c) for c in libs]:
        bc = fortran_compile_to_bc(c, compile_command, args)
        bitcodes.append(bc)

    return bitcodes


def cplusplus_build_libs(args):
    """Generate C++ specific LLVM bitcodes for SMACK libraries."""

    bitcodes = []
    libs = ['smack.cpp']

    compile_command = default_clang_compile_command(args, True)
    compile_command[0] = llvm_exact_bin('clang++')

    for c in [os.path.join(smack_lib(), c) for c in libs]:
        bc = compile_to_bc(c, compile_command, args)
        bitcodes.append(bc)

    return bitcodes


def rust_build_libs(args):
    """Generate Rust specific LLVM bitcodes for SMACK libraries."""
    bitcodes = []
    libs = ['smack.rs']

    compile_command = default_rust_compile_command(
        ['--emit=llvm-bc', '--crate-type', 'lib'])

    for c in [os.path.join(smack_lib(), c) for c in libs]:
        bc = compile_to_bc(c, compile_command, args)
        bitcodes.append(bc)

    return bitcodes

# llvm link files


def link_bc_files(bitcodes, libs, args):
    """Link generated LLVM bitcode and relevant smack libraries."""

    smack_libs = default_build_libs(args)
    for build_lib in libs:
        smack_libs += build_lib(args)

    bitcodes = extern_entry_points(args, bitcodes)
    try_command([llvm_exact_bin('llvm-link'), '-o', args.bc_file] + bitcodes)
    try_command([llvm_exact_bin('llvm-link'), '-o', args.linked_bc_file,
                 args.bc_file] + smack_libs)

    # import here to avoid a circular import
    from .top import llvm_to_bpl
    llvm_to_bpl(args)
