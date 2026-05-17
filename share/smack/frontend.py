import contextlib
import json
import os
import re
import shutil
import sys
from pathlib import Path

from .utils import (
    llvm_exact_bin,
    smack_headers,
    smack_lib,
    temporary_directory,
    temporary_file,
    try_command,
)
from .versions import RUST_VERSION

# Needed for cargo operations
with contextlib.suppress(ImportError):
    import toml


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


def extern_entry_points(args, bcs):
    new_bcs = []
    for bc in bcs:
        new_bc = temporary_file(Path(bc).stem, '.bc', args)
        cmd = ['-in', bc, '-out', new_bc]
        for ep in args.entry_points:
            cmd += ['-entry-points', ep]

        try_command(['extern-statics', *cmd], console=True)
        new_bcs.append(new_bc)
    return new_bcs


def default_clang_compile_command(args, lib=False):
    cmd = [
        llvm_exact_bin('clang'),
        '-c',
        '-emit-llvm',
        '-O0',
        '-g',
        '-gcolumn-info',
        '-Wno-error=implicit-function-declaration',
        '-Wno-error=implicit-int',
        '-Wno-error=int-conversion',
        '-Wno-error=incompatible-pointer-types',
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
        cmd += (
            ['-fsanitize=signed-integer-overflow,shift']
            if not lib
            else ['-DSIGNED_INTEGER_OVERFLOW_CHECK']
        )
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
    bc = temporary_file(Path(input_file).stem, '.bc', args)
    try_command([*compile_command, '-o', bc, input_file], console=True)
    return bc


def d_compile_to_bc(input_file, compile_command, args):
    """Compile a D source file to LLVM IR."""
    bc = temporary_file(Path(input_file).stem, '.bc', args)
    try_command([*compile_command, '-of=' + bc, input_file], console=True)
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
    ll = temporary_file(Path(input_file).stem, '.ll', args)
    try_command([*compile_command, '-o', ll, input_file], console=True)
    # change the throw level of 'Debug Info Version' from error to warning in
    # the IR
    try_command(['sed', '-i', 's/i32 1, !"Debug Info Version"/i32 2, !"Debug Info Version"/g', ll])
    try_command([llvm_exact_bin('llvm-as'), ll])
    try_command(['rm', ll])
    bc = '.'.join([*ll.split('.')[:-1], 'bc'])
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

    with Path(args.bpl_file).open('a+') as out, Path(input_file).open() as f:
        out.write(f.read())


def json_compilation_database_frontend(input_file, args):
    """Generate Boogie code from a JSON compilation database."""

    if len(args.input_files) > 1:
        raise RuntimeError("Expected a single JSON compilation database.")

    output_flags = re.compile(r"-o ([^ ]*)[.]o\b")
    optimization_flags = re.compile(r"-O[1-9]\b")

    with Path(input_file).open() as f:
        for cc in json.load(f):
            if 'objects' in cc:
                # TODO what to do when there are multiple linkings?
                bit_codes = [re.sub('[.]o$', '.bc', f) for f in cc['objects']]
                try_command([llvm_exact_bin('llvm-link'), '-o', args.bc_file, *bit_codes])
                try_command(
                    [
                        llvm_exact_bin('llvm-link'),
                        '-o',
                        args.linked_bc_file,
                        args.bc_file,
                        *default_build_libs(args),
                    ]
                )

            else:
                command = cc['command']
                command = output_flags.sub(r"-o \1.bc", command)
                command = optimization_flags.sub("-O0", command)
                command = command + " -emit-llvm"
                try_command(command.split(), cc['directory'], console=True)
    if not getattr(args, 'skip_llvm_to_bpl', False):
        # import here to avoid a circular import
        from .top import llvm_to_bpl

        llvm_to_bpl(args)

    return args.linked_bc_file


def default_cargo_compile_command(args):
    compile_command = ['cargo', '+' + RUST_VERSION, 'build']
    if os.environ.get('SMACK_CARGO_ALLOW_NETWORK') != '1':
        compile_command.append('--offline')
    return compile_command + args


def cargo_frontend(input_file, args):
    """Generate LLVM bitcode from a cargo build."""

    def copy_cargo_package(manifest):
        package_dir = Path(manifest).resolve().parent
        work_dir = temporary_directory(package_dir.stem, None, args)
        package_copy = str(Path(work_dir) / 'package')
        shutil.copytree(
            package_dir, package_copy, ignore=shutil.ignore_patterns('target', 'Cargo.lock')
        )
        return str(Path(package_copy) / Path(manifest).name)

    def verifier_smack_crate(work_dir):
        crate_dir = str(Path(work_dir) / 'smack')
        shutil.copytree(
            smack_lib(),
            crate_dir,
            ignore=shutil.ignore_patterns('target', 'Cargo.lock', '*.a', '*.bc', '*.o'),
        )

        manifest = Path(crate_dir) / 'Cargo.toml'
        config = toml.load(manifest)
        config.setdefault('build-dependencies', {})['cc'] = '=1.0.72'
        with manifest.open('w') as f:
            toml.dump(config, f)

        return crate_dir

    input_file = copy_cargo_package(input_file)
    config = toml.load(input_file)
    smack_crate = verifier_smack_crate(str(Path(input_file).parent))
    if isinstance(config.get('dependencies'), dict):
        smack_dep = config['dependencies'].get('smack')
        if isinstance(smack_dep, dict) and 'path' in smack_dep:
            smack_dep['path'] = smack_crate
            with Path(input_file).open('w') as f:
                toml.dump(config, f)

    def find_target(config, options=None):
        target_name = config['package']['name']
        # TODO: Shaobo: target selection can be done via Cargo options.
        # But we don't capture Cargo options for now.
        if options is None and 'lib' in config and 'name' in config['lib']:
            target_name = config['lib']['name']
        return target_name.replace('-', '_')

    targetdir = temporary_directory(Path(input_file).stem, None, args)
    rustargs = [*default_rust_compile_args(args), '--emit=llvm-bc', '-Clto', '-Cembed-bitcode=yes']
    compile_command = default_cargo_compile_command(
        ['--target-dir', targetdir, '--manifest-path', input_file]
    )
    try_command(compile_command, console=True, env={'RUSTFLAGS': " ".join(rustargs)})

    target_name = find_target(config)

    # Find the name of the crate's bc file
    bcbase = targetdir + '/debug/deps/'
    entries = os.listdir(bcbase)
    bcs = []

    for entry in entries:
        if entry.startswith(target_name + '-') and entry.endswith('.bc'):
            bcs.append(bcbase + entry)

    bc_file = temporary_file(Path(input_file).stem, '.bc', args)
    try_command([llvm_exact_bin('llvm-link'), *bcs, '-o', bc_file])
    return bc_file


def default_rust_compile_args(args):
    return [
        '-A',
        'unused-imports',
        '-C',
        'opt-level=0',
        '-C',
        'no-prepopulate-passes',
        '-C',
        'debuginfo=0',
        '--cfg',
        'verifier="smack"',
        '-C',
        'passes=name-anon-globals',
        '-C',
        'panic=abort',
    ]


def default_rust_compile_command(args):
    compile_command = ['rustc', '+' + RUST_VERSION, *default_rust_compile_args(args)]
    return compile_command + args


def rust_build_rlib(input_file, args):
    compile_command = default_rust_compile_command(['--crate-type', 'rlib,lib'])
    rlib = temporary_file('lib' + Path(input_file).stem, '.rlib', args)
    try_command([*compile_command, '-o', rlib, input_file], console=True)
    return rlib


def rust_frontend(input_file, args):
    """Generate Boogie code from Rust programming language source(s)."""
    rlib = rust_build_rlib(smack_lib() + '/smack.rs', args)
    compile_command = default_rust_compile_command(['--emit=llvm-bc', '--extern', 'smack=' + rlib])

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
    for c in [str(Path(smack_lib()) / c) for c in libs]:
        bc = compile_to_bc(c, compile_command, args)
        bitcodes.append(bc)

    return bitcodes


def fortran_build_libs(args):
    """Generate FORTRAN-specific LLVM bitcodes for SMACK libraries."""

    bitcodes = []
    libs = ['smack.f90']

    compile_command = default_clang_compile_command(args)
    compile_command[0] = 'flang'

    for c in [str(Path(smack_lib()) / c) for c in libs]:
        bc = fortran_compile_to_bc(c, compile_command, args)
        bitcodes.append(bc)

    return bitcodes


def cplusplus_build_libs(args):
    """Generate C++ specific LLVM bitcodes for SMACK libraries."""

    bitcodes = []
    libs = ['smack.cpp']

    compile_command = default_clang_compile_command(args, True)
    compile_command[0] = llvm_exact_bin('clang++')

    for c in [str(Path(smack_lib()) / c) for c in libs]:
        bc = compile_to_bc(c, compile_command, args)
        bitcodes.append(bc)

    return bitcodes


def rust_build_libs(args):
    """Generate Rust specific LLVM bitcodes for SMACK libraries."""
    bitcodes = []
    libs = ['smack.rs']

    compile_command = default_rust_compile_command(['--emit=llvm-bc', '--crate-type', 'lib'])

    for c in [str(Path(smack_lib()) / c) for c in libs]:
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
    try_command([llvm_exact_bin('llvm-link'), '-o', args.bc_file, *bitcodes])
    try_command([llvm_exact_bin('llvm-link'), '-o', args.linked_bc_file, args.bc_file, *smack_libs])

    if not getattr(args, 'skip_llvm_to_bpl', False):
        # import here to avoid a circular import
        from .top import llvm_to_bpl

        llvm_to_bpl(args)

    return args.linked_bc_file
