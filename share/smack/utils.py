import os
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path
from threading import Timer

from .versions import LLVM_SHORT_VERSION

temporary_files: list[str] = []


def temporary_file(prefix, extension, args):
    f, name = tempfile.mkstemp(extension, prefix + '-', Path.cwd(), True)
    os.close(f)
    if not args.debug:
        temporary_files.append(name)
    return name


def temporary_directory(prefix, extension, args):
    name = tempfile.mkdtemp(extension, prefix + '-', Path.cwd())
    if not args.debug:
        temporary_files.append(name)
    return name


def remove_temp_files():
    for f in temporary_files:
        p = Path(f)
        if p.is_file():
            p.unlink()
        elif p.is_dir():
            shutil.rmtree(f)


def timeout_killer(proc, timed_out):
    if not timed_out[0]:
        timed_out[0] = True
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)


def try_command(cmd, cwd=None, console=False, timeout=None, env=None):
    # Lazy import to avoid a load-time cycle with top.py (which itself
    # re-exports symbols from pipeline.translate which imports utils).
    from . import top

    args = top.args  # type: ignore[attr-defined]
    console = (console or args.verbose or args.debug) and not args.quiet
    filelog = args.debug
    output = ''
    proc = None
    timer = None
    if env is not None:
        for k, v in env.items():
            os.putenv(k, v)
    try:
        if args.debug:
            print("Running {}".format(" ".join(cmd)))

        proc = subprocess.Popen(
            cmd,
            cwd=cwd,
            preexec_fn=os.setsid,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            universal_newlines=True,
        )

        if timeout:
            timed_out = [False]
            timer = Timer(timeout, timeout_killer, [proc, timed_out])
            timer.start()

        if console:
            assert proc.stdout is not None
            while True:
                line = proc.stdout.readline()
                if line:
                    output += line
                    print(line, end='')
                elif proc.poll() is not None:
                    break
            proc.wait()
        else:
            output = proc.communicate()[0]

        if timeout and timer is not None:
            timer.cancel()

        rc = proc.returncode
        proc = None
        if timeout and timed_out[0]:
            return output + (f"\n{cmd[0]} timed out.")
        elif rc == -signal.SIGSEGV:
            raise Exception("segmentation fault")
        elif rc:
            raise Exception(output)
        else:
            return output

    except (RuntimeError, OSError) as err:
        print(output, file=sys.stderr)
        sys.exit("Error invoking command:\n{}\n{}".format(" ".join(cmd), err))

    finally:
        if timeout and timer:
            timer.cancel()
        if proc:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        if filelog:
            with Path(temporary_file(cmd[0], '.log', args)).open('w') as f:
                f.write(output)


def llvm_exact_bin(name):
    return name + '-' + LLVM_SHORT_VERSION


def smack_root():
    return str(Path(sys.argv[0]).resolve().parent.parent)


def smack_header_path():
    return str(Path(smack_root()) / 'share' / 'smack' / 'include')


def smack_headers(args):
    paths = []
    paths.append(smack_header_path())
    return paths


def smack_lib():
    return str(Path(smack_root()) / 'share' / 'smack' / 'lib')


def smack_portfolio_path():
    return str(Path(smack_root()) / 'share' / 'smack' / 'default-portfolio.yaml')
