from __future__ import annotations

import argparse
import os
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path
from threading import Timer

from .logging_config import get_logger
from .versions import LLVM_SHORT_VERSION

_log = get_logger("utils")

temporary_files: list[str] = []


def temporary_file(prefix: str, extension: str, args: argparse.Namespace) -> str:
    f, name = tempfile.mkstemp(extension, prefix + '-', Path.cwd(), True)
    os.close(f)
    if not args.debug:
        temporary_files.append(name)
    return name


def temporary_directory(prefix: str, extension: str, args: argparse.Namespace) -> str:
    name = tempfile.mkdtemp(extension, prefix + '-', Path.cwd())
    if not args.debug:
        temporary_files.append(name)
    return name


def remove_temp_files() -> None:
    for f in temporary_files:
        p = Path(f)
        if p.is_file():
            p.unlink()
        elif p.is_dir():
            shutil.rmtree(f)


def timeout_killer(proc: subprocess.Popen[str], timed_out: list[bool]) -> None:
    if not timed_out[0]:
        timed_out[0] = True
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)


def try_command(
    cmd: list[str],
    cwd: str | None = None,
    console: bool = False,
    timeout: float | None = None,
    env: dict[str, str] | None = None,
) -> str:
    # Lazy import to avoid a load-time cycle with top.py (which itself
    # re-exports symbols from pipeline.translate which imports utils).
    from . import top

    args = top.args
    console = (console or args.verbose or args.debug) and not args.quiet
    filelog: bool = args.debug
    output = ''
    proc: subprocess.Popen[str] | None = None
    timer: Timer | None = None
    timed_out: list[bool] = [False]
    if env is not None:
        for k, v in env.items():
            os.putenv(k, v)
    try:
        # smack.utils logger respects --debug via logging_config.configure.
        # Kept the level check explicit (rather than just _log.debug(...))
        # because the join() is non-trivial when arg lists are long.
        if args.debug:
            _log.debug("Running %s", " ".join(cmd))

        proc = subprocess.Popen(
            cmd,
            cwd=cwd,
            preexec_fn=os.setsid,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            universal_newlines=True,
        )

        if timeout:
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
        _log.error("subprocess output before failure:\n%s", output)
        sys.exit("Error invoking command:\n{}\n{}".format(" ".join(cmd), err))

    finally:
        if timeout and timer:
            timer.cancel()
        if proc:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        if filelog:
            with Path(temporary_file(cmd[0], '.log', args)).open('w') as f:
                f.write(output)


def llvm_exact_bin(name: str) -> str:
    return name + '-' + LLVM_SHORT_VERSION


def smack_root() -> str:
    return str(Path(sys.argv[0]).resolve().parent.parent)


def smack_header_path() -> str:
    return str(Path(smack_root()) / 'share' / 'smack' / 'include')


def smack_headers(args: argparse.Namespace) -> list[str]:
    paths: list[str] = []
    paths.append(smack_header_path())
    return paths


def smack_lib() -> str:
    return str(Path(smack_root()) / 'share' / 'smack' / 'lib')


def smack_portfolio_path() -> str:
    return str(Path(smack_root()) / 'share' / 'smack' / 'default-portfolio.yaml')
