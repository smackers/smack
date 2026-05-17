import re
from pathlib import Path

from .logging_config import get_logger, get_warnings_logger
from .utils import temporary_file, try_command

_log = get_logger("replay")
_warn = get_warnings_logger()

SPECIAL_NAMES = ['__VERIFIER_assert', '__VERIFIER_assume']


def replay_error_trace(verifier_output, args):
    if args.verifier != 'corral':
        _warn.warning(
            "Replay for verifiers other than 'corral' currently unsupported; skipping replay"
        )
        return

    _log.info("Attempting to replay error trace.")

    missing_definitions = detect_missing_definitions(args.bc_file)
    if '__SMACK_code' in missing_definitions:
        _warn.warning("inline Boogie code found; replay may fail")

    arguments, return_values = extract_values(verifier_output)

    with Path(args.replay_harness).open('w') as f:
        f.write(harness(arguments, return_values, missing_definitions))
    _log.info("Generated replay harness: %s", args.replay_harness)

    stubs_bc = temporary_file('stubs', '.bc', args)
    try_command(['clang', '-c', '-emit-llvm', '-o', stubs_bc, args.replay_harness])
    try_command(
        ['clang', '-Wl,-e,_smack_replay_main', '-o', args.replay_exe_file, args.bc_file, stubs_bc]
    )
    _log.info("Generated replay executable: %s", args.replay_exe_file)

    try:
        if 'error reached!' in try_command(["./" + args.replay_exe_file]):
            _log.info("Error-trace replay successful.")
            return True

        else:
            _log.info("Error-trace replay failed.")

    except Exception as err:
        _log.error("Error-trace replay caught %s", err)

    return False


def detect_missing_definitions(bc_file):
    missing = []
    try:
        try_command(['clang', bc_file])
    except Exception as err:
        msg = repr(err).replace("\\n", "\n")
        for line in msg.split("\n"):
            m = re.search(r'\"_(.*)\", referenced from:', line) or re.search(
                r'undefined reference to `(.*)\'', line
            )
            if m:
                missing.append(m.group(1))
    return missing


def extract(line):
    match = re.search(r'.*\((smack:.*) = (.*)\).*', line)
    return match and [match.group(1), match.group(2)]


def extract_values(trace):
    arguments = {}
    return_values = {}

    for key, val in [x for x in map(extract, trace.split('\n')) if x]:
        if 'smack:entry:' in key:
            _, _, fn = key.split(':')
            arguments[fn] = []

        elif 'smack:arg:' in key:
            _, _, fn, _arg = key.split(':')
            if fn not in arguments:
                raise Exception(f"expected entry point key smack:entry:{fn}")
            arguments[fn].append(val)

        elif 'smack:ext:' in key:
            _, _, fn = key.split(':')
            if fn not in return_values:
                return_values[fn] = []
            return_values[fn].append(val)

        else:
            _warn.warning("unexpected key %s", key)

    return arguments, return_values


def harness(arguments, return_values, missing_definitions):
    code = []
    code.append("""//
// This file was automatically generated from a Boogie error trace.
// It contains stubs for unspecified functions that were called in that trace.
// These stubs will return the same values they did in the error trace.
// This file can be linked with the source program to reproduce the error.
//
#include <stdlib.h>
#include <stdio.h>

void __VERIFIER_assert(int b) {
  if (!b) {
    printf("error reached!\\n");
    exit(0);
  }
}

void __VERIFIER_assume(int b) {
  if (!b) {
    printf("assumption does not hold.\\n");
    exit(-1);
  }
}
""")

    for fn in set(missing_definitions) - set(SPECIAL_NAMES):
        if fn in return_values:
            code.append(
                """// stub for function: {fn}
int {fn}$table[] = {{{vals}}};
int {fn}$idx = 0;

int {fn}() {{
  return {fn}$table[{fn}$idx++];
}}
""".format(fn=fn, vals=", ".join(return_values[fn]))
            )

        else:
            _warn.warning("unknown return value for %s", fn)
            code.append(
                f"""// stub for function {fn}
void {fn}() {{
  return;
}}
"""
            )

    if len(arguments) > 1:
        _warn.warning("multiple entrypoint argument annotations found")

    elif len(arguments) < 1:
        _warn.warning("no entrypoint argument annotations found")

    for fn, args in list(arguments.items()):
        code.append(
            """// entry point wrapper
int _smack_replay_main() {{
  {fn}({vals});
  return 0;
}}
int smack_replay_main() {{
  {fn}({vals});
  return 0;
}}
""".format(fn=fn, vals=", ".join(args))
        )

    return "\n".join(code)
