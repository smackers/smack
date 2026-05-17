"""Command-builders for the back-end verifiers (Boogie, Corral).

Pure functions of an argparse.Namespace — no side effects, no I/O — so they
are trivially unit-testable in isolation.

Symbooglix support was removed in the Phase 1 modernization (Mono dependency
drop). CVC4 and Yices2 support was removed in the same phase; Z3 (default)
and cvc5 (when added) cover all use cases.
"""


def boogie_command(args):
    command = ["boogie"]
    command += ["/inferModifies"]
    command += [f"/timeLimit:{args.time_limit}"]
    command += [f"/errorLimit:{args.max_violations}"]
    if not args.modular:
        command += ["/loopUnroll:%d" % args.unroll]
    return command


def corral_command(args):
    command = ["corral"]
    command += [args.bpl_file]
    command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
    command += ["/k:%d" % args.context_bound]
    command += ["/useProverEvaluate"]
    command += [f"/timeLimit:{args.time_limit}"]
    command += [f"/cex:{args.max_violations}"]
    command += ["/maxStaticLoopBound:%d" % args.loop_limit]
    command += ["/recursionBound:%d" % args.unroll]
    return command
