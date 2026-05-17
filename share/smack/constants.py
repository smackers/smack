"""Module-level constants shared across the SMACK Python tooling.

Extracted from share/smack/top.py during Phase B5 of the modernization plan so
sub-modules (e.g. `pipeline.translate`) can reference them without importing
top.py and creating a load-time cycle.
"""

VERSION = "2.8.0"  # x-release-please-version


def inlined_procedures():
    return [
        "$galloc",
        "$alloc",
        "$malloc",
        "$free",
        "$memset",
        "$memcpy",
        "__VERIFIER_",
        "$initialize",
        "__SMACK_static_init",
        "__SMACK_init_func_memory_model",
        "__SMACK_loop_exit",
        "__SMACK_check_overflow",
    ]
