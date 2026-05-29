"""Source-tree fallback for SMACK tool versions.

CMake installs ``bin/versions`` as this module. Keeping the same constants in
the source tree lets ``bin/smack`` run directly in tests before installation.
"""

Z3_VERSION = "4.16.0"
Z3_GLIBC_VERSION = "2.39"
BOOGIE_VERSION = "3.5.6"
CORRAL_VERSION = "1.1.8"
LLVM_SHORT_VERSION = "21"
LLVM_FULL_VERSION = "21.1.0"
RUST_VERSION = "nightly-2022-01-01"
