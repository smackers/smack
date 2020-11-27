#!/bin/sh

# This script has to be copied into the root folder of the SVCOMP package

ROOT="$( cd "$(dirname "$(readlink -f "${0}")")" && pwd )"
SMACK_BIN="${ROOT}/bin"
BOOGIE_BIN="${ROOT}/smack-deps/boogie"
CORRAL_BIN="${ROOT}/smack-deps/corral"
Z3_BIN="${ROOT}/smack-deps/z3/bin"
DOTNET_BIN="${ROOT}/smack-deps/dotnet"

export DOTNET_ROOT=${DOTNET_BIN}
export PATH=${DOTNET_BIN}:${SMACK_BIN}:${BOOGIE_BIN}:${CORRAL_BIN}:${Z3_BIN}:$PATH

smack -x=svcomp --verifier=svcomp -q $@

