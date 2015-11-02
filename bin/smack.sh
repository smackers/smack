#!/bin/sh
SMACK_BIN="$( cd "$(dirname "$(readlink -f "${0}")")" && pwd )"
ROOT="$( cd "${SMACK_BIN}" && cd .. && cd .. && pwd )"
CORRAL_DIR="${ROOT}/corral"
LLVM_DIR="${ROOT}/llvm"

export PATH=${LLVM_DIR}/bin:$PATH
export CORRAL="mono ${CORRAL_DIR}/bin/Release/corral.exe"

$SMACK_BIN/smack.py -x=svcomp --verifier=svcomp -q $@

