#!/bin/sh
SMACK_BIN="$( cd "$(dirname "$(readlink -f "${0}")")" && pwd )"
ROOT="$( cd "${SMACK_BIN}" && cd .. && cd .. && pwd )"
CORRAL_DIR="${ROOT}/corral"
LOCKPWN_DIR="${ROOT}/lockpwn"
LLVM_DIR="${ROOT}/llvm"

export PATH=${LLVM_DIR}/bin:$SMACK_BIN:$PATH
export CORRAL="mono ${CORRAL_DIR}/bin/Release/corral.exe"
export LOCKPWN="mono ${LOCKPWN_DIR}/Binaries/lockpwn.exe"

smack.py -x=svcomp --verifier=svcomp -q $@

