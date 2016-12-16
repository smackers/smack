#!/bin/sh

# This script has to be copied into the root folder of the SVCOMP package

ROOT="$( cd "$(dirname "$(readlink -f "${0}")")" && pwd )"
SMACK_BIN="${ROOT}/smack/bin"
BOOGIE_BIN="${ROOT}/boogie"
CORRAL_BIN="${ROOT}/corral"
LOCKPWN_BIN="${ROOT}/lockpwn"
LLVM_BIN="${ROOT}/llvm/bin"
LLVM_LIB="${ROOT}/llvm/lib"

# Setting mono heap size to 13GB
export MONO_GC_PARAMS=max-heap-size=13g

export PATH=${LLVM_BIN}:$SMACK_BIN:$PATH
export BOOGIE="mono ${BOOGIE_BIN}/Boogie.exe"
export CORRAL="mono ${CORRAL_BIN}/corral.exe"
export LOCKPWN="mono ${LOCKPWN_BIN}/lockpwn.exe"
export LD_LIBRARY_PATH=${LLVM_LIB}:$LD_LIBRARY_PATH

smack -x=svcomp --verifier=svcomp -q $@

