#!/bin/bash

################################################################################
#
# Builds and installs SMACK in BASE_DIR (see shell var below in settings).
#
# Requirements:
# - git
# - python
# - gcc
# - g++
# - make
# - autoconf
#
################################################################################

# Exit on error
set -e

################################################################################

# Settings

# Change this to the desired path (default uses working-dir/smack-project)
BASE_DIR=`pwd`/smack-project

# Set these flags to control various installation options
INSTALL_LLVM=1
INSTALL_SMACK=1

# Other dirs
LLVM_DIR="${BASE_DIR}/llvm"
SMACK_DIR="${BASE_DIR}/smack"

################################################################################

# Set up base directory for everything
mkdir -p ${BASE_DIR}
cd ${BASE_DIR}

################################################################################

# LLVM

if [ ${INSTALL_LLVM} -eq 1 ]; then

mkdir -p ${LLVM_DIR}/src
mkdir -p ${LLVM_DIR}/build
mkdir -p ${LLVM_DIR}/install

# Get llvm and extract
wget http://llvm.org/releases/3.4/llvm-3.4.src.tar.gz
wget http://llvm.org/releases/3.4/clang-3.4.src.tar.gz
wget http://llvm.org/releases/3.4/compiler-rt-3.4.src.tar.gz

tar -C ${LLVM_DIR}/src -xzvf llvm-3.4.src.tar.gz --strip 1
mkdir -p ${LLVM_DIR}/src/tools/clang
tar -C ${LLVM_DIR}/src/tools/clang -xzvf clang-3.4.src.tar.gz --strip 1
mkdir -p ${LLVM_DIR}/src/projects/compiler-rt
tar -C ${LLVM_DIR}/src/projects/compiler-rt -xzvf compiler-rt-3.4.src.tar.gz --strip 1

# Configure llvm and build
cd ${LLVM_DIR}/build/
cmake -DCMAKE_INSTALL_PREFIX=${LLVM_DIR}/install -DCMAKE_BUILD_TYPE=Release ../src
make
make install

cd ${BASE_DIR}

fi

################################################################################

# SMACK

if [ ${INSTALL_SMACK} -eq 1 ]; then

mkdir -p ${SMACK_DIR}/src
mkdir -p ${SMACK_DIR}/build
mkdir -p ${SMACK_DIR}/install

# Get SMACK
git clone git://github.com/smackers/smack.git ${SMACK_DIR}/src/

# Configure SMACK and build
cd ${SMACK_DIR}/build/
cmake -DLLVM_CONFIG=${LLVM_DIR}/install/bin -DCMAKE_INSTALL_PREFIX=${SMACK_DIR}/install -DCMAKE_BUILD_TYPE=Release ../src
make
make install

cd ${BASE_DIR}

# Set required paths and environment variables
export BOOGIE=/cygdrive/c/Users/zvonimir/Boogie/boogie
export CORRAL=/cygdrive/c/projects/corral/corral
export PATH=${LLVM_DIR}/install/bin:$PATH
export PATH=${SMACK_DIR}/install/bin:$PATH

# Run SMACK regressions
cd ${SMACK_DIR}/src/test
make
./regtest.py --verifier {boogie,corral,duality}

cd ${BASE_DIR}

fi

################################################################################

