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

# Set up directories

# Base directory for everything
mkdir -p ${BASE_DIR}

# Other dirs
mkdir -p ${LLVM_DIR}/src
mkdir -p ${LLVM_DIR}/build
mkdir -p ${LLVM_DIR}/install
mkdir -p ${SMACK_DIR}/src
mkdir -p ${SMACK_DIR}/build
mkdir -p ${SMACK_DIR}/install

cd ${BASE_DIR}

################################################################################

# LLVM

if [ ${INSTALL_LLVM} -eq 1 ]; then

# Get llvm and extract
wget http://llvm.org/releases/3.3/llvm-3.3.src.tar.gz
wget http://llvm.org/releases/3.3/cfe-3.3.src.tar.gz
wget http://llvm.org/releases/3.3/compiler-rt-3.3.src.tar.gz

tar -C ${LLVM_DIR}/src -xzvf llvm-3.3.src.tar.gz --strip 1
mkdir -p ${LLVM_DIR}/src/tools/clang
tar -C ${LLVM_DIR}/src/tools/clang -xzvf cfe-3.3.src.tar.gz --strip 1
mkdir -p ${LLVM_DIR}/src/projects/compiler-rt
tar -C ${LLVM_DIR}/src/projects/compiler-rt -xzvf compiler-rt-3.3.src.tar.gz --strip 1

# Configure llvm and build
cd ${LLVM_DIR}/build/
${LLVM_DIR}/src/configure --prefix=${LLVM_DIR}/install --enable-shared --enable-optimized
make
make install

cd ${BASE_DIR}

fi

################################################################################

# SMACK

if [ ${INSTALL_SMACK} -eq 1 ]; then

# Get SMACK
git clone git://github.com/smackers/smack.git ${SMACK_DIR}/src/

# Configure SMACK and build
cd ${SMACK_DIR}/build/
${SMACK_DIR}/src/configure --with-llvmsrc=${LLVM_DIR}/src --with-llvmobj=${LLVM_DIR}/build --prefix=${SMACK_DIR}/install --enable-shared --enable-optimized
make
make install

cd ${BASE_DIR}

# Set required paths and environment variables
export BOOGIE=boogie
export CORRAL=corral
export PATH=$PATH:${LLVM_DIR}/install/bin
export PATH=$PATH:${SMACK_DIR}/install/bin

# Run SMACK regressions
cd ${SMACK_DIR}/src/test
make
./regtest.py
./regtest-corral.py

cd ${BASE_DIR}

fi

################################################################################

