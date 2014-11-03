#!/bin/bash
#
# This file is distributed under the MIT License. See LICENSE for details.
#

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

# Setting colors
textcolor='\e[0;35m'
nocolor='\e[0m'

################################################################################

# Set up base directory for everything
mkdir -p ${BASE_DIR}
cd ${BASE_DIR}

################################################################################

# LLVM

if [ ${INSTALL_LLVM} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing LLVM ***${nocolor}"

mkdir -p ${LLVM_DIR}/src
mkdir -p ${LLVM_DIR}/build
mkdir -p ${LLVM_DIR}/install

# Get llvm and extract
wget http://llvm.org/releases/3.5.0/llvm-3.5.0.src.tar.xz
wget http://llvm.org/releases/3.5.0/cfe-3.5.0.src.tar.xz
wget http://llvm.org/releases/3.5.0/compiler-rt-3.5.0.src.tar.xz

tar -C ${LLVM_DIR}/src -xvf llvm-3.5.0.src.tar.xz --strip 1
mkdir -p ${LLVM_DIR}/src/tools/clang
tar -C ${LLVM_DIR}/src/tools/clang -xvf cfe-3.5.0.src.tar.xz --strip 1
mkdir -p ${LLVM_DIR}/src/projects/compiler-rt
tar -C ${LLVM_DIR}/src/projects/compiler-rt -xvf compiler-rt-3.5.0.src.tar.xz --strip 1

# Configure llvm and build
cd ${LLVM_DIR}/build/
${LLVM_DIR}/src/configure --prefix=${LLVM_DIR}/install --enable-optimized
make
make install

cd ${BASE_DIR}

echo -e "${textcolor}*** SMACK BUILD: Installed LLVM ***${nocolor}"

fi

################################################################################

# SMACK

if [ ${INSTALL_SMACK} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing SMACK ***${nocolor}"

mkdir -p ${SMACK_DIR}/src
mkdir -p ${SMACK_DIR}/build
mkdir -p ${SMACK_DIR}/install

# Get SMACK
git clone git://github.com/smackers/smack.git ${SMACK_DIR}/src/

# Configure SMACK and build
cd ${SMACK_DIR}/build/
${SMACK_DIR}/src/configure --with-llvmsrc=${LLVM_DIR}/src --with-llvmobj=${LLVM_DIR}/build --prefix=${SMACK_DIR}/install --enable-optimized
make
make install

cd ${BASE_DIR}

echo -e "${textcolor}*** SMACK BUILD: Installed SMACK ***${nocolor}"

# Set required paths and environment variables
export BOOGIE=/cygdrive/c/projects/boogie/Binaries/boogie
export CORRAL=/cygdrive/c/projects/corral/bin/Debug/corral
export PATH=${LLVM_DIR}/install/bin:$PATH
export PATH=${SMACK_DIR}/install/bin:$PATH

# Run SMACK regressions
echo -e "${textcolor}*** SMACK BUILD: Running regressions ***${nocolor}"
cd ${SMACK_DIR}/src/test
./regtest.py --verifier {boogie,corral}
echo -e "${textcolor}*** SMACK BUILD: Regressions done ***${nocolor}"

cd ${BASE_DIR}

echo -e "${textcolor}*** SMACK BUILD: You have to set the required environment variables! ***${nocolor}"

fi

################################################################################

