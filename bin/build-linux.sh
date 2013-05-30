#!/bin/bash

################################################################################
#
# Builds and installs SMACK in BASE_DIR (see shell var below in settings).
#
# Requirements (see "Install required packages" below):
# - git
# - mercurial
# - python
# - gcc
# - make
# - autoconf
# - mono
#
################################################################################

# Exit on error
set -e

################################################################################

# Settings

# Change this to the desired path (default uses working-dir/smack-project)
BASE_DIR=`pwd`/smack-project

# Set these flags to control various installation options
INSTALL_PACKAGES=1
INSTALL_Z3=1
INSTALL_BOOGIE=1
INSTALL_LLVM=1
INSTALL_SMACK=1

# Other dirs
Z3_DIR="${BASE_DIR}/z3"
BOOGIE_DIR="${BASE_DIR}/boogie"
LLVM_DIR="${BASE_DIR}/llvm"
SMACK_DIR="${BASE_DIR}/smack"

################################################################################

# Install required packages

if [ ${INSTALL_PACKAGES} -eq 1 ]; then

sudo apt-get install git --assume-yes
sudo apt-get install mercurial --assume-yes
sudo apt-get install autoconf --assume-yes
sudo apt-get install mono-devel --assume-yes

fi

################################################################################

# Set up directories

# Base directory for everything
mkdir -p ${BASE_DIR}

# Other dirs
mkdir -p ${Z3_DIR}/src
mkdir -p ${Z3_DIR}/install
mkdir -p ${BOOGIE_DIR}
mkdir -p ${LLVM_DIR}/src
mkdir -p ${LLVM_DIR}/build
mkdir -p ${LLVM_DIR}/install
mkdir -p ${SMACK_DIR}/src
mkdir -p ${SMACK_DIR}/build
mkdir -p ${SMACK_DIR}/install

cd ${BASE_DIR}

################################################################################

# Z3

if [ ${INSTALL_Z3} -eq 1 ]; then

# Get Z3
git clone https://git01.codeplex.com/z3 ${Z3_DIR}/src/

# Configure Z3 and build
cd ${Z3_DIR}/src/
autoconf
./configure --prefix=${Z3_DIR}/install
python scripts/mk_make.py
cd build
make
sudo make install

cd ${BASE_DIR}

fi

################################################################################

# Boogie

if [ ${INSTALL_BOOGIE} -eq 1 ]; then

# Get Boogie
hg clone https://hg.codeplex.com/boogie ${BOOGIE_DIR}

# Build Boogie
cd ${BOOGIE_DIR}/Source
xbuild Boogie.sln
ln -s ${Z3_DIR}/install/bin/z3 ${BOOGIE_DIR}/Binaries/z3.exe

cd ${BASE_DIR}

fi

################################################################################

# LLVM

if [ ${INSTALL_LLVM} -eq 1 ]; then

# Get llvm and extract
wget http://llvm.org/releases/3.2/llvm-3.2.src.tar.gz
wget http://llvm.org/releases/3.2/clang-3.2.src.tar.gz
wget http://llvm.org/releases/3.2/compiler-rt-3.2.src.tar.gz

tar -C ${LLVM_DIR}/src -xzvf llvm-3.2.src.tar.gz --strip 1
mkdir -p ${LLVM_DIR}/src/tools/clang
tar -C ${LLVM_DIR}/src/tools/clang -xzvf clang-3.2.src.tar.gz --strip 1
mkdir -p ${LLVM_DIR}/src/projects/compiler-rt
tar -C ${LLVM_DIR}/src/projects/compiler-rt -xzvf compiler-rt-3.2.src.tar.gz --strip 1

# Configure llvm and build
cd ${LLVM_DIR}/build/
${LLVM_DIR}/src/configure --prefix=${LLVM_DIR}/install
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
${SMACK_DIR}/src/configure --with-llvmsrc=${LLVM_DIR}/src --with-llvmobj=${LLVM_DIR}/build --prefix=${SMACK_DIR}/install
make
make install
cp -r ${SMACK_DIR}/src/bin ${SMACK_DIR}/install/bin

cd ${BASE_DIR}

# Set required paths and environment variables
export BOOGIE="mono ${BOOGIE_DIR}/Binaries/Boogie.exe"
export PATH=$PATH:${LLVM_DIR}/install/bin
export PATH=$PATH:${SMACK_DIR}/install/bin

# Run SMACK regressions
cd ${SMACK_DIR}/src/test
make
./regtest.py

cd ${BASE_DIR}

fi

################################################################################

