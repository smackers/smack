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
# - g++
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
INSTALL_CORRAL=1
INSTALL_LLVM=1
INSTALL_SMACK=1

# Other dirs
Z3_DIR="${BASE_DIR}/z3"
BOOGIE_DIR="${BASE_DIR}/boogie"
CORRAL_DIR="${BASE_DIR}/corral"
LLVM_DIR="${BASE_DIR}/llvm"
SMACK_DIR="${BASE_DIR}/smack"

################################################################################

# Install required packages

if [ ${INSTALL_PACKAGES} -eq 1 ]; then

sudo apt-get install -y g++
sudo apt-get install -y git
sudo apt-get install -y mercurial
sudo apt-get install -y autoconf
sudo apt-get install -y wget
sudo apt-get install -y unzip
sudo apt-get install -y monodevelop

fi

################################################################################

# Set up base directory for everything
mkdir -p ${BASE_DIR}
cd ${BASE_DIR}

################################################################################

# Z3

if [ ${INSTALL_Z3} -eq 1 ]; then

mkdir -p ${Z3_DIR}/src
mkdir -p ${Z3_DIR}/install

# Get Z3
cd ${Z3_DIR}/src/
wget "http://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=z3&changeSetId=89c1785b73225a1b363c0e485f854613121b70a7"
unzip -o SourceControlFileDownload*
rm -f SourceControlFileDownload*

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

mkdir -p ${BOOGIE_DIR}

# Get Boogie
hg clone -r 661c32e8d5ca https://hg.codeplex.com/boogie ${BOOGIE_DIR}

# Build Boogie
cd ${BOOGIE_DIR}/Source
xbuild Boogie.sln
ln -s ${Z3_DIR}/install/bin/z3 ${BOOGIE_DIR}/Binaries/z3.exe

cd ${BASE_DIR}

fi

################################################################################

# Corral

if [ ${INSTALL_CORRAL} -eq 1 ]; then

mkdir -p ${CORRAL_DIR}

# Get Corral
git clone https://git01.codeplex.com/corral ${CORRAL_DIR}
cd ${CORRAL_DIR}
git checkout df4d2e2ace82

# Build Corral
cd ${CORRAL_DIR}/references

cp ${BOOGIE_DIR}/Binaries/AbsInt.dll .
cp ${BOOGIE_DIR}/Binaries/Basetypes.dll .
cp ${BOOGIE_DIR}/Binaries/CodeContractsExtender.dll .
cp ${BOOGIE_DIR}/Binaries/Concurrency.dll .
cp ${BOOGIE_DIR}/Binaries/Core.dll .
cp ${BOOGIE_DIR}/Binaries/ExecutionEngine.dll .
cp ${BOOGIE_DIR}/Binaries/Graph.dll .
cp ${BOOGIE_DIR}/Binaries/Houdini.dll .
cp ${BOOGIE_DIR}/Binaries/Model.dll .
cp ${BOOGIE_DIR}/Binaries/ParserHelper.dll .
cp ${BOOGIE_DIR}/Binaries/Provers.SMTLib.dll .
cp ${BOOGIE_DIR}/Binaries/VCExpr.dll .
cp ${BOOGIE_DIR}/Binaries/VCGeneration.dll .
cp ${BOOGIE_DIR}/Binaries/Boogie.exe .
cp ${BOOGIE_DIR}/Binaries/BVD.exe .
cp ${BOOGIE_DIR}/Binaries/Doomed.dll .
cp ${BOOGIE_DIR}/Binaries/Predication.dll .

cd ${CORRAL_DIR}
xbuild cba.sln
ln -s ${Z3_DIR}/install/bin/z3 ${CORRAL_DIR}/bin/Debug/z3.exe

cd ${BASE_DIR}

fi

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
${LLVM_DIR}/src/configure --prefix=${LLVM_DIR}/install --enable-optimized
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
${SMACK_DIR}/src/configure --with-llvmsrc=${LLVM_DIR}/src --with-llvmobj=${LLVM_DIR}/build --prefix=${SMACK_DIR}/install --enable-optimized
make
make install

cd ${BASE_DIR}

# Set required paths and environment variables
export BOOGIE="mono ${BOOGIE_DIR}/Binaries/Boogie.exe"
export CORRAL="mono ${CORRAL_DIR}/bin/Debug/corral.exe"
export PATH=${LLVM_DIR}/install/bin:$PATH
export PATH=${SMACK_DIR}/install/bin:$PATH

# Run SMACK regressions
cd ${SMACK_DIR}/src/test
make
./regtest.py
./regtest-corral.py

cd ${BASE_DIR}

fi

################################################################################

