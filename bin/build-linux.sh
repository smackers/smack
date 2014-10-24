#!/bin/bash
#
# This file is distributed under the MIT License. See LICENSE for details.
#

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
INSTALL_MONO=1
INSTALL_Z3=1
INSTALL_BOOGIE=1
INSTALL_CORRAL=1
INSTALL_LLVM=1
INSTALL_SMACK=1

# Other dirs
MONO_DIR="${BASE_DIR}/mono-3"
Z3_DIR="${BASE_DIR}/z3"
BOOGIE_DIR="${BASE_DIR}/boogie"
CORRAL_DIR="${BASE_DIR}/corral"
LLVM_DIR="${BASE_DIR}/llvm"
SMACK_DIR="${BASE_DIR}/smack"

# Setting colors
textcolor='\e[0;35m'
nocolor='\e[0m'

################################################################################

# Install required packages

if [ ${INSTALL_PACKAGES} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing required packages ***${nocolor}"

sudo add-apt-repository ppa:ubuntu-toolchain-r/test
sudo apt-get update
sudo apt-get install -y g++-4.8
sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-4.8 20
sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 20
sudo update-alternatives --config gcc
sudo update-alternatives --config g++

sudo apt-get install -y git
sudo apt-get install -y mercurial
sudo apt-get install -y autoconf
sudo apt-get install -y wget
sudo apt-get install -y unzip

echo -e "${textcolor}*** SMACK BUILD: Installed required packages ***${nocolor}"

fi

################################################################################

# Set up base directory for everything
mkdir -p ${BASE_DIR}
cd ${BASE_DIR}

################################################################################

# mono

if [ ${INSTALL_MONO} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing mono ***${nocolor}"

mkdir -p ${MONO_DIR}

# Install mono
sudo apt-get install -y git autoconf automake bison flex libtool gettext gdb
cd ${MONO_DIR}
git clone git://github.com/mono/mono.git
cd mono
git checkout mono-3.8.0
./autogen.sh --prefix=/usr/local
make get-monolite-latest
make EXTERNAL_MCS=${PWD}/mcs/class/lib/monolite/gmcs.exe
sudo make install

# Install libgdiplus
sudo apt-get install -y libglib2.0-dev libfontconfig1-dev libfreetype6-dev libxrender-dev 
sudo apt-get install -y libtiff-dev libjpeg-dev libgif-dev libpng-dev libcairo2-dev
cd ${MONO_DIR}
git clone git://github.com/mono/libgdiplus.git
cd libgdiplus
./autogen.sh --prefix=/usr/local
make
sudo make install

export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib

cd ${BASE_DIR}

echo -e "${textcolor}*** SMACK BUILD: Installed mono ***${nocolor}"

fi

################################################################################

# Z3

if [ ${INSTALL_Z3} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing Z3 ***${nocolor}"

mkdir -p ${Z3_DIR}/src
mkdir -p ${Z3_DIR}/install

# Get Z3
cd ${Z3_DIR}/src/
wget "http://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=z3&changeSetId=93337fedebefdb072066f2219efe69c80adc2647"
unzip -o SourceControlFileDownload*
rm -f SourceControlFileDownload*

# Configure Z3 and build
cd ${Z3_DIR}/src/
python scripts/mk_make.py --prefix=${Z3_DIR}/install
cd build
make
make install

cd ${BASE_DIR}

echo -e "${textcolor}*** SMACK BUILD: Installed Z3 ***${nocolor}"

fi

################################################################################

# Boogie

if [ ${INSTALL_BOOGIE} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing Boogie ***${nocolor}"

mkdir -p ${BOOGIE_DIR}

# Get Boogie
hg clone -r 02815f46a6f1 https://hg.codeplex.com/boogie ${BOOGIE_DIR}

# Build Boogie
cd ${BOOGIE_DIR}/Source
xbuild Boogie.sln
ln -s ${Z3_DIR}/install/bin/z3 ${BOOGIE_DIR}/Binaries/z3.exe

cd ${BASE_DIR}

echo -e "${textcolor}*** SMACK BUILD: Installed Boogie ***${nocolor}"

fi

################################################################################

# Corral

if [ ${INSTALL_CORRAL} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing Corral ***${nocolor}"

mkdir -p ${CORRAL_DIR}

# Get Corral
git clone https://git01.codeplex.com/corral ${CORRAL_DIR}
cd ${CORRAL_DIR}
git checkout 9235ea4f8cd2

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

echo -e "${textcolor}*** SMACK BUILD: Installed Corral ***${nocolor}"

fi

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
export BOOGIE="mono ${BOOGIE_DIR}/Binaries/Boogie.exe"
export CORRAL="mono ${CORRAL_DIR}/bin/Debug/corral.exe"
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

