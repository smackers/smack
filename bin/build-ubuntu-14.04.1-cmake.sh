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
# - LLVM, clang
# - cmake
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
INSTALL_SMACK=1

# Other dirs
Z3_DIR="${BASE_DIR}/z3"
BOOGIE_DIR="${BASE_DIR}/boogie"
CORRAL_DIR="${BASE_DIR}/corral"
SMACK_DIR="${BASE_DIR}/smack"

# Setting colors
textcolor='\e[0;35m'
nocolor='\e[0m'

################################################################################

# Install required packages

if [ ${INSTALL_PACKAGES} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing required packages ***${nocolor}"

sudo add-apt-repository "deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.5 main"
wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key|sudo apt-key add -
sudo apt-get update
sudo apt-get install -y clang-3.5 clang-3.5-doc libclang-common-3.5-dev libclang-3.5-dev libclang1-3.5 libclang1-3.5-dbg libllvm3.5 libllvm3.5-dbg lldb-3.5 llvm-3.5 llvm-3.5-dev llvm-3.5-doc llvm-3.5-runtime lldb-3.5-dev
sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.5 20
sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-3.5 20
sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-3.5 20
sudo update-alternatives --install /usr/bin/llvm-link llvm-link /usr/bin/llvm-link-3.5 20
sudo apt-get install -y libz-dev
sudo apt-get install -y libedit-dev
sudo apt-get install -y mono-complete
sudo apt-get install -y git
sudo apt-get install -y mercurial
sudo apt-get install -y cmake
sudo apt-get install -y unzip

echo -e "${textcolor}*** SMACK BUILD: Installed required packages ***${nocolor}"

fi

################################################################################

# Set up base directory for everything
mkdir -p ${BASE_DIR}
cd ${BASE_DIR}

################################################################################

# Z3

if [ ${INSTALL_Z3} -eq 1 ]; then

echo -e "${textcolor}*** SMACK BUILD: Installing Z3 ***${nocolor}"

mkdir -p ${Z3_DIR}/src
mkdir -p ${Z3_DIR}/install

# Get Z3
cd ${Z3_DIR}/src/
wget "http://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=z3&changeSetId=cee7dd39444c9060186df79c2a2c7f8845de415b" -O z3_download
unzip -o z3_download
rm -f z3_download

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
hg clone -r a776dc352a84 https://hg.codeplex.com/boogie ${BOOGIE_DIR}

# Build Boogie
cd ${BOOGIE_DIR}/Source
mozroots --import --sync
wget https://nuget.org/nuget.exe
mono ./nuget.exe restore Boogie.sln
xbuild Boogie.sln /p:Configuration=Release
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
git checkout 6d808d06c23c

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
xbuild cba.sln /p:Configuration=Release
ln -s ${Z3_DIR}/install/bin/z3 ${CORRAL_DIR}/bin/Release/z3.exe

cd ${BASE_DIR}

echo -e "${textcolor}*** SMACK BUILD: Installed Corral ***${nocolor}"

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
cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DLLVM_CONFIG=/usr/bin -DCMAKE_INSTALL_PREFIX=${SMACK_DIR}/install -DCMAKE_BUILD_TYPE=Release ../src
make
make install

echo -e "${textcolor}*** SMACK BUILD: Installed SMACK ***${nocolor}"

# Set required paths and environment variables
export BOOGIE="mono ${BOOGIE_DIR}/Binaries/Boogie.exe"
export CORRAL="mono ${CORRAL_DIR}/bin/Release/corral.exe"
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
