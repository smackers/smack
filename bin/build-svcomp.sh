#!/bin/bash
################################################################################
#
# This file is distributed under the MIT License. See LICENSE for details.
#
################################################################################
#
# This script builds and installs SMACK, including the following dependencies:
# - Git
# - Python
# - CMake
# - LLVM
# - Clang
# - Mono
# - Z3
# - Boogie
# - Corral
#
################################################################################

# Set these flags to control various installation options
INSTALL_DEPENDENCIES=1
BUILD_Z3=1
BUILD_BOOGIE=1
BUILD_CORRAL=1
BUILD_SMACK=1

# PATHS
ROOT="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SMACK_DIR="${ROOT}/smack"
Z3_DIR="${ROOT}/z3"
BOOGIE_DIR="${ROOT}/boogie"
CORRAL_DIR="${ROOT}/corral"

BOOGIE_COMMIT=437bde8d02
CORRAL_DOWNLOAD_LINK="http://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=corral&changeSetId=0afb111179633047e14223115a5b16fe05d0ab5a"

SMACKENV=${ROOT}/smack.environment
WGET="wget --no-verbose --method=GET"

# Partial list of dependnecies; the rest are added depending on the platform
DEPENDENCIES="git cmake python-yaml unzip wget"

function puts {
  echo -e "\033[35m*** SMACK BUILD: ${1} ***\033[0m"
}

# Exit on error
set -e

Z3_DOWNLOAD_LINK="https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/z3-4.4.1-x64-ubuntu-14.04.zip"
DEPENDENCIES+=" clang-3.5 llvm-3.5 mono-complete libz-dev libedit-dev"


if [ ${INSTALL_DEPENDENCIES} -eq 1 ]
then
  puts "Installing required packages"

  sudo add-apt-repository "deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.5 main"
  ${WGET} -O - http://llvm.org/apt/llvm-snapshot.gpg.key | sudo apt-key add -
  sudo apt-get update
  sudo apt-get install -y ${DEPENDENCIES}
  sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.5 20
  sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-3.5 20
  sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-3.5 20
  sudo update-alternatives --install /usr/bin/llvm-link llvm-link /usr/bin/llvm-link-3.5 20

  puts "Installed required packages"
fi


if [ ${BUILD_Z3} -eq 1 ]
then
  puts "Installing Z3"

  ${WGET} ${Z3_DOWNLOAD_LINK} -O z3-downloaded.zip
  unzip -o z3-downloaded.zip -d z3-extracted
  mv z3-extracted/z3-* ${Z3_DIR}
  rm -rf z3-downloaded.zip z3-extracted

  puts "Installed Z3"
fi


if [ ${BUILD_BOOGIE} -eq 1 ]
then
  puts "Building Boogie"

  git clone https://github.com/boogie-org/boogie.git ${BOOGIE_DIR}
  cd ${BOOGIE_DIR}
  git reset --hard ${BOOGIE_COMMIT}
  cd ${BOOGIE_DIR}/Source
  mozroots --import --sync
  ${WGET} https://nuget.org/nuget.exe
  mono ./nuget.exe restore Boogie.sln
  rm -rf /tmp/nuget/
  xbuild Boogie.sln /p:Configuration=Release
  ln -s ${Z3_DIR}/bin/z3 ${BOOGIE_DIR}/Binaries/z3.exe

  puts "Built Boogie"
fi


if [ ${BUILD_CORRAL} -eq 1 ]
then
  puts "Building Corral"

  cd ${ROOT}
  ${WGET} ${CORRAL_DOWNLOAD_LINK} -O corral-downloaded.zip
  unzip -o corral-downloaded.zip -d ${CORRAL_DIR}
  rm -f corral-downloaded.zip
  cd ${CORRAL_DIR}
  cp ${BOOGIE_DIR}/Binaries/*.{dll,exe} references
  xbuild cba.sln /p:Configuration=Release
  ln -s ${Z3_DIR}/bin/z3 ${CORRAL_DIR}/bin/Release/z3.exe

  puts "Built Corral"
fi


if [ ${BUILD_SMACK} -eq 1 ]
then
  puts "Building SMACK"

  git clone https://github.com/smackers/smack.git ${SMACK_DIR}/src
  cd ${SMACK_DIR}/src
  git checkout svcomp2016
  mkdir -p ${SMACK_DIR}/build
  mkdir -p ${SMACK_DIR}/install
  cd ${SMACK_DIR}/build
  cmake -DCMAKE_INSTALL_PREFIX=${SMACK_DIR}/install -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=Debug ..
  make
  make install

  puts "Configuring shell environment"
  echo export PATH=${SMACK_DIR}/install/bin:$PATH >> ${SMACKENV}
  echo export BOOGIE=\"mono ${BOOGIE_DIR}/Binaries/Boogie.exe\" >> ${SMACKENV}
  echo export CORRAL=\"mono ${CORRAL_DIR}/bin/Release/corral.exe\" >> ${SMACKENV}
  puts "The required environment variables have been set in ${SMACKENV}"
  puts "You should source ${SMACKENV} in your .bashrc"

  puts "Built SMACK"
fi

