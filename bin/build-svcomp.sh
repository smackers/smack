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
TEST_SMACK=0

# PATHS
SMACK_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && cd .. && pwd )"
ROOT="$( cd "${SMACK_DIR}" && cd .. && pwd )"
Z3_DIR="${ROOT}/z3"
BOOGIE_DIR="${ROOT}/boogie"
CORRAL_DIR="${ROOT}/corral"
MONO_DIR="${ROOT}/mono"
LLVM_DIR="${ROOT}/llvm"

source ${SMACK_DIR}/bin/versions

SMACKENV=${ROOT}/smack.environment
WGET="wget --no-verbose --method=GET"

# Install prefix -- system default is used if left unspecified
INSTALL_PREFIX=
CONFIGURE_INSTALL_PREFIX=
CMAKE_INSTALL_PREFIX=

# Partial list of dependnecies; the rest are added depending on the platform
DEPENDENCIES="git cmake python-yaml unzip wget"

function puts {
  echo -e "\033[35m*** SMACK BUILD: ${1} ***\033[0m"
}

# Exit on error
set -e

Z3_DOWNLOAD_LINK="https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/z3-4.4.1-x64-ubuntu-14.04.zip"
DEPENDENCIES+=" clang-3.5 llvm-3.5 mono-complete libz-dev libedit-dev"

# Parse command line options
while [[ $# > 0 ]]
do
  case "$1" in
  --prefix)
    puts "Using install prefix $2"
    INSTALL_PREFIX="${2%/}"
    CONFIGURE_INSTALL_PREFIX="--prefix=$2"
    CMAKE_INSTALL_PREFIX="-DCMAKE_INSTALL_PREFIX=$2"
    echo export PATH=${INSTALL_PREFIX}/bin:$PATH >> ${SMACKENV}
    shift
    shift
    ;;

  *)
    puts "Unknown option: $1"
    exit 1
    ;;
  esac
done


if [ ${INSTALL_DEPENDENCIES} -eq 1 ]
then
  puts "Installing required packages"

  case "$distro" in
  linux-opensuse*)
    sudo zypper --non-interactive install ${DEPENDENCIES}
    ;;

  linux-ubuntu-14*)
    sudo add-apt-repository "deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.5 main"
    ${WGET} -O - http://llvm.org/apt/llvm-snapshot.gpg.key | sudo apt-key add -
    sudo apt-get update
    sudo apt-get install -y ${DEPENDENCIES}
    sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.5 20
    sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-3.5 20
    sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-3.5 20
    sudo update-alternatives --install /usr/bin/llvm-link llvm-link /usr/bin/llvm-link-3.5 20
    ;;

  linux-ubuntu-12*)
    sudo add-apt-repository -y ppa:ubuntu-toolchain-r/test
    sudo add-apt-repository -y ppa:andykimpe/cmake
    sudo apt-get update
    sudo apt-get install -y ${DEPENDENCIES}
    sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-4.8 20
    sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 20
    sudo update-alternatives --config gcc
    sudo update-alternatives --config g++
    ;;

  linux-cygwin*)
    ;;

  *)
    puts "Distribution ${distro} not supported. Dependencies must be installed manually."
    exit 1
    ;;
  esac

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

  mkdir -p ${SMACK_DIR}/build
  cd ${SMACK_DIR}/build
  cmake ${CMAKE_INSTALL_PREFIX} -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=Debug ..
  make
  make install

  puts "Configuring shell environment"
  echo export BOOGIE=\"mono ${BOOGIE_DIR}/Binaries/Boogie.exe\" >> ${SMACKENV}
  echo export CORRAL=\"mono ${CORRAL_DIR}/bin/Release/corral.exe\" >> ${SMACKENV}
  source ${SMACKENV}
  puts "The required environment variables have been set in ${SMACKENV}"
  puts "You should source ${SMACKENV} in your .bashrc"

  puts "Built SMACK"
fi


if [ ${TEST_SMACK} -eq 1 ]
then
  puts "Running SMACK regression tests"

  cd ${SMACK_DIR}/test
  ./regtest.py
  res=$?

  puts "Regression tests complete"
fi

exit $res

