#!/bin/bash
################################################################################
#
# This file is distributed under the MIT License. See LICENSE for details.
#
################################################################################
#
# This script builds and installs SMACK, including the following dependencies:
# - Git
# - Mercurial
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

# Required versions
MONO_VERSION=mono-3.8.0
BOOGIE_COMMIT=d6a7f2bd79c9
CORRAL_COMMIT=3aa62d7425b5

# Set these flags to control various installation options
INSTALL_DEPENDENCIES=1
BUILD_Z3=1
BUILD_BOOGIE=1
BUILD_CORRAL=1
BUILD_SMACK=1
TEST_SMACK=1
BUILD_LLVM=0 # LLVM is typically installed from packages (see below)
BUILD_MONO=0

# PATHS
SMACK_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && cd .. && pwd )"
ROOT="$( cd "${SMACK_DIR}" && cd .. && pwd )"
Z3_DIR="${ROOT}/z3"
BOOGIE_DIR="${ROOT}/boogie"
CORRAL_DIR="${ROOT}/corral"
MONO_DIR="${ROOT}/mono"

BASHRC=~/.bashrc

# Install prefix -- system default is used if left unspecified
INSTALL_PREFIX=
CONFIGURE_INSTALL_PREFIX=
CMAKE_INSTALL_PREFIX=

################################################################################
#
# A FEW HELPER FUNCTIONS
#
# Detecting OS distributions
#
# The format of the output is:
#   <plat>-<dist>-<ver>-<arch>
#   ^      ^      ^     ^
#   |      |      |     +----- architecture: x86_64, i86pc, etc.
#   |      |      +----------- version: 5.5, 4.7
#   |      +------------------ distribution: centos, rhel, nexentaos
#   +------------------------- platform: linux, sunos
#
################################################################################

# ================================================================
# Trim a string, remove internal spaces, convert to lower case.
# ================================================================
function get-platform-trim {
  local s=$(echo "$1" | tr -d '[ \t]' | tr 'A-Z' 'a-z')
  echo $s
}

# ================================================================
# Get the platform root name.
# ================================================================
function get-platform-root {
  if which uname >/dev/null 2>&1 ; then
    if uname -o >/dev/null 2>&1 ; then
      # Linux distro
      uname -o | tr 'A-Z' 'a-z'
    elif uname -s >/dev/null 2>&1 ; then
      # Solaris variant
      uname -s | tr 'A-Z' 'a-z'
    else
      echo "unknown"
    fi
  else
    echo "unknown"
  fi
}

# ================================================================
# Get the platform identifier.
# ================================================================
function get-platform {
  plat=$(get-platform-root)
  case "$plat" in
    "gnu/linux")
      d=$(get-platform-trim "$(lsb_release -i)" | awk -F: '{print $2;}')
      r=$(get-platform-trim "$(lsb_release -r)" | awk -F: '{print $2;}')
      m=$(get-platform-trim "$(uname -m)")
      if [[ "$d" == "redhatenterprise"* ]] ; then
        # Need a little help for Red Hat because
        # they don't make the minor version obvious.
        d="rhel_${d:16}"  # keep the tail (e.g., es or client)
        x=$(get-platform-trim "$(lsb_release -c)" | \
          awk -F: '{print $2;}' | \
          sed -e 's/[^0-9]//g')
        r="$r.$x"
      fi
      echo "linux-$d-$r-$m"
      ;;
    "cygwin")
      x=$(get-platform-trim "$(uname)")
      echo "linux-$x"
      ;;
    "sunos")
      d=$(get-platform-trim "$(uname -v)")
      r=$(get-platform-trim "$(uname -r)")
      m=$(get-platform-trim "$(uname -m)")
      echo "sunos-$d-$r-$m"
      ;;
    "unknown")
      echo "unk-unk-unk-unk"
      ;;
    *)
      echo "$plat-unk-unk-unk"
      ;;
  esac
}

function puts {
  echo -e "\033[35m*** SMACK BUILD: ${1} ***\033[0m"
}

################################################################################
#
# END HELPER FUNCTIONS
#
################################################################################

# Exit on error
set -e

# Parse command line options
while [[ $# > 0 ]]
do
  case "$1" in
  --prefix)
    puts "Using install prefix $2"
    INSTALL_PREFIX="$2"
    CONFIGURE_INSTALL_PREFIX="--prefix=$2"
    CMAKE_INSTALL_PREFIX="-DCMAKE_INSTALL_PREFIX=$2"
    shift
    shift
    ;;

  *)
    puts "Unknown option: $1"
    exit 1
    ;;
  esac
done

distro=$(get-platform)
puts "Detected distribution: $distro"

# Set platform-dependent flags
case "$distro" in
linux-opensuse*)
  Z3_DOWNLOAD_LINK="http://download-codeplex.sec.s-msft.com/Download/Release?ProjectName=z3&DownloadId=1436282&FileTime=130700549966730000&Build=20959"
  ;;

linux-ubuntu-14*)
  Z3_DOWNLOAD_LINK="http://download-codeplex.sec.s-msft.com/Download/Release?ProjectName=z3&DownloadId=1436285&FileTime=130700551242630000&Build=20959"
  ;;

linux-ubuntu-12*)
  Z3_DOWNLOAD_LINK="http://download-codeplex.sec.s-msft.com/Download/Release?ProjectName=z3&DownloadId=1436285&FileTime=130700551242630000&Build=20959"
  BUILD_LLVM=1
  BUILD_MONO=1
  ;;

linux-cygwin*)
  BUILD_LLVM=1
  BUILD_Z3=0
  BUILD_BOOGIE=0
  BUILD_CORRAL=0
  ;;

*)
  puts "Distribution ${distro} not supported. Manual installation required."
  exit 1
  ;;
esac


if [ ${INSTALL_DEPENDENCIES} -eq 1 ]; then
  puts "Installing required packages"

  case "$distro" in
  linux-opensuse*)
    sudo zypper --non-interactive install llvm-clang llvm-devel gcc-c++ \
      ncurses-devel zlib-devel mono-complete git mercurial cmake make python-yaml
    ;;

  linux-ubuntu-14*)
    sudo add-apt-repository "deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.5 main"
    wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key|sudo apt-key add -
    sudo apt-get update
    sudo apt-get install -y clang-3.5 libllvm3.5 llvm-3.5 llvm-3.5-dev llvm-3.5-runtime
    sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.5 20
    sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-3.5 20
    sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-3.5 20
    sudo update-alternatives --install /usr/bin/llvm-link llvm-link /usr/bin/llvm-link-3.5 20
    sudo apt-get install -y libz-dev libedit-dev mono-complete git mercurial cmake python-yaml unzip
    ;;

  linux-ubuntu-12*)
    sudo add-apt-repository -y ppa:ubuntu-toolchain-r/test
    sudo add-apt-repository -y ppa:andykimpe/cmake
    sudo apt-get update
    sudo apt-get install -y g++-4.8
    sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-4.8 20
    sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 20
    sudo update-alternatives --config gcc
    sudo update-alternatives --config g++
    sudo apt-get install -y git mercurial autoconf cmake wget unzip python-yaml
    sudo apt-get install -y git autoconf automake bison flex libtool gettext gdb
    sudo apt-get install -y libglib2.0-dev libfontconfig1-dev libfreetype6-dev libxrender-dev
    sudo apt-get install -y libtiff-dev libjpeg-dev libgif-dev libpng-dev libcairo2-dev
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


if [ ${BUILD_MONO} -eq 1 ]
then
  puts "Building mono"

  git clone git://github.com/mono/mono.git ${MONO_DIR}
  cd ${MONO_DIR}
  git checkout ${MONO_VERSION}
  ./autogen.sh ${CONFIGURE_INSTALL_PREFIX}
  make get-monolite-latest
  make EXTERNAL_MCS=${PWD}/mcs/class/lib/monolite/gmcs.exe
  sudo make install

  # Install libgdiplus
  cd ${MONO_DIR}
  git clone git://github.com/mono/libgdiplus.git
  cd libgdiplus
  ./autogen.sh ${CONFIGURE_INSTALL_PREFIX}
  make
  sudo make install

  echo export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${INSTALL_PREFIX}/lib >> ${BASHRC}
  source ${BASHRC}

  puts "Built mono"
fi


if [ ${BUILD_LLVM} -eq 1 ]
then
  puts "Building LLVM"

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
  cmake ${CMAKE_INSTALL_PREFIX} -DCMAKE_BUILD_TYPE=Release ../src
  make
  sudo make install

  puts "Built LLVM"
fi


if [ ${BUILD_Z3} -eq 1 ]
then
  puts "Building Z3"

  wget ${Z3_DOWNLOAD_LINK} -O z3-downloaded.zip
  unzip -o z3-downloaded.zip -d z3-extracted
  mv z3-extracted/z3-* ${Z3_DIR}
  rm -f z3-downloaded.zip
  rmdir z3-extracted

  puts "Built Z3"
fi


if [ ${BUILD_BOOGIE} -eq 1 ]; then
  puts "Building Boogie"

  hg clone -r ${BOOGIE_COMMIT} https://hg.codeplex.com/boogie ${BOOGIE_DIR}
  cd ${BOOGIE_DIR}/Source
  mozroots --import --sync
  wget https://nuget.org/nuget.exe
  mono ./nuget.exe restore Boogie.sln
  xbuild Boogie.sln /p:Configuration=Release
  ln -s ${Z3_DIR}/bin/z3 ${BOOGIE_DIR}/Binaries/z3.exe

  puts "Built Boogie"
fi


if [ ${BUILD_CORRAL} -eq 1 ]
then
  puts "Building Corral"

  git clone https://git01.codeplex.com/corral ${CORRAL_DIR}
  cd ${CORRAL_DIR}
  git checkout ${CORRAL_COMMIT}
  cp ${BOOGIE_DIR}/Binaries/*.{dll,exe} references
  xbuild cba.sln /p:Configuration=Release
  ln -s ${Z3_DIR}/bin/z3 ${CORRAL_DIR}/bin/Release/z3.exe

  puts "Built Corral"
fi


if [ ${BUILD_SMACK} -eq 1 ]
then
  puts "Building SMACK"

  mkdir -p ${SMACK_DIR}/build
  cd ${SMACK_DIR}/build/
  cmake ${CMAKE_INSTALL_PREFIX} -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DLLVM_CONFIG=/usr/bin -DCMAKE_BUILD_TYPE=Release ..
  make
  sudo make install

  puts "Configuring shell environment"
  echo export BOOGIE=\\"mono ${BOOGIE_DIR}/Binaries/Boogie.exe\\" >> ${BASHRC}
  echo export CORRAL=\\"mono ${CORRAL_DIR}/bin/Release/corral.exe\\" >> ${BASHRC}
  source ${BASHRC}
  puts "The required environment variables have been set in ${BASHRC}"

  puts "Built SMACK"
fi


if [ ${TEST_SMACK} -eq 1 ]
then
  puts "Running SMACK regression tests"

  cd ${SMACK_DIR}/test
  ./regtest.py

  puts "Regression tests complete"
fi
