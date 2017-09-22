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
# - lockpwn
#
################################################################################

# Set these flags to control various installation options
INSTALL_DEPENDENCIES=1
BUILD_Z3=1
BUILD_BOOGIE=1
BUILD_CORRAL=1
BUILD_LOCKPWN=1
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
LOCKPWN_DIR="${ROOT}/lockpwn"
MONO_DIR="${ROOT}/mono"
LLVM_DIR="${ROOT}/llvm"

source ${SMACK_DIR}/bin/versions

SMACKENV=${ROOT}/smack.environment
WGET="wget --no-verbose"

# Install prefix -- system default is used if left unspecified
INSTALL_PREFIX=
CONFIGURE_INSTALL_PREFIX=
CMAKE_INSTALL_PREFIX=

# Partial list of dependnecies; the rest are added depending on the platform
DEPENDENCIES="git cmake python-yaml python-psutil unzip wget"

shopt -s extglob

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

distro=$(get-platform)
puts "Detected distribution: $distro"

# Set platform-dependent flags
case "$distro" in
linux-opensuse*)
  Z3_DOWNLOAD_LINK="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-debian-8.2.zip"
  DEPENDENCIES+=" llvm-clang llvm-devel gcc-c++ mono-complete make"
  DEPENDENCIES+=" ncurses-devel zlib-devel"
  ;;

linux-@(ubuntu|neon)-1[46]*)
  Z3_DOWNLOAD_LINK="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-ubuntu-14.04.zip"
  DEPENDENCIES+=" clang-${LLVM_SHORT_VERSION} llvm-${LLVM_SHORT_VERSION} mono-complete libz-dev libedit-dev"
  ;;

linux-ubuntu-12*)
  Z3_DOWNLOAD_LINK="https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-ubuntu-14.04.zip"
  DEPENDENCIES+=" g++-4.8 autoconf automake bison flex libtool gettext gdb"
  DEPENDENCIES+=" libglib2.0-dev libfontconfig1-dev libfreetype6-dev libxrender-dev"
  DEPENDENCIES+=" libtiff-dev libjpeg-dev libgif-dev libpng-dev libcairo2-dev"
  BUILD_LLVM=1
  BUILD_MONO=1
  INSTALL_PREFIX="/usr/local"
  CONFIGURE_INSTALL_PREFIX="--prefix=${INSTALL_PREFIX}"
  CMAKE_INSTALL_PREFIX="-DCMAKE_INSTALL_PREFIX=${INSTALL_PREFIX}"
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

  linux-@(ubuntu|neon)-1[46]*)
    RELEASE_VERSION=$(get-platform-trim "$(lsb_release -r)" | awk -F: '{print $2;}')
    UBUNTU_CODENAME="trusty"
    case "$RELEASE_VERSION" in
    14*)
      UBUNTU_CODENAME="trusty"
      ;;
    16*)
      UBUNTU_CODENAME="xenial"
      ;;
    *)
      puts "Release ${RELEASE_VERSION} for ${distro} not supported. Dependencies must be installed manually."
      exit 1
      ;;
    esac

    # Adding LLVM repository
    sudo add-apt-repository "deb http://apt.llvm.org/${UBUNTU_CODENAME}/ llvm-toolchain-${UBUNTU_CODENAME}-${LLVM_SHORT_VERSION} main"
    ${WGET} -O - http://apt.llvm.org/llvm-snapshot.gpg.key | sudo apt-key add -
    # Adding MONO repository
    sudo add-apt-repository "deb http://download.mono-project.com/repo/debian wheezy main"
    sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF
#    echo "deb http://download.mono-project.com/repo/debian wheezy main" | sudo tee /etc/apt/sources.list.d/mono-xamarin.list
    sudo apt-get update
    sudo apt-get install -y ${DEPENDENCIES}
    sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-${LLVM_SHORT_VERSION} 30
    sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-${LLVM_SHORT_VERSION} 30
    sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-${LLVM_SHORT_VERSION} 30
    sudo update-alternatives --install /usr/bin/llvm-link llvm-link /usr/bin/llvm-link-${LLVM_SHORT_VERSION} 30
    sudo update-alternatives --install /usr/bin/llvm-dis llvm-dis /usr/bin/llvm-dis-${LLVM_SHORT_VERSION} 30
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


if [ ${BUILD_MONO} -eq 1 ]
then
  puts "Building mono"

  git clone git://github.com/mono/mono.git ${MONO_DIR}
  cd ${MONO_DIR}
  git checkout mono-${MONO_VERSION}
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

  if [[ ${INSTALL_PREFIX} ]]
  then
    echo export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${INSTALL_PREFIX}/lib >> ${SMACKENV}
    source ${SMACKENV}
  fi

  puts "Built mono"
fi


if [ ${BUILD_LLVM} -eq 1 ]
then
  puts "Building LLVM"

  mkdir -p ${LLVM_DIR}/src/{tools/clang,projects/compiler-rt}
  mkdir -p ${LLVM_DIR}/build

  ${WGET} http://llvm.org/releases/${LLVM_FULL_VERSION}/llvm-${LLVM_FULL_VERSION}.src.tar.xz
  ${WGET} http://llvm.org/releases/${LLVM_FULL_VERSION}/cfe-${LLVM_FULL_VERSION}.src.tar.xz
  ${WGET} http://llvm.org/releases/${LLVM_FULL_VERSION}/compiler-rt-${LLVM_FULL_VERSION}.src.tar.xz

  tar -C ${LLVM_DIR}/src -xvf llvm-${LLVM_FULL_VERSION}.src.tar.xz --strip 1
  tar -C ${LLVM_DIR}/src/tools/clang -xvf cfe-${LLVM_FULL_VERSION}.src.tar.xz --strip 1
  tar -C ${LLVM_DIR}/src/projects/compiler-rt -xvf compiler-rt-${LLVM_FULL_VERSION}.src.tar.xz --strip 1

  cd ${LLVM_DIR}/build/
  cmake -G "Unix Makefiles" ${CMAKE_INSTALL_PREFIX} -DCMAKE_BUILD_TYPE=Release ../src
  make
  sudo make install

  puts "Built LLVM"
fi


if [ ${BUILD_Z3} -eq 1 ]
then
  puts "Installing Z3"

  ${WGET} ${Z3_DOWNLOAD_LINK} -O z3-downloaded.zip
  unzip -o z3-downloaded.zip -d z3-extracted
  mv -f --backup=numbered z3-extracted/z3-* ${Z3_DIR}
  rm -rf z3-downloaded.zip z3-extracted

  puts "Installed Z3"
fi


if [ ${BUILD_BOOGIE} -eq 1 ]
then
  puts "Building Boogie"

  if [ ! -d "$BOOGIE_DIR" ] ; then
    git clone https://github.com/boogie-org/boogie.git ${BOOGIE_DIR}
  fi
  cd ${BOOGIE_DIR}
  git reset --hard ${BOOGIE_COMMIT}
  cd ${BOOGIE_DIR}/Source
  ${WGET} https://dist.nuget.org/win-x86-commandline/latest/nuget.exe
  mono ./nuget.exe restore Boogie.sln
  rm -rf /tmp/nuget/
  msbuild Boogie.sln /p:Configuration=Release
  ln -sf ${Z3_DIR}/bin/z3 ${BOOGIE_DIR}/Binaries/z3.exe

  puts "Built Boogie"
fi


if [ ${BUILD_CORRAL} -eq 1 ]
then
  puts "Building Corral"

  if [ ! -d "$CORRAL_DIR" ] ; then
    git clone https://github.com/boogie-org/corral.git ${CORRAL_DIR}
  fi
  cd ${CORRAL_DIR}
  git reset --hard ${CORRAL_COMMIT}
  git submodule init
  git submodule update
  msbuild cba.sln /p:Configuration=Release
  ln -sf ${Z3_DIR}/bin/z3 ${CORRAL_DIR}/bin/Release/z3.exe

  puts "Built Corral"
fi

if [ ${BUILD_LOCKPWN} -eq 1 ]
then
  puts "Building lockpwn"

  cd ${ROOT}
  if [ ! -d "$LOCKPWN_DIR" ] ; then
    git clone https://github.com/smackers/lockpwn.git
  fi
  cd ${LOCKPWN_DIR}
  git reset --hard ${LOCKPWN_COMMIT}
  msbuild lockpwn.sln /p:Configuration=Release
  ln -sf ${Z3_DIR}/bin/z3 ${LOCKPWN_DIR}/Binaries/z3.exe

  puts "Built lockpwn"
fi

if [ ${BUILD_SMACK} -eq 1 ]
then
  puts "Building SMACK"

  mkdir -p ${SMACK_DIR}/build
  cd ${SMACK_DIR}/build
  cmake ${CMAKE_INSTALL_PREFIX} -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=Debug ..
  make
  sudo make install

  puts "Configuring shell environment"
  echo export BOOGIE=\"mono ${BOOGIE_DIR}/Binaries/Boogie.exe\" >> ${SMACKENV}
  echo export CORRAL=\"mono ${CORRAL_DIR}/bin/Release/corral.exe\" >> ${SMACKENV}
  echo export LOCKPWN=\"mono ${LOCKPWN_DIR}/Binaries/lockpwn.exe\" >> ${SMACKENV}
  source ${SMACKENV}
  puts "The required environment variables have been set in ${SMACKENV}"
  puts "You should source ${SMACKENV} in your .bashrc"

  puts "Built SMACK"
fi


if [ ${TEST_SMACK} -eq 1 ]
then
  puts "Running SMACK regression tests"

  cd ${SMACK_DIR}/test
  ./regtest.py ${TRAVIS_ENV}
  res=$?

  puts "Regression tests complete"
fi

exit $res
