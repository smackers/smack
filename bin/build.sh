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

# Settings; change these as needed and/or desired

# Used versions of Boogie and Corral
BOOGIE_COMMIT=d6a7f2bd79c9
CORRAL_COMMIT=3aa62d7425b5

# Base project path (default is script-location-path/../..)
SCRIPT_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
BASE_DIR=${SCRIPT_DIR}/../..

# Installation prefix (system default is used unless changed)
PREFIX=

# Set these flags to control various installation options
INSTALL_PACKAGES=1
INSTALL_Z3=1
INSTALL_BOOGIE=1
INSTALL_CORRAL=1
INSTALL_SMACK=1
INSTALL_LLVM=0 # LLVM is typically installed from packages (see below)

# Other dirs
Z3_DIR="${BASE_DIR}/z3"
BOOGIE_DIR="${BASE_DIR}/boogie"
CORRAL_DIR="${BASE_DIR}/corral"
SMACK_DIR="${SCRIPT_DIR}/.."

# Setting colors
textcolor='\e[0;35m'
nocolor='\e[0m'

################################################################################

# Set up base directory for everything
mkdir -p ${BASE_DIR}
cd ${BASE_DIR}

################################################################################

# Detect Linux distribution

# The format of the output is:
#   <plat>-<dist>-<ver>-<arch>
#   ^      ^      ^     ^
#   |      |      |     +----- architecture: x86_64, i86pc, etc.
#   |      |      +----------- version: 5.5, 4.7
#   |      +------------------ distribution: centos, rhel, nexentaos
#   +------------------------- platform: linux, sunos
#

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
      echo "unkown"
    fi
  else
    echo "unkown"
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

distro=$(get-platform)
echo -e "${textcolor}Detected distribution: $distro${nocolor}"

################################################################################

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
    INSTALL_LLVM=1
    ;;

  linux-cygwin*)
    INSTALL_LLVM=1
    INSTALL_Z3=0
    INSTALL_BOOGIE=0
    INSTALL_CORRAL=0
    ;;

  *)
    echo -e "${textcolor}Distribution not supported. Manual install required.${nocolor}"
    exit 1
    ;;
esac

################################################################################

# Install required packages

if [ ${INSTALL_PACKAGES} -eq 1 ]; then

case "$distro" in
  linux-opensuse*)
    echo -e "${textcolor}*** SMACK BUILD: Installing required packages ***${nocolor}"
    sudo zypper --non-interactive install llvm-clang llvm-devel gcc-c++ ncurses-devel zlib-devel \
      mono-complete git mercurial cmake make python-yaml
    echo -e "${textcolor}*** SMACK BUILD: Installed required packages ***${nocolor}"
    ;;

  linux-ubuntu-14*)
    echo -e "${textcolor}*** SMACK BUILD: Installing required packages ***${nocolor}"
    sudo add-apt-repository "deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.5 main"
    wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key|sudo apt-key add -
    sudo apt-get update
    sudo apt-get install -y clang-3.5 clang-3.5-doc libclang-common-3.5-dev libclang-3.5-dev \
      libclang1-3.5 libclang1-3.5-dbg libllvm3.5 libllvm3.5-dbg lldb-3.5 llvm-3.5 llvm-3.5-dev \
      llvm-3.5-doc llvm-3.5-runtime lldb-3.5-dev
    sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.5 20
    sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-3.5 20
    sudo update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-3.5 20
    sudo update-alternatives --install /usr/bin/llvm-link llvm-link /usr/bin/llvm-link-3.5 20
    sudo apt-get install -y libz-dev libedit-dev mono-complete git mercurial cmake python-yaml
    echo -e "${textcolor}*** SMACK BUILD: Installed required packages ***${nocolor}"
    ;;

  linux-ubuntu-12*)
    echo -e "${textcolor}*** SMACK BUILD: Installing required packages ***${nocolor}"
    sudo add-apt-repository -y ppa:ubuntu-toolchain-r/test
    sudo add-apt-repository -y ppa:andykimpe/cmake
    sudo apt-get update
    sudo apt-get install -y g++-4.8
    sudo update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-4.8 20
    sudo update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-4.8 20
    sudo update-alternatives --config gcc
    sudo update-alternatives --config g++
    sudo apt-get install -y git mercurial autoconf cmake wget unzip python-yaml

    # Install mono
    echo -e "${textcolor}*** SMACK BUILD: Installing mono ***${nocolor}"

    MONO_DIR="${BASE_DIR}/mono-3"
    mkdir -p ${MONO_DIR}

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
    echo -e "${textcolor}*** SMACK BUILD: Installed required packages ***${nocolor}"
    ;;

  linux-cygwin*)
    ;;

  *)
    echo -e "${textcolor}Distribution not supported. Manually install dependencies.${nocolor}"
    exit 1
    ;;
esac

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
  cmake -DCMAKE_INSTALL_PREFIX=${LLVM_DIR}/install -DCMAKE_BUILD_TYPE=Release ../src
  make
  make install

  cd ${BASE_DIR}

  echo -e "${textcolor}*** SMACK BUILD: Installed LLVM ***${nocolor}"

fi

################################################################################

# Z3

if [ ${INSTALL_Z3} -eq 1 ]; then

  echo -e "${textcolor}*** SMACK BUILD: Installing Z3 ***${nocolor}"

  wget ${Z3_DOWNLOAD_LINK} -O z3_download.zip
  unzip -o z3_download.zip
  rm -f z3_download.zip
  mv z3-* ${Z3_DIR}

  echo -e "${textcolor}*** SMACK BUILD: Installed Z3 ***${nocolor}"

fi

################################################################################

# Boogie

if [ ${INSTALL_BOOGIE} -eq 1 ]; then

  echo -e "${textcolor}*** SMACK BUILD: Installing Boogie ***${nocolor}"

  mkdir -p ${BOOGIE_DIR}

  # Get Boogie
  hg clone -r ${BOOGIE_COMMIT} https://hg.codeplex.com/boogie ${BOOGIE_DIR}

  # Build Boogie
  cd ${BOOGIE_DIR}/Source
  mozroots --import --sync
  wget https://nuget.org/nuget.exe
  mono ./nuget.exe restore Boogie.sln
  xbuild Boogie.sln /p:Configuration=Release
  ln -s ${Z3_DIR}/bin/z3 ${BOOGIE_DIR}/Binaries/z3.exe

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
  git checkout ${CORRAL_COMMIT}

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
  ln -s ${Z3_DIR}/bin/z3 ${CORRAL_DIR}/bin/Release/z3.exe

  cd ${BASE_DIR}

  echo -e "${textcolor}*** SMACK BUILD: Installed Corral ***${nocolor}"

fi

################################################################################

# SMACK

if [ ${INSTALL_SMACK} -eq 1 ]; then

  echo -e "${textcolor}*** SMACK BUILD: Installing SMACK ***${nocolor}"

  mkdir -p ${SMACK_DIR}/build

  # Configure SMACK and build
  cd ${SMACK_DIR}/build/
  cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DLLVM_CONFIG=/usr/bin -DCMAKE_INSTALL_PREFIX=${PREFIX} -DCMAKE_BUILD_TYPE=Release ..
  make
  make install

  echo -e "${textcolor}*** SMACK BUILD: Installed SMACK ***${nocolor}"

  # Set required paths and environment variables
  export BOOGIE="mono ${BOOGIE_DIR}/Binaries/Boogie.exe"
  export CORRAL="mono ${CORRAL_DIR}/bin/Release/corral.exe"
#  export PATH=${SMACK_DIR}/install/bin:$PATH

  # Run SMACK regressions
  echo -e "${textcolor}*** SMACK BUILD: Running regressions ***${nocolor}"
  cd ${SMACK_DIR}/test
  ./regtest.py --verifier {boogie,corral}
  echo -e "${textcolor}*** SMACK BUILD: Regressions done ***${nocolor}"

  cd ${BASE_DIR}

  echo -e "${textcolor}*** SMACK BUILD: You have to set the required environment variables! ***${nocolor}"

fi

################################################################################
