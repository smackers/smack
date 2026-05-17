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
# - LLVM / Clang
# - Boost
# - Z3
# - Boogie
# - Corral
#
# Symbooglix, lockpwn, CVC4, Yices2, and Mono support were removed in the
# Phase 1 modernization. Boogie + Corral run on dotnet (>=8.0); Z3 is the
# only SMT solver.
#
################################################################################

# Set these flags to control various installation options
INSTALL_DEPENDENCIES=${INSTALL_DEPENDENCIES:-1}
INSTALL_Z3=${INSTALL_Z3:-1}
INSTALL_BOOGIE=${INSTALL_BOOGIE:-1}
INSTALL_CORRAL=${INSTALL_CORRAL:-0}
BUILD_SMACK=${BUILD_SMACK:-1}
TEST_SMACK=${TEST_SMACK:-1}
INSTALL_LLVM=${INSTALL_LLVM:-1}
BUILD_LLVM=${BUILD_LLVM:-0} # LLVM is typically installed from packages (see below)

# Support for more programming languages
INSTALL_OBJECTIVEC=${INSTALL_OBJECTIVEC:-0}
INSTALL_RUST=${INSTALL_RUST:-0}

# Development dependencies
INSTALL_DEV_DEPENDENCIES=${INSTALL_DEV_DEPENDENCIES:-0}

# PATHS
SMACK_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && cd .. && pwd )"
ROOT_DIR="$( cd "${SMACK_DIR}" && cd .. && pwd )"
DEPS_DIR="${ROOT_DIR}/smack-deps"
Z3_DIR="${DEPS_DIR}/z3"
BOOGIE_DIR="${DEPS_DIR}/boogie"
CORRAL_DIR="${DEPS_DIR}/corral"
LLVM_DIR="${DEPS_DIR}/llvm"

source ${SMACK_DIR}/bin/versions

SMACKENV=${ROOT_DIR}/smack.environment
WGET="wget --no-verbose"
Z3_DOWNLOAD_LINK=${Z3_DOWNLOAD_LINK:-"https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-${Z3_GLIBC_VERSION}.zip"}

# Install prefix -- system default is used if left unspecified
INSTALL_PREFIX=
CONFIGURE_INSTALL_PREFIX=
CMAKE_INSTALL_PREFIX=

# Partial list of dependencies; the rest are added depending on the platform
DEPENDENCIES="git cmake python3-yaml python3-psutil python3-toml unzip wget ninja-build apt-transport-https dotnet-sdk-8.0 libboost-all-dev"

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

# ================================================================
# Check if git repo is up to date.
# ================================================================
function upToDate {
  if [ ! -d "$1/.git" ] ; then
    return 1
  else
    cd $1
    hash=$(git rev-parse --short=10 HEAD)
    if [ $hash == $2 ] ; then
      return 0
    else
      return 1
    fi
  fi
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
  if [ ${INSTALL_LLVM} -eq 1 ] ; then
    DEPENDENCIES+=" llvm-clang llvm-devel"
  fi
  DEPENDENCIES+=" gcc-c++ make"
  DEPENDENCIES+=" ncurses-devel"
  ;;

linux-@(ubuntu|neon)-@(24|25)*)
  if [ ${INSTALL_LLVM} -eq 1 ] ; then
    DEPENDENCIES+=" clang-${LLVM_SHORT_VERSION} llvm-${LLVM_SHORT_VERSION}-dev"
  fi
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
    echo export PATH=\"${INSTALL_PREFIX}/bin:\$PATH\" >> ${SMACKENV}
    shift
    shift
    ;;

  *)
    puts "Unknown option: $1"
    exit 1
    ;;
  esac
done


if [ ${INSTALL_DEPENDENCIES} -eq 1 ] ; then
  puts "Installing required packages"

  case "$distro" in
  linux-opensuse*)
    sudo zypper --non-interactive install ${DEPENDENCIES}
    ;;

  linux-@(ubuntu|neon)-@(24|25)*)
    # Aggressive scope: 24.04 LTS (noble) is the floor. Older Ubuntu
    # releases ship glibc < 2.39, which breaks the pinned Z3 binary
    # download and the LLVM 22 apt suite layout.
    RELEASE_VERSION=$(get-platform-trim "$(lsb_release -r)" | awk -F: '{print $2;}')
    case "$RELEASE_VERSION" in
    24*)
      UBUNTU_CODENAME="noble"
      ;;
    25.04*)
      UBUNTU_CODENAME="plucky"
      ;;
    25.10*)
      UBUNTU_CODENAME="questing"
      ;;
    *)
      puts "Release ${RELEASE_VERSION} for ${distro} not supported. SMACK requires Ubuntu 24.04 LTS or newer."
      exit 1
      ;;
    esac

    if [ ${INSTALL_OBJECTIVEC} -eq 1 ] ; then
      sudo apt-get install -y gobjc gnustep gnustep-make gnustep-common gnustep-devel
    fi

    # Adding LLVM repository
    if [ ${INSTALL_LLVM} -eq 1 ] ; then
      sudo install -d -m 0755 /etc/apt/keyrings
      ${WGET} -qO- https://apt.llvm.org/llvm-snapshot.gpg.key | sudo tee /etc/apt/keyrings/apt.llvm.org.asc >/dev/null
      LLVM_APT_SUITE="llvm-toolchain-${UBUNTU_CODENAME}-${LLVM_SHORT_VERSION}"
      echo "deb [signed-by=/etc/apt/keyrings/apt.llvm.org.asc] http://apt.llvm.org/${UBUNTU_CODENAME}/ ${LLVM_APT_SUITE} main" | sudo tee /etc/apt/sources.list.d/apt.llvm.org.list
    fi

    # Adding .NET repository
    ${WGET} -q https://packages.microsoft.com/config/ubuntu/${RELEASE_VERSION}/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
    sudo dpkg -i packages-microsoft-prod.deb
    rm -f packages-microsoft-prod.deb
    sudo apt-get update

    sudo apt-get install -y ${DEPENDENCIES}
    ;;

  *)
    puts "Distribution ${distro} not supported. Dependencies must be installed manually."
    exit 1
    ;;
  esac

  puts "Installed required packages"
fi


if [ ${BUILD_LLVM} -eq 1 ] ; then
  puts "Building LLVM"
  mkdir -p ${LLVM_DIR}/src
  mkdir -p ${LLVM_DIR}/build
  ${WGET} https://github.com/llvm/llvm-project/releases/download/llvmorg-${LLVM_FULL_VERSION}/llvm-project-${LLVM_FULL_VERSION}.src.tar.xz

  tar -C ${LLVM_DIR}/src -xvf llvm-project-${LLVM_FULL_VERSION}.src.tar.xz --strip 1

  cd ${LLVM_DIR}/build/
  cmake -G "Unix Makefiles" ${CMAKE_INSTALL_PREFIX} \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_ENABLE_PROJECTS="clang;compiler-rt" ../src/llvm
  make
  sudo make install
  puts "Built LLVM"
fi


if [ ${INSTALL_OBJECTIVEC} -eq 1 ] ; then
  puts "Installing Objective-C"
  # The version numbers here will have to change by OS
  sudo ln -s /usr/lib/gcc/x86_64-linux-gnu/4.8/include/objc /usr/local/include/objc
  echo ". /usr/share/GNUstep/Makefiles/GNUstep.sh" >> ${SMACKENV}
  puts "Installed Objective-C"
fi


if [ ${INSTALL_RUST} -eq 1 ] ; then
  puts "Installing Rust"
  if ! [ -x "$(command -v rustup)" ]; then
      ${WGET} -O - --secure-protocol=TLSv1_2 https://sh.rustup.rs | bash -s -- -y
      source $HOME/.cargo/env
  fi
  rustup toolchain install ${RUST_VERSION}
  cargo install rustfilt
  puts "Installed Rust"
fi


if [ ${INSTALL_Z3} -eq 1 ] ; then
  if [ ! -d "$Z3_DIR" ] ; then
    puts "Installing Z3"
    mkdir -p ${Z3_DIR}
    ${WGET} ${Z3_DOWNLOAD_LINK} -O z3-downloaded.zip
    unzip -o z3-downloaded.zip -d z3-extracted
    mv -f --backup=numbered z3-extracted/z3-*/* ${Z3_DIR}
    rm -rf z3-downloaded.zip z3-extracted
    puts "Installed Z3"
  else
    puts "Z3 already installed"
  fi
  echo export PATH=\"${Z3_DIR}/bin:\$PATH\" >> ${SMACKENV}
fi


if [ ${INSTALL_BOOGIE} -eq 1 ] ; then
  if [ ! -d "$BOOGIE_DIR" ] ; then
    puts "Installing Boogie"
    dotnet tool install Boogie --tool-path ${BOOGIE_DIR} --version ${BOOGIE_VERSION}
    puts "Installed Boogie"
  else
    puts "Boogie already installed"
  fi
  echo export PATH=\"${BOOGIE_DIR}:\$PATH\" >> ${SMACKENV}
fi


if [ ${INSTALL_CORRAL} -eq 1 ] ; then
  if [ ! -d "$CORRAL_DIR" ] ; then
    puts "Installing Corral"
    dotnet tool install Corral --tool-path ${CORRAL_DIR} --version ${CORRAL_VERSION}
    puts "Installed Corral"
  else
    puts "Corral already installed"
  fi
  echo export PATH=\"${CORRAL_DIR}:\$PATH\" >> ${SMACKENV}
fi


if [ ${INSTALL_DEV_DEPENDENCIES} -eq 1 ] ; then
  sudo apt-get install -y python3-pip clang-format-${LLVM_SHORT_VERSION}
  sudo pip3 install -U flake8
  if [ "${GITHUB_ACTIONS}" = "true" ] ; then
    exit 0
  fi
fi


if [ ${BUILD_SMACK} -eq 1 ] ; then
  puts "Building SMACK"

  cd ${SMACK_DIR}
  git submodule init
  git submodule update

  mkdir -p ${SMACK_DIR}/build
  cd ${SMACK_DIR}/build
  cmake -DCMAKE_CXX_COMPILER=clang++-${LLVM_SHORT_VERSION} \
        -DCMAKE_C_COMPILER=clang-${LLVM_SHORT_VERSION} ${CMAKE_INSTALL_PREFIX} \
        -DCMAKE_BUILD_TYPE=Debug .. -G Ninja
  ninja

  if [ -n "${CMAKE_INSTALL_PREFIX}" ] ; then
    ninja install
  else
    sudo ninja install
  fi

  puts "Configuring shell environment"
  source ${SMACKENV}
  puts "The required environment variables have been set in ${SMACKENV}"
  puts "You should source ${SMACKENV} in your .bashrc"

  puts "Built SMACK"
fi


if [ ${TEST_SMACK} -eq 1 ] ; then
  puts "Running SMACK regression tests"

  cd ${SMACK_DIR}/test
  SMACK_TEST_PREFIX="${INSTALL_PREFIX:-/usr/local}"
  SMACK_TEST_OUTPUT_DIR="${SMACK_TEST_OUTPUT_DIR:-${SMACK_DIR}/build/regtest}"
  PATH="${SMACK_TEST_PREFIX}/bin:${BOOGIE_DIR}:${Z3_DIR}/bin:${PATH}" \
    ./regtest.py --verifier="${REGTEST_VERIFIER:-boogie}" \
      --output-dir "${SMACK_TEST_OUTPUT_DIR}" ${REGTEST_ENV}
  res=$?

  puts "Regression tests complete"
fi

exit $res
