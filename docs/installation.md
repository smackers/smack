## System Requirements and Installation


In principle SMACK can be run on any platform on which [LLVM][] and [Boogie][]
can run. In practice we have run SMACK on standard Ubuntu and openSUSE Linux
distributions, OS X, and Windows via Cygwin. Below we outline system
requirements and installation instructions for typical system configurations.
A quick way to get started without worrying about system requirements and
installation, however, is to launch our reproducible and portable development
environment using [Vagrant][]. An even quicker way to get started is to use
our prepackaged Vagrant box.

### Super-Quick Setup: Virtual Smack

Just download [vsmack](bin/vsmack) and put it in your executable path, ensure
[Vagrant][] and [VirtualBox][] are installed, and run `vsmack` directly on
your source files. For example,
````Shell
# fetch vsmack and set executable permission
wget -O ~/bin/vsmack https://raw.githubusercontent.com/smackers/smack/develop/bin/vsmack
chmod u+x ~/bin/vsmack

# fetch a source file
wget https://raw.githubusercontent.com/smackers/smack/develop/test/basic/simple.c

# run vsmack
vsmack simple.c
````

### Quick Setup: Vagrant Development Environment

SMACK can be run in a preconfigured virtual environment using [Vagrant][] and
[VirtualBox][]. Both are available for a wide range of systems, with great
installation support. The following versions are required:

* [VirtualBox][] version 4.3.20 or greater
* [Vagrant][] version 1.7.2 or greater

Once both are properly installed, launch [Vagrant][] by running the following
command in SMACK.s root directory (that which contains `Vagrantfile`):
````Shell
vagrant up
````
This can take a few minutes the first time around, since it includes the
download of a virtual machine image and the installation of several other
packages. When this step finishes, our virtual machine should be up and
running; verify this with the `vagrant status` command. Then open a shell to
the running virtual machine via SSH:
````Shell
vagrant ssh
````
and proceed to using SMACK. When finished, simply close the SSH
session, and halt, suspend, or destroy the virtual machine:
````Shell
vagrant destroy
````

### General System Requirements

SMACK depends on the following projects:

* [LLVM][] version [3.9.1][LLVM-3.9.1]
* [Clang][] version [3.9.1][Clang-3.9.1]
* [Python][] version 2.7 or greater
* [Mono][] version 5.0.0 or greater (except on Windows)
* [Z3][] or compatible SMT-format theorem prover
* [Boogie][] or [Corral][] or compatible Boogie-format verifier

See [here](https://github.com/smackers/smack/blob/master/bin/versions) for
compatible version numbers of [Boogie][] and [Corral][]. See the appropriate
installation instructions below for installing these requirements.

### Installation on Linux

Some distributions of Linux may have various SMACK dependencies like [Python][]
installed out of the box. Nevertheless it is important to ensure that the
required version numbers, as indicated above, are installed and selected for
use. Generally speaking, apart from [Z3][], [Boogie][], and [Corral][], these
dependencies can be installed via the system.s default package manager, such as
`apt-get`, `rpm`, or `yast`. In some cases, it may be necessary to specify
alternate package repositories for the system.s default package manager, or to
subvert the package manager altogether, and download, compile, and install the
required project manually. The [Z3][], [Boogie][], and [Corral][] projects are
generally not indexed by Linux package managers, and must be installed manually.

To facilitate the installation of SMACK and its requirements, we provide an
automated [build.sh][] script in `bin/build.sh`. Running this script on a fresh
installation of Ubuntu or openSUSE Linux should actually result in the full
installation of SMACK and its requirements. However, we do not expect this
script to work out of the box on all configurations. Instead, it can be used as
reference guidelines for manual installation.

### Installation on OS X

The general instructions for installation on OS X mainly follow those above for
Linux, and are outlined in our automated [build.sh][] script in `bin/build.sh`.
Note however that `bin/build.sh` does not run on OS X . it can only be used as
reference guidelines.

In addition to the requirements above, installing SMACK and its dependencies
requires the Command Line Tools for [Xcode][]. Generally speaking, apart from
[Mono][], [Z3][], [Boogie][], and [Corral][], dependencies can be installed via
the [Homebrew][] package manager. [Mono][] can be installed from binaries
either from the [Mono][] download page, or via [Homebrew Cask][].

### Installation on Windows/Cygwin

The general instructions for installation on Windows using [Cygwin][] mainly
follow those above for Linux, and are outlined in our automated [build.sh][]
script in `bin/build.sh`. Note however that an actual [.NET][] Framework and
SDK should be present in place of the [Mono][] emulator, and that prebuilt
[Z3][], [Boogie][], and [Corral][] may be installed via their Windows
installers rather than built from source.

**NOTE** Although we have not pinpointed the problem exactly, building [LLVM][]
and [Clang][] is problematic on some [Cygwin][] configurations. Please consult
[LLVM][] documentation in case of any issues.

### Installing SMACK Itself

SMACK is built using [CMake][] via the following sequence of shell commands
from SMACK.s root directory:
````Shell
mkdir build
cd build
cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=Debug ..
make install
````
Note that the `llvm-config` binary must be in your executable `PATH`.
To specify an install location `PREFIX` other than the default installation
prefix, add the additional flag:
````Shell
-DCMAKE_INSTALL_PREFIX=PREFIX
````
substituting the string `PREFIX` for the desired location.

Actually running SMACK relies on the environment variables `BOOGIE` and
`CORRAL` targeting the `Boogie.exe` and `corral.exe` executables, for instance
residing in paths prefixed by `XXX` and `YYY`:
````Shell
export BOOGIE="mono /XXX/Boogie/Binaries/Boogie.exe"
export CORRAL="mono /YYY/Corral/bin/Release/corral.exe"
````
Source the preceding lines in your shell.s `.profile`, and ensure they invoke
Boogie/Corral correctly. For example, running
````Shell
BOOGIE
````
should result in
````
*** Error: No input files were specified.
````
printed to standard output.

Finally, note that the following LLVM and Clang binaries must be in your
executable path: `clang`, `llvm-config`, `llvm-link`.

### Verifying the SMACK Installation

To ensure SMACK has been installed properly, run the regression tests from the
shell in the `test` directory by executing
````Shell
./regtest.py
````

[Vagrant]: https://www.vagrantup.com
[VirtualBox]: https://www.virtualbox.org
[CMake]: http://www.cmake.org
[Python]: http://www.python.org
[LLVM]: http://llvm.org
[LLVM-3.9.1]: http://llvm.org/releases/download.html#3.9.1
[Clang]: http://clang.llvm.org
[Clang-3.9.1]: http://llvm.org/releases/download.html#3.9.1
[Boogie]: https://github.com/boogie-org/boogie
[Corral]: https://corral.codeplex.com/
[Z3]: https://github.com/Z3Prover/z3/
[Mono]: http://www.mono-project.com/
[Cygwin]: https://www.cygwin.com
[.NET]: https://msdn.microsoft.com/en-us/vstudio/aa496123.aspx
[build.sh]: https://github.com/smackers/smack/blob/master/bin/build.sh
[Xcode]: https://developer.apple.com/xcode/
[Homebrew]: http://brew.sh/
[Homebrew Cask]: http://caskroom.io
