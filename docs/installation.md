## System Requirements and Installation


In principle SMACK can be run on any platform on which [LLVM][] and [Boogie][]
can run. In practice we have run SMACK on standard Ubuntu and openSUSE Linux
distributions, OS X, and Windows. Below we outline system
requirements and installation instructions for typical system configurations.
A quick way to get started without worrying about system requirements and
installation, however, is to launch our reproducible and portable development
environment using [Vagrant][]. An even quicker way to get started is to use
our prepackaged Docker container.

### Quick Setup 1: Vagrant Development Environment

SMACK can be run in a preconfigured virtual environment using [Vagrant][] and
[VirtualBox][]. Both are available for a wide range of systems, with great
installation support. The following versions are required:

* [VirtualBox][] version 4.3.20 or greater
* [Vagrant][] version 1.7.2 or greater

Once both are properly installed, launch [Vagrant][] by running the following
command in SMACK's root directory (that which contains `Vagrantfile`):
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

### Quick Setup 2: Docker

SMACK can also be run in a [Docker][] container. We tested the Dockerfile on
the following configurations:

* Ubuntu 18.04, Docker version 19.03.6
* Windows WSL Ubuntu 20.04, Docker Desktop with Docker engine version 20.10.2

#### Docker Hub

SMACK's Docker container images can be pulled from Docker Hub directly:

```shell
docker pull smackers/smack:stable # built from the main branch
docker pull smackers/smack:latest # built from the develop branch
```

#### Local Build

Once Docker is successfully installed, build the Docker image by running the
following command in SMACK's root directory that contains `Dockerfile`:
```Shell
docker build . -t smack
```
After the image is successfully built, invoke a Docker container by running the
following command:
```Shell
docker run -it smack
```
For more advanced usages of Docker (e.g., to mount host directories), please refer
to Docker's official documentation.

### General System Requirements

SMACK depends on the following projects:

* [LLVM][] version [12.0.1][LLVM-12.0.1]
* [Clang][] version [12.0.1][Clang-12.0.1]
* [Boost][] version 1.55 or greater
* [Python][] version 3.6.8 or greater
* [Ninja][] version 1.5.1 or greater
* [Z3][] or compatible SMT-format theorem prover
* [Boogie][] or [Corral][] or compatible Boogie-format verifier
* [sea-dsa][]

See [here](https://github.com/smackers/smack/blob/main/bin/versions) for
compatible version numbers of [Boogie][] and [Corral][]. See the appropriate
installation instructions below for installing these requirements.

### Installation on Linux

Some distributions of Linux may have various SMACK dependencies like [Python][]
installed out of the box. Nevertheless it is important to ensure that the
required version numbers, as indicated above, are installed and selected for
use. Generally speaking, apart from [Z3][], [Boogie][], and [Corral][], these
dependencies can be installed via the system's default package manager, such as
`apt-get`, `rpm`, or `yast`. In some cases, it may be necessary to specify
alternate package repositories for the system's default package manager, or to
subvert the package manager altogether, and download, compile, and install the
required project manually. The [Z3][], [Boogie][], and [Corral][] projects are
generally not indexed by Linux package managers, and must be installed manually.

To facilitate the installation of SMACK and its requirements, we provide an
automated [build.sh][] script in `bin/build.sh`. Running this script on a fresh
installation of Ubuntu or openSUSE Linux should actually result in the full
installation of SMACK and its requirements, apart from setting the required
environment variables in your shell's `.profile`. However, we do not expect
this script to work out of the box on all configurations. Instead, it can be
used as reference guidelines for manual installation.

**NOTE** A common omission is to forget to set the required environment
variables after the installation process, as indicated in the end of the build
script.  Alternatively, you can read how to accomplish this below.

### Installation on OS X

The general instructions for installation on OS X mainly follow those above for
Linux, and are outlined in our automated [build.sh][] script in `bin/build.sh`.
Note however that `bin/build.sh` does not run on OS X . It can only be used as
reference guidelines.

In addition to the requirements above, installing SMACK and its dependencies
requires the Command Line Tools for [Xcode][]. Generally speaking, apart from
[Mono][], [Z3][], [Boogie][], and [Corral][], dependencies can be installed via
the [Homebrew][] package manager. [Mono][] can be installed from binaries
either from the [Mono][] download page, or via [Homebrew Cask][].

### Installation on Windows

SMACK can be installed on the Windows Subsystem for Linux (WSL) by following the
same procedure as the Linux installation (i.e., via the build script [build.sh][]).
We tested the WSL installation on Windows 10 (Build 18362) with Ubuntu 16.04
installed via the Microsoft Store.

### Installing SMACK Itself

The prerequisite step for building SMACK is to fetch its submodule
(i.e., [sea-dsa][]). Then, it is built using [CMake][]. Both steps can be done
via the following sequence of shell commands from SMACK's root directory:
```Shell
# fetch the submodule
git submodule init
git submodule update
# build SMACK
mkdir build
cd build
cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=Debug .. -G Ninja
ninja install
````
Note that the `llvm-config` binary must be in your executable `PATH`.
To specify an install location `PREFIX` other than the default installation
prefix, add the additional flag:
````Shell
-DCMAKE_INSTALL_PREFIX=PREFIX
````
substituting the string `PREFIX` for the desired location.

Actually running SMACK relies on `boogie` and `corral` being in the executable
path. For instance, if you have built Boogie and Corral from source at paths
at `$BOOGIE_SOURCE` and `$CORRAL_SOURCE`:
````bash
export PATH="$BOOGIE_SOURCE/Binaries:$PATH"
export PATH="$CORRAL_SOURCE/bin:$PATH"
````
Source the preceding lines in your shell's `.profile`, and ensure they invoke
Boogie/Corral correctly. For example, running
````console
$ boogie
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
[LLVM-12.0.1]: http://llvm.org/releases/download.html#12.0.1
[Clang]: http://clang.llvm.org
[Clang-12.0.1]: http://llvm.org/releases/download.html#12.0.1
[Boogie]: https://github.com/boogie-org/boogie
[Corral]: https://github.com/boogie-org/corral
[Z3]: https://github.com/Z3Prover/z3/
[Mono]: http://www.mono-project.com/
[Cygwin]: https://www.cygwin.com
[.NET]: https://msdn.microsoft.com/en-us/vstudio/aa496123.aspx
[build.sh]: https://github.com/smackers/smack/blob/main/bin/build.sh
[Xcode]: https://developer.apple.com/xcode/
[Homebrew]: http://brew.sh/
[Homebrew Cask]: https://formulae.brew.sh/cask/
[Docker]: https://www.docker.com
[Ninja]: https://ninja-build.org
[sea-dsa]: https://github.com/seahorn/sea-dsa
[Boost]: http://boost.org/
