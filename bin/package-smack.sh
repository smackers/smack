#!/bin/bash
#
# This file is distributed under the MIT License. See LICENSE for details.
#

# Note: this script requires CDE to be downloaded from
# http://www.pgbovine.net/cde.html

VERSION=1.8.1
PACKAGE=smack-$VERSION-64

# Create folder to export
mkdir $PACKAGE
cd $PACKAGE

# Create file to verify
echo int main\(void\) \{                            >> test.c
echo   int a\;                                      >> test.c
echo   a = 2\;                                      >> test.c
echo   if \(a != 3\) __VERIFIER_error\(\)\;         >> test.c
echo   return 0\;                                   >> test.c
echo \}                                             >> test.c

# Run SMACK with CDE
../cde_2011-08-15_64bit smack test.c -x svcomp --verifier corral --clang-options=-m32
../cde_2011-08-15_64bit smack test.c -x svcomp --verifier corral --clang-options=-m64
../cde_2011-08-15_64bit smack test.c -x svcomp --verifier svcomp --clang-options=-m32
../cde_2011-08-15_64bit smack test.c -x svcomp --verifier svcomp --clang-options=-m64

# Clean up temporary files
rm test.* cde.options

# Copy license file
cp ../../LICENSE .

# Create wrapper script
echo \#\!/bin/sh                                                                                   >  smack.sh
echo HERE=\"\$\(dirname \"\$\(readlink -f \"\$\{0\}\"\)\"\)\"                                      >> smack.sh
echo \$HERE/cde-package/cde-exec \'smack\' \'-x=svcomp\' \'--verifier=svcomp\' \'-q\' \"\$\@\"  >> smack.sh
chmod u+x smack.sh

# Package it up
cd ..
tar -cvzf $PACKAGE.tgz $PACKAGE
