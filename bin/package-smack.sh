#!/bin/bash

# Note: this script requires CDE to be downloaded from
# http://www.pgbovine.net/cde.html

VERSION=1.4.1
PACKAGE=smack-$VERSION-64

# Create folder to export
mkdir $PACKAGE
cd $PACKAGE

# Create file to verify
echo \#include \"smack.h\"        >  test.c
echo int main\(void\) \{          >> test.c
echo   int a\;                    >> test.c
echo   a = 2\;                    >> test.c
echo   assert\(a == 3\)\;         >> test.c
echo   return 0\;                 >> test.c
echo \}                           >> test.c

# Run SMACK with CDE
../cde_2011-08-15_64bit smackverify.py test.c --verifier boogie
../cde_2011-08-15_64bit smackverify.py test.c --verifier corral
../cde_2011-08-15_64bit smackverify.py test.c --verifier duality

# Clean up temporary files
rm corral* a.bpl test.* cde.options

# Copy license file
cp ../../LICENSE .

# Create wrapper script
echo \#\!/bin/sh                                                >  smackverify.sh
echo HERE=\"\$\(dirname \"\$\(readlink -f \"\$\{0\}\"\)\"\)\"   >> smackverify.sh
echo \$HERE/cde-package/cde-exec \'smackverify.py\' \"\$\@\"    >> smackverify.sh
chmod u+x smackverify.sh

# Package it up
cd ..
tar -cvzf $PACKAGE.tgz $PACKAGE

