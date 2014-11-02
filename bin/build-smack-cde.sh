#!/bin/bash

#Set up dir to export
mkdir smack-cde
cd smack-cde

# Create file to verify
echo \#include \"smack.h\"        >  test.c
echo int main\(void\) \{          >> test.c
echo   int a\;                    >> test.c
echo   a = 2\;                    >> test.c
echo   __SMACK_assert\(a == 3\)\; >> test.c
echo   return 0\;                 >> test.c
echo \}                           >> test.c

# !!!Generalize this, so we don't need to know current version number?
wget https://github.com/downloads/pgbovine/CDE/cde_2011-08-15_64bit

# !!!Generalize this
mv cde_2011-08-15_64bit cde

chmod u+x cde

# Run cde
./cde smack-verify.py test.c --verifier corral
./cde smack-verify.py test.c --verifier boogie-inline

# Clean up smack-verify junk
rm corral* a.bpl test.* cde cde.options

# Create wrapper script
echo \#\!/bin/sh                                                >  smack-verify.sh
echo HERE=\"\$\(dirname \"\$\(readlink -f \"\$\{0\}\"\)\"\)\"   >> smack-verify.sh
echo \$HERE/cde-package/cde-exec \'smack-verify.py\' \"\$\@\"   >> smack-verify.sh
chmod u+x smack-verify.sh

# tar it up
cd ..
tar -cvf smack-cde.tar smack-cde/
gzip smack-cde.tar
