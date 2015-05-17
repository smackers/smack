#!/bin/bash

INSTALLDIR=../install

#Gets rid of installation
if [[ $1 == "clean" ]]
    then
    rm ${INSTALLDIR} -rf
    exit
fi

#Gets rid of everything except sv-benchmarks, since they're big
if [[ $1 == "tidy" ]]
    then
    rm ${INSTALLDIR}/benchexec/ -rf
    rm ${INSTALLDIR}/data/ -rf
    rm ${INSTALLDIR}/inputXMLFiles/ -rf
    rm ${INSTALLDIR}/runSmackBench.sh -f
    exit
fi

#Copies things over again
if [[ $1 == "refresh" ]]
    then
    cp toInstallDir/* ${INSTALLDIR} -r
    exit
fi

##########################
# Setup cgroups
##########################
#In ubuntu 14+, this cgroup-bin seems to properly mount the various
#  copies of cgroup for each category.
#sudo apt-get update 
#sudo apt-get install cgroup-bin
#And then restart
#However, for BenchExec's actual documentation, it says to do the following:
#sudo mount -t cgroup cgroup /sys/fs/cgroup
#sudo chmod o+wt,g+w /sys/fs/cgroup/
#Also, must add "swapaccount=1" to GRUB_CMDLINE_LINUX option in /etc/default/grub
#   Then run 
#   sudo update-grub
#   Then restart
#This is by far the goofiest thing with this setup.  I've only done it once,
#   and I don't know what other issues will be encountered when done again.


##########################
# Setup install folder
##########################
mkdir -p ${INSTALLDIR}

##########################
# Get svcomp benchmarks
##########################
#Download svcomp benchmarks
svn checkout https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/ ${INSTALLDIR}/sv-benchmarks


##########################
# Prepare benchexec
##########################
#Get BenchExec package
git clone https://github.com/dbeyer/benchexec.git ${INSTALLDIR}/benchexec/
#git clone https://github.com/MontyCarter/benchexec.git ./install/
#And its dependency, tempita
wget https://pypi.python.org/packages/3.3/T/Tempita/Tempita-0.5.3dev-py3.3.egg --directory-prefix=${INSTALLDIR}
#The following extracts only the Tempita-0.5.3dev/tempita folder, and when it does so,
#  replaces the 'Tempita-0.5.3dev/' portion with 'benchexec/'.
#  In other words, it extracts just the module portion of tempita to the benchexec folder
#  -n means don't overwrite existing target files, tempita/\* means get only files in tempita dir
unzip -n ${INSTALLDIR}/Tempita-0.5.3dev-py3.3.egg tempita/\* -d ${INSTALLDIR}/benchexec/
rm ${INSTALLDIR}/Tempita-0.5.3dev-py3.3.egg
#Copy smack's BenchExec wrapper to the benchexec installation
cp toInstallDir/* ${INSTALLDIR} -r


