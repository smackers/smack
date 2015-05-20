#!/bin/bash

# MAJOR SYSTEM CHANGES:
#  -Installs cgroups, modifies grub, requires restart
#  -Installs java7, and sets this to be primary java executable
#  -Installs ant

INSTALLDIR=../install
SRCDIR=`pwd`

#Gets rid of installation
if [[ $1 == "clean" ]]
    then
    rm ${INSTALLDIR} -rf
    echo SMACKBench Install Removed
    echo
    exit
fi

#Gets rid of everything except sv-benchmarks, since they're big
if [[ $1 == "tidy" ]]
    then
    rm ${INSTALLDIR}/benchexec/ -rf
    rm ${INSTALLDIR}/data/exec* -rf
    rm ${INSTALLDIR}/data/*.py -f
    rm ${INSTALLDIR}/data/__pycache__/ -rf
    rm ${INSTALLDIR}/inputXMLFiles/ -rf
    rm ${INSTALLDIR}/runSmackBench.sh -f
    rm ${INSTALLDIR}/cpachecker/ -rf
    echo "SMACKBench Install Removed (except for svcomp benchmarks)"
    echo
    exit
fi

#Copies things over again
if [[ $1 == "refresh" ]]
    then
    cp toInstallDir/* ${INSTALLDIR} -r
    echo SMACKBench Installation Refreshed
    echo
    exit
fi

##########################
# Setup cgroups
##########################
#In ubuntu 14+, this cgroup-bin seems to properly mount the various
#  copies of cgroup for each category.
#sudo apt-get update
#sudo apt-get install cgroup-bin -y
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
#Using export instead of clone so it isn't 6GB of DL (still 3.2GB - is it worth the extra 3 to do checkout?)
svn export https://svn.sosy-lab.org/software/sv-benchmarks/trunk/c/ ${INSTALLDIR}/data/sv-benchmarks


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


################################
# Prepare CPAchecker as witness
################################
#Update this to be the most recent stable tag
svn checkout https://svn.sosy-lab.org/software/cpachecker/tags/cpachecker-1.4/ ${INSTALLDIR}/cpachecker
JAVAVER=`java -version 2>&1 | head -n 1 | awk -F '"' '{print substr($2,0,3)}'`
JAVACVER=`javac -version 2>&1 | head -n 1 | awk -F ' ' '{print substr($2,0,3)}'`
# If java/javac not installed, or java/javac version is less than 1.7, install java 1.7
if [[ -z `which java` || -z `which javac` || (( ${JAVAVER} < 1.7 )) || (( ${JAVACVER} < 1.7 )) ]]
then
    sudo apt-get install openjdk-7-jdk -y
    sudo update-alternatives --config java
    sudo update-alternatives --config javac
fi
#If ant is not installed, install it
if [[ -z `which ant` ]]
then
    sudo apt-get install ant -y
fi

#Install CPAchecker
cd ${INSTALLDIR}/cpachecker
ant
cd ${SRCDIR}
