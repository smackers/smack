#!/bin/bash

# MAJOR SYSTEM CHANGES:
#  -Installs ruby

# ParamILS tarball filename (all old version seem to be 
# downloadable from same directory)
#
# IF INCREMENTING PARAMILS VERSION, OUR CUSTOMIZED algo_specifics.rb
# MUST BE VERIFIED FOR COMPATIBILITY
#
# ALSO, INCREMENTING PARAMILS VERSIONS REQUIRES CHANGING THE NAME OF
# THE PARAMILS SOURCE FOLDER IN THE tune/src FOLDER
PARAMILSTAR=paramils2.3.8-source.tgz

# Default directory is <parent of smack project>/SMACKTune
INSTALLDIR=../../../SMACKTune
SRCDIR=`pwd`

# Gets rid of installation
if [[ $1 == "clean" ]]
    then
    # Check for alternate install dir to clean
    if [[ ! -z $2 ]] 
    then
	# Strip trailing slash, if any
	INSTALLDIR=${2%/}
    fi
    rm ${INSTALLDIR} -rf
    echo "SMACKTune Installation Removed ( ${INSTALLDIR} )"
    echo
    exit
fi

# Copies things over again
if [[ $1 == "refresh" ]]
    then
    # Check for alternate install dir to refresh
    if [[ ! -z $2 ]] 
    then
	# Strip trailing slash, if any
	INSTALLDIR=${2%/}
    fi
    cp src/* ${INSTALLDIR} -r
    echo SMACKTune Installation Refreshed
    echo
    exit
fi

# Set install dir if first argument is not empty string 
# (or "clean" or "tidy" or "refresh")
if [[ ! -z $1 ]] 
then
    # Strip trailing slash, if any
    INSTALLDIR=${1%/}
fi

# Install ruby
sudo apt-get update
sudo apt-get install ruby-full
# Install paramils
mkdir -p ${INSTALLDIR}
cd ${INSTALLDIR}
wget http://www.cs.ubc.ca/labs/beta/Projects/ParamILS/${PARAMILSTAR}
tar -zvxf ${PARAMILSTAR}
rm ${PARAMILSTAR}
cd ${SRCDIR}

# Copy over src contents
cp src/* ${INSTALLDIR} -r
