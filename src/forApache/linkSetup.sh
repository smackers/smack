#!/bin/bash

# This file creates a symlink in your public_html folder to the SMACKBench
# results folder.

USAGE="\n\
Usage: $0 DATAFOLDER TARGETROOT VIRTUALDIR\n\
Creates a link named VIRTUALDIR in the folder TARGETROOT\n\
which points to SMACKBench's DATAFOLDER\n\
\n\
\n\
\tDATAFOLDER -\tThe path to the data folder SMACKBench install\n\
\t\t\tdirectory (e.g., /path/to/SMACKBench/install/data)\n\n\
\tTARGETROOT -\tThe web folder where the link to the SMACKBench\n\
\t\t\tdata folder should be created\n\n\
\tVIRTUALDIR -\tThe name of the directory to be added to\n\
\t\t\tTARGETROOT\n"
if [[ ! $# -ne 3 &&  ! $# -ne 2 ]]
then
    echo -e ${USAGE}

else
    DATAFOLDER=${1%/}
    TARGETROOT=${2%/}
    if [[ -z $3 ]]
    then
	VIRTUALDIR="SMACKBench"
    else
	VIRTUALDIR=${3%/}
    fi
    if [[ ! -d ${DATAFOLDER} ]]
    then
	echo "DATAFOLDER ,$1, could not be found!"
	echo 
	echo -e ${USAGE}
	exit
    fi
    if [[ ! -d ${TARGETROOT} ]]
    then
	echo "TARGETROOT, $2, could not be found!"
	echo 
	echo -e ${USAGE}
	exit
    fi
    ln -s ${DATAFOLDER} ${TARGETROOT}/${VIRTUALDIR}
fi
