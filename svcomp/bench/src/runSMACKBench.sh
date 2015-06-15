#!/bin/bash

#This file executes SMACK using BenchExec, on the sv-comp benchmarks.
#
#It creates a folder called data/exec_<timestamp>/, copies input xml file 
#smack.xml into this directory, and executes benchexec, passing smack.xml
#as an argument.
#
#With the current configuration of smack.xml, this causes benchexec to execute
#smack on the sv-comp Simple set, using a limit of 4GB of memory and two cores.
#These low limits were set to enable running 4 benchmarks concurrently.
#
#The memory and core limits are set in the input xml file (smack.xml), and the
#number of concurrent threads is set here in this file.  These should be modified
#appropriately based on specs of the hardware, as well as desired accuracy of
#benchmark timing (if memory is fully allocated, swapping is likely to occur,
#which can negatively impact benchmark times).
#
#In the future, number of threads and sv-comp benchmark set should be 
#parameterized.

#Gets rid of existing results
if [[ $1 == "clean" ]]
    then
    rm data/exec* -rf
    rm data/*.bc data/*.bpl -f
    rm data/nohup.out -f
    exit
fi

#Kills all executing instances of BenchExec and smack for
# calling user
if [[ $1 == "cancel" ]]
then
    pkill -KILL -u ${USER} -f benchexec
    pkill -u ${USER} -f corral
    pkill -u ${USER} -f boogie
    pkill -u ${USER} -f z3
    exit
fi

cd data

BENCHEXECPATH=../benchexec/bin

INPUTXMLPATH=../inputXMLFiles
INPUTXMLFILE=smack.xml
INPUTXML=${INPUTXMLPATH}/${INPUTXMLFILE}

################################
# Generate folder for this run
################################
OUTFOLDER=`date +%Y.%m.%d_%H.%M.%S.%N`
OUTFOLDER=exec_${OUTFOLDER}
mkdir -p ${OUTFOLDER}

################################
# Copy over input xml file,
# while replacing {SETNAME} to
# be the target set name
################################
SETNAME=Simple
THREADCOUNT=4
sed "s/{SETNAME}/${SETNAME}/" ${INPUTXML} > ${OUTFOLDER}/${INPUTXMLFILE}



# Use nohup, so job doesn't terminate if SSH session dies
#  First, remove any existing nohup.out
rm nohup.out -f
if [[ $1 == "debug" ]]
then
    nohup ${BENCHEXECPATH}/benchexec -d ${OUTFOLDER}/${INPUTXMLFILE} -o ${OUTFOLDER}/results/ -N ${THREADCOUNT} &
else
    nohup ${BENCHEXECPATH}/benchexec ${OUTFOLDER}/${INPUTXMLFILE} -o ${OUTFOLDER}/results/ -N ${THREADCOUNT} &
fi
../checkWitnesses.py ${OUTFOLDER}
cd ..
