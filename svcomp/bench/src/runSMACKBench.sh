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

USAGE="
Usage:
    ./runSMACKBench.sh cancel                     -Kills all SMACKBench instances
 or ./runSMACKBench.sh clean                      -Deletes all SMACKBench results
 or ./runSMACKBench.sh SET XMLIN THREADS THREADMEM [debug]  -Executes SMACKBench

Parameters:
    SET        The svcomp category set to benchmark
    XMLIN      The input xml file specifying the parameters to run with
    THREADS    The number of concurrent tests to run
    THREADMEM  The amount of memory to allocate to each thread


Options:
    debug      Runs BenchExec with the debug option"

#Gets rid of existing results
if [[ $1 == "clean" ]]
    then
    rm data/exec* -rf
    rm data/*.bc data/*.bpl data/*.c data/*.log -f
    rm data/nohup*.out -f
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

################################
# Validate input args
################################
if [[ -z $1 ]]
then
    echo "You must specify an svcomp set to benchmark!"
    echo "$USAGE"
    exit
fi
if [[ -z $2 ]]
then
    echo "You must specify an parameter set (input xml file)!"
    echo "$USAGE"
    exit
fi
if [[ -z $3 ]]
then
    echo "You must specify the number of concurrent tests to run!"
    echo "$USAGE"
    exit
fi
if [[ -z $4 ]]
then
    echo "You must specify the number of concurrent tests to run!"
    echo "$USAGE"
    exit
fi

cd data

SETNAME=$1
INPUTXMLFILE=$2
THREADCOUNT=$3
MEMLIMIT=$4
CORELIMIT=2


BENCHEXECPATH=../benchexec/bin
INPUTXMLPATH=../inputXMLFiles
INPUTXML=${INPUTXMLPATH}/${INPUTXMLFILE}

################################
# Generate folder for this run
################################
OUTFOLDER=`date +%Y.%m.%d_%H.%M.%S.%N`
OUTFOLDER=exec_${OUTFOLDER}_${SETNAME}
mkdir -p ${OUTFOLDER}

################################
# Copy over input xml file,
# while replacing {SETNAME} to
# be the target set name
################################
sed "s/{SETNAME}/${SETNAME}/" ${INPUTXML} > ${OUTFOLDER}/${INPUTXMLFILE}
sed -i "s/{MEMLIMIT}/${MEMLIMIT}/" ${OUTFOLDER}/${INPUTXMLFILE}
sed -i "s/{CORELIMIT}/${CORELIMIT}/" ${OUTFOLDER}/${INPUTXMLFILE}

if [[ $5 == "debug" ]]
then
    ${BENCHEXECPATH}/benchexec -d ${OUTFOLDER}/${INPUTXMLFILE} -o ${OUTFOLDER}/results/ -N ${THREADCOUNT}
else
    ${BENCHEXECPATH}/benchexec ${OUTFOLDER}/${INPUTXMLFILE} -o ${OUTFOLDER}/results/ -N ${THREADCOUNT}
fi
../checkWitnesses.py ${OUTFOLDER}
cd ..
