#!/bin/bash


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
cd ..
