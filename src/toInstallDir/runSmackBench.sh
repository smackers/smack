#!/bin/bash


#Gets rid of existing results
if [[ $1 == "clean" ]]
    then
    rm data/exec* -rf
    rm *.bc *.bpl -f
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
sed "s/{SETNAME}/${SETNAME}/" ${INPUTXML} > ${OUTFOLDER}/${SETNAME}_input.xml



if [[ $1 == "debug" ]]
then
    ${BENCHEXECPATH}/benchexec -d ${OUTFOLDER}/${SETNAME}_input.xml -o ${OUTFOLDER}/results/
else
    ${BENCHEXECPATH}/benchexec ${OUTFOLDER}/${SETNAME}_input.xml -o ${OUTFOLDER}/results/
fi
cd ..
