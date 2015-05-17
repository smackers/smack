#!/bin/bash


#Gets rid of existing results
if [[ $1 == "clean" ]]
    then
    rm executions -rf
    rm *.bc *.bpl -f
    exit
fi

BENCHEXECPATH=benchexec/bin

INPUTXMLPATH=inputXMLFiles
INPUTXMLFILE=smack.xml
INPUTXML=${INPUTXMLPATH}/${INPUTXMLFILE}

################################
# Generate folder for this run
################################
OUTFOLDER=`date +%Y.%m.%d_%H.%M.%S.%N`
OUTFOLDER=executions/exec_${OUTFOLDER}
mkdir -p ${OUTFOLDER}

################################
# Copy over input xml file
################################
cp ${INPUTXML} ${OUTFOLDER}


if [[ $1 == "debug" ]]
then
    ${BENCHEXECPATH}/benchexec -d ${OUTFOLDER}/${INPUTXMLFILE} -o ${OUTFOLDER}/results/
else
    ${BENCHEXECPATH}/benchexec ${OUTFOLDER}/${INPUTXMLFILE} -o ${OUTFOLDER}/results/
fi
${BENCHEXECPATH}/table-generator "${OUTFOLDER}/results/*.xml"
rm loopBound.bpl smack.bc

