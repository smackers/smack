#!/bin/bash

#This file translates and validates bpl files for each benchmark
#referenced by the SVCOMP *.set file passed as an argument to this
#script

USAGE="\n\
Usage: $0 SVCOMPSETFILE\n\n\
Calls SMACK on each benchmark referenced in SVCOMPSETFILE.\n\
Each benchmark is translated to a Boogie bpl file, which is\n\
then validated to ensure there are no bpl parsing, name\n\
resolution, or type check errors.
\n\
\n\
Translated bpl files are created in the same folder that each\n\
input C source file was located.
\n\
\n\
\tSVCOMPSETFILE -\tThe SVCOMP *.set file referencing the\n\
\t\t\tbenchmarks to translate and validate.\n"

if [[ $# -ne 1 ]]
then
    echo -e "\nIncorrect number of arguments: $#"
    echo -e ${USAGE}
    exit
fi
if [[ ! -f $1 ]]
then
    echo -e "\nFile does not exist:\n$1"
    echo -e ${USAGE}
    exit
fi
if [[ ${1: -4} != ".set" ]]
then
    echo -e "\nOnly .set files are supported:\n$1"
    echo -e ${USAGE}
    exit
fi

GOOD=""
BAD=""

TOTALCOUNT=0
#Loop through each wildcard file list (could also be individual file)
for i in `cat $1`
do
    #Loop through each file in wildcard list
    for j in `echo $i`
    do
	#Get total benchmark count, for progress display
	TOTALCOUNT=`expr ${TOTALCOUNT} + 1`
    done
done
CURCOUNT=0
echo
for i in `cat $1`
do
    for j in `echo $i`
    do
	#Build output bpl file path and name
	dir=`echo $j | cut -d "/" -f1`
	suffix="."`echo $j |awk -F . '{print $NF}'`
	filename=`basename $j $suffix`
	bplfile=$dir"/"$filename".bpl"
	#Execute smack with --no-verify option
	OUT=$(smack --no-verify --svcomp $j --bpl $bplfile | grep "SMACK generated invalid Boogie file")
	#Build a text list of valid and invalid files (${GOOD}, ${BAD})
	if [[ -z $OUT ]]
	then
	    GOOD="$j\n${GOOD}"
	else
	    BAD="$j\n${BAD}"
	fi
	CURCOUNT=`expr ${CURCOUNT} + 1`
	GOODCOUNT=`echo -e "${GOOD}" | wc -l`
	BADCOUNT=`echo -e "${BAD}" | wc -l`
	GOODCOUNT=`expr ${GOODCOUNT} - 1`
	BADCOUNT=`expr ${BADCOUNT} - 1`
	#Display progress, without newline (carriage return only)
	echo -ne "Completed: ${CURCOUNT} of ${TOTALCOUNT} (Valid: ${GOODCOUNT}, Invalid: ${BADCOUNT})\r"
    done
done
#Display summary showing valid count and valid file list,
#then invalid count and invalid file list
echo

echo
echo "============================================================================================="
echo Valid bpl files: ${GOODCOUNT}
echo "============================================================================================="
echo -e ${GOOD}
echo "============================================================================================="
echo Invalid bpl files: ${BADCOUNT}
echo "============================================================================================="
echo -e ${BAD}
