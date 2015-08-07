#!/bin/bash

errorMsg="Run takes either 'clean' to clean all bpl & bc files, or a non-negative number of concurrent runs to execute"

PARAMILSDIR=../paramils2.3.8-source
PARAMILSEXE=param_ils_2_3_run.rb

if ! [[ -n $1 ]]
then
    echo $errorMsg
    exit
fi

#Clean before each run, to ensure *.bpl's and *.bc's are fresh
#rm ./smackConfig/__pycache__ -rf &> /dev/null
rm ./smackConfig/*.bc ./smackConfig/benchmarks/*.bc ./smackConfig/benchmarks/*.bpl &> /dev/null

# Make sure the argument is either `clean` or a number of concurrent executions
# to run
if [ "$1" == "clean" ]
then
    exit
else
    re='^[0-9]+$'
    if ! [[ $1 =~ $re && $1 -gt 0  ]]
    then
	echo $errorMsg
	exit
    fi
	
fi

cd smackConfig

#Generate instance file reference times for this hardware, if it doesn't exist
if [ ! -f instanceSmack.txt ]
    then
    echo "============================"
    echo "| Generating Instance File |"
    echo "============================"
    echo
    ./generateInstanceFile.py benchmarks
    echo
    echo
    #Clean after generating instance reference timings,
    #  to ensure *.bpl's and *.bc's are fresh
    rm ./*.bc ./benchmarks/*.bc ./smackConfig/benchmarks/*.bpl
fi


echo "============================"
echo "| Running ParamILS         |"
echo "============================"
echo
let runCount=$1
if [ $runCount = 1 ]
    then
    #If only 1, don't send to background
    ruby ${PARAMILSDIR}/${PARAMILSEXE} -numRun 0 -userunlog 1 -scenariofile scenarioSmack.txt -validN 1000 -pruning 0
else
    while [ $runCount -gt 0 ]; do
	let runCount=runCount-1
	ruby ${PARAMILSDIR}/{$PARAMILSEXE} -numRun $runCount -userunlog 1 -scenariofile scenarioSmack.txt -validN 1000 -pruning 0 &
    done
fi

cd ..
