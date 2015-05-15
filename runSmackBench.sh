#!/bin/bash

if [[ $1 == "clean" ]]
    then
    rm configSmack/results -rf
    rm configSmack/scratch -rf
    rm configSmack/*.bc configSmack/*.bpl
    exit
fi

cd configSmack
if [[ $1 == "debug" ]]
    then
    ../benchexec/bin/benchexec -d smack.xml
    else
    ../benchexec/bin/benchexec smack.xml
fi
../benchexec/bin/table-generator 'results/*.xml'
cd ..
