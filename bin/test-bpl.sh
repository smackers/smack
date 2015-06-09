GOOD=""
BAD=""

TOTALCOUNT=0
for i in `cat $1`
do
    for j in `echo $i`
    do
	TOTALCOUNT=`expr ${TOTALCOUNT} + 1`
    done
done
CURCOUNT=0
echo
for i in `cat $1`
do
  for j in `echo $i`
  do
    dir=`echo $j | cut -d "/" -f1`
    suffix="."`echo $j |awk -F . '{print $NF}'`
    filename=`basename $j $suffix`
    bplfile=$dir"/"$filename".bpl"
    OUT=$(smack.py --no-verify --svcomp $j --bpl $bplfile | grep "SMACK generated invalid Boogie file")
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
    echo -ne "Completed: ${CURCOUNT} of ${TOTALCOUNT} (Valid: ${GOODCOUNT}, Invalid: ${BADCOUNT})\r"
  done
done
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
