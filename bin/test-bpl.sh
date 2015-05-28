for i in `cat $1`
do
  for j in `echo $i`
  do
  echo "============================================================================================="
  echo $j
  echo "============================================================================================="
    dir=`echo $j | cut -d "/" -f1`
    suffix="."`echo $j |awk -F . '{print $NF}'`
    filename=`basename $j $suffix`
    bplfile=$dir"/"$filename".bpl"
    bcfile=$dir"/"$filename".bc"
    smack-boogie.py --verifier=boogie $j -o $bplfile --bc $bcfile
    #echo $bplfile
    #echo $bcfile
  done
done
