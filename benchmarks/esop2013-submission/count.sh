for file in $(ls *.hs); do
content=`cat $file`
echo $file
lines= sloccount $file | grep "Total Physical Source"
echo $lines
python count.py $file $lines
#echo "Time = "
#time liquid $file > /dev/null | tail -n1
echo "\n"
done
