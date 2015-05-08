#!/bin/bash
for filename in good/*; do
	echo "-------------------------------" $filename
	cat "$filename"
	./interpreter "$filename"
	echo " "
	echo " "
	echo " "
	#./interpreter "$filename"
    #for ((i=0; i<=3; i++)); do
    #    ./MyProgram.exe "$filename" "Logs/$(basename "$filename" .txt)_Log$i.txt"
    #done
done