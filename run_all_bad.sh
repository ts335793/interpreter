#!/bin/bash
for filename in bad/*; do
	echo "-------------------------------" $filename
	cat "$filename"
	./interpreter "$filename"
	echo " "
	echo " "
	echo " "
done
