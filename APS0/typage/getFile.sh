#! /bin/bash

for f in aps0/*.aps 
do
	(echo $f ; ./toProlog $f)>> result.txt
done
