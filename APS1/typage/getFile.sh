#! /bin/bash

for f in aps1/*.aps 
do
	(echo $f ; ./toProlog $f)>> result.txt
done
