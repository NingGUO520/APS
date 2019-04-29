#! /bin/bash

for f in aps2/*.aps 
do
	(echo $f ; ./toProlog $f)>> result.txt
done