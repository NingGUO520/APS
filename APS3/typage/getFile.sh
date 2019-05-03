#! /bin/bash

for f in aps3/*.aps 
do
	(echo $f ; ./toProlog $f)>> result.txt
done