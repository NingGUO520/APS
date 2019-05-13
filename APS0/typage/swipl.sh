#!/bin/bash
# filename='result.txt'
# while read line; do
# reading each line
# if [[ $line != aps* ]];
# then
echo "program([const(x,int,42),echo(x)])"  | swipl -s typageAPS0.pl -g main_stdin
# fi
# done < $filename
