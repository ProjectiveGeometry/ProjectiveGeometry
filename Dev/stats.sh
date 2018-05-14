#!/bin/sh

echo "-------------------------------------------------------------------------\n"
echo "------------------------------ Script de stats --------------------------\n"
echo "-------------------------------------------------------------------------\n\n"

if [ -f stats.txt ]
then
	rm -rf stats.txt
fi

if test $# -eq 0
then
     echo "Pas d'argument"
else
	coqwc $1/*.v
    files=$(ls *.v)
    echo $files
    for i in $files
    do
		lemmes=$(awk '$1 == "Lemma"{print $2}' $i)
		for j in $lemmes
		do
			occ=$(grep $j *.v | wc -l)
			jocc="$j $occ"
			echo $jocc >> stats.txt
		done
	done
fi

