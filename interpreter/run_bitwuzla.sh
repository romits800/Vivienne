#!/bin/bash

filename=$1
rm -f /tmp/*bitwuzla.err /tmp/*bitwuzla.out /tmp/*boolector.err /tmp/*boolector.out /tmp/*cvc4.err /tmp/*cvc4.out /tmp/*z3.err /tmp/*z3.out /tmp/*yices.err /tmp/*yices.out

sed "s/(get-model)//" $filename > ${filename}.bool

bitwuzla -m ${filename}.bool 1> $filename.bitwuzla.out 2> $filename.bitwuzla.err
ret=$?

if [ $ret -eq 0 ]; then
    echo "bitwuzla"
else
    echo "failed"
fi

rm ${filename}.bool
