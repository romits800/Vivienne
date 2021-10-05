#!/bin/bash

filename=$1
rm -f /tmp/*bitwuzla.err /tmp/*bitwuzla.out /tmp/*boolector.err /tmp/*boolector.out /tmp/*cvc4.err /tmp/*cvc4.out /tmp/*z3.err /tmp/*z3.out /tmp/*yices.err /tmp/*yices.out

boolector ${filename} 1> $filename.boolector.out 2> $filename.boolector.err ; echo boolector;
ret=$?

if [ $ret -eq 0 ]; then
    echo "boolector"
else
    echo "failed"
fi


