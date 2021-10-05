#!/bin/bash

filename=$1
rm -f /tmp/*bitwuzla.err /tmp/*bitwuzla.out /tmp/*boolector.err /tmp/*boolector.out /tmp/*cvc4.err /tmp/*cvc4.out /tmp/*z3.err /tmp/*z3.out /tmp/*yices.err /tmp/*yices.out

cvc4-1.8-x86_64-linux-opt $filename 1> $filename.cvc4.out 2> $filename.cvc4.err 
ret=$?

if [ $ret -eq 0 ]; then
    echo "cvc4"
else
    echo "failed"
fi

