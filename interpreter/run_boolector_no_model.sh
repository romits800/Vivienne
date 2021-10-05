#!/bin/bash

filename=$1
rm -f /tmp/*bitwuzla.err /tmp/*bitwuzla.out /tmp/*boolector.err /tmp/*boolector.out /tmp/*cvc4.err /tmp/*cvc4.out /tmp/*z3.err /tmp/*z3.out /tmp/*yices.err /tmp/*yices.out

boolector ${filename} 1> $filename.boolector.out 2> $filename.boolector.err
ret=$?

if [ $ret -eq 1 ]; then
    echo "failed"
else
    # TODO: investigate boolectors exit values
    echo "boolector"
fi


