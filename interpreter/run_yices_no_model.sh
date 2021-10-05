#!/bin/bash

filename=$1
rm -f /tmp/*bitwuzla.err /tmp/*bitwuzla.out /tmp/*boolector.err /tmp/*boolector.out /tmp/*cvc4.err /tmp/*cvc4.out /tmp/*z3.err /tmp/*z3.out /tmp/*yices.err /tmp/*yices.out

yices-smt2 $filename 1> $filename.yices.out 2> $filename.yices.err
ret=$?

if [ $ret -eq 0 ]; then
    echo "yices"
else
    echo "failed"
fi

