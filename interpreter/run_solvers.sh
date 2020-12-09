#!/bin/bash

filename=$1

{ cvc4-1.8-x86_64-linux-opt -m $filename 1> /tmp/cvc4.out 2> /tmp/cvc4.err && echo cvc4; } &
cvc4_pid=$!
{ z3 -smt2 MODEL=true $filename 1> /tmp/z3.out 2> /tmp/z3.err && echo z3; } &
z3_pid=$!
{ yices-smt2 $filename 1> /tmp/yices.out 2> /tmp/yices.err && echo yices; } &
yices_pid=$!

wait -n

for i in $cvc4_pid $z3_pid $yices_pid
do
    pkill -P $i
    #    kill -9 $i
done

pkill -P $$

