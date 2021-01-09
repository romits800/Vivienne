#!/bin/bash

filename=$1

sed "s/(get-model)//" $filename > ${filename}.bool

{ cvc4-1.8-x86_64-linux-opt -m $filename 1> /tmp/cvc4.out 2> /tmp/cvc4.err ; echo cvc4; } &
cvc4_pid=$!
{ z3 -smt2 MODEL=true $filename 1> /tmp/z3.out 2> /tmp/z3.err ; echo z3; } &
z3_pid=$!
{ yices-smt2 $filename 1> /tmp/yices.out 2> /tmp/yices.err ; echo yices; } &
yices_pid=$!
{ boolector -m ${filename}.bool 1> /tmp/boolector.out 2> /tmp/boolector.err ; echo boolector; } &
boolector_pid=$!


# wait for the solver and the printing
#wait -n
#wait -n
#sleep 1
wait $yices_pid || wait $z3_pic || wait $cvc4_pid || wait $boolector_pid 

rm ${filename}.bool

for i in $cvc4_pid $z3_pid $yices_pid $boolector_pid
do
    pkill -9 -P $i &
    #    kill -9 $i
done

pkill -9 -P $$ &

