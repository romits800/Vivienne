#!/bin/bash

filename=$1
rm -f /tmp/*bitwuzla.err /tmp/*bitwuzla.out /tmp/*boolector.err /tmp/*boolector.out /tmp/*cvc4.err /tmp/*cvc4.out /tmp/*z3.err /tmp/*z3.out /tmp/*yices.err /tmp/*yices.out

{ cvc4-1.8-x86_64-linux-opt $filename 1> $filename.cvc4.out 2> $filename.cvc4.err ; echo cvc4; } &
cvc4_pid=$!
{ z3 -smt2 $filename 1> $filename.z3.out 2> $filename.z3.err ; echo z3; } &
z3_pid=$!
#{ bitwuzla ${filename} 1> $filename.bitwuzla.out 2> $filename.bitwuzla.err ; echo bitwuzla; } &
#bitwuzla_pid=$!
{ boolector ${filename} 1> $filename.boolector.out 2> $filename.boolector.err ; echo boolector; } &
boolector_pid=$!
{ yices-smt2 $filename 1> $filename.yices.out 2> $filename.yices.err && echo yices; } &
yices_pid=$!


# wait for the solver and the printing
#wait -n
#wait -n
#sleep 1
#{ wait $yices_pid && test $? -eq 0; } || 

ret=1
until [ $ret -eq 0 ]; do
    wait -n
    ret=$?
done

#wait $z3_pic || wait $cvc4_pid || wait $boolector_pid

for i in $z3_pid $boolector_pid $yices_pid $cvc4_pid $bitwuzla_pid
do
    pkill -9 -P $i &
    #    kill -9 $i
done

pkill -9 -P $$ &

