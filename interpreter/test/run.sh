clang --target=wasm32 -O1 -emit-llvm -c -S add.c
llc -O1 -filetype=obj add.ll
wasm2wat add.o -f -o add.wat

rm add.o

#awk '!/\(import|\(type \(;/'  add.wat > add2.wat
#mv add2.wat add.wat
#sed -i "s/func \$\([a-z0-9]*\) (type [0-9])/func $\1 (export \"\1\")/" add.wat 
