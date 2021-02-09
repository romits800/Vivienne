#!/bin/bash

SCRIPT_PATH="`dirname \"$0\"`"
pushd $SCRIPT_PATH
WASM="../../interpreter/wasm"

check () {
    $2 &> /dev/null
    if [ $? -eq 0 ]; then 
        echo "passed: $1" 
    else
        echo "failed: $1"
    fi
}

check 1 "$WASM -i script_if.wast"
check 2 "$WASM -i script_mem_store.wast"
check 3 "$WASM -i script_mem_operations_nonfailure.wast"
check 4 "$WASM -i script_mem_operations_failure.wast"
check 5 "$WASM -i script_mem_loop.wast"
check 6 "$WASM -i script_mem_loop_pass.wast"
check 7 "$WASM -i script_mem_loop_if.wast" # loop invar gives an extra error
check 8 "$WASM -i script_mem_loop_if_3.wast"
check 9 "$WASM -i script_mem_stores.wast"
check 10 "$WASM -i script_call.wast"
check 11 "$WASM -i script_mem_operations_char_nonfailure.wast"
check 12 "$WASM -i script_mem_operations_char_failure.wast"

# ctwasm examples
check 13 "$WASM -i script_salsa20_pass.wast"
check 14 "$WASM -i script_salsa20_fail.wast"
check 15 "$WASM -i script_tea_pass.wast"
check 16 "$WASM -i script_tea_fail.wast"
check 17 "$WASM -i script_sha256.wast"

check 18 "$WASM -i script_ext.wast"
check 19 "$WASM -i script_wrap.wast"

# tweetnacl
check 20 "$WASM -i script_tweetnacl_core_hsalsa20.wast"
check 21 "$WASM -i script_tweetnacl_core_salsa20.wast"
check 22 "$WASM -i script_tweetnacl_poly1305.wast"

check 23 "$WASM -i script_else.wast"
popd
