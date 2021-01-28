(module $js 
   (memory $memory (export "memory") 2)
   (public (i32.const 0) (i32.const 7))
   (secret (i32.const 8) (i32.const 23))
   )
(register "js" $js)


(module
  (type (;0;) (func))
  (import "js" "memory" (memory (;0;) 1))
  (func (;0;) (type 0)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
    i32.const -1640531527
    local.set 6
    i32.const 0
    local.set 7
    i32.const 0
    i32.load
    local.set 0
    i32.const 4
    i32.load
    local.set 1
    i32.const 8
    i32.load
    local.set 2
    i32.const 12
    i32.load
    local.set 3
    i32.const 16
    i32.load
    local.set 4
    i32.const 20
    i32.load
    local.set 5
    i32.const 0
    local.set 8
    loop  ;; label = @1
      local.get 7
      local.get 6
      i32.add
      local.set 7
      local.get 0
      local.get 1
      i32.const 4
      i32.shl
      local.get 2
      i32.add
      local.get 1
      local.get 7
      i32.add
      i32.xor
      local.get 1
      i32.const 5
      i32.shr_u
      local.get 3
      i32.add
      i32.xor
      i32.add
      local.set 0
      local.get 1
      local.get 0
      i32.const 4
      i32.shl
      local.get 4
      i32.add
      local.get 0
      local.get 7
      i32.add
      i32.xor
      local.get 0
      i32.const 5
      i32.shr_u
      local.get 5
      i32.add
      i32.xor
      i32.add
      local.set 1
      local.get 8
      i32.const 1
      i32.add
      local.set 8
      local.get 8
      i32.const 32
      i32.lt_u
      br_if 0 (;@1;)
    end
    i32.const 0
    local.get 0
    i32.store
    i32.const 4
    local.get 1
    i32.store)
  (func (;1;) (type 0)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32)
    i32.const -1640531527
    local.set 6
    i32.const -957401312
    local.set 7
    i32.const 0
    i32.load
    local.set 0
    i32.const 4
    i32.load
    local.set 1
    i32.const 8
    i32.load
    local.set 2
    i32.const 12
    i32.load
    local.set 3
    i32.const 16
    i32.load
    local.set 4
    i32.const 20
    i32.load
    local.set 5
    i32.const 0
    local.set 8
    loop  ;; label = @1
      local.get 1
      local.get 0
      i32.const 4
      i32.shl
      local.get 4
      i32.add
      local.get 0
      local.get 7
      i32.add
      i32.xor
      local.get 0
      i32.const 5
      i32.shr_u
      local.get 5
      i32.add
      i32.xor
      i32.sub
      local.set 1
      local.get 0
      local.get 1
      i32.const 4
      i32.shl
      local.get 2
      i32.add
      local.get 1
      local.get 7
      i32.add
      i32.xor
      local.get 1
      i32.const 5
      i32.shr_u
      local.get 3
      i32.add
      i32.xor
      i32.sub
      local.set 0
      local.get 7
      local.get 6
      i32.sub
      local.set 7
      local.get 8
      i32.const 1
      i32.add
      local.set 8
      local.get 8
      i32.const 32
      i32.lt_u
      br_if 0 (;@1;)
    end
    i32.const 0
    local.get 0
    i32.store
    i32.const 4
    local.get 1
    i32.store)
  (export "encrypt" (func 0))
  (export "decrypt" (func 1)))

(symb_exec "encrypt")
(symb_exec "decrypt")

;;(assert_failure (symb_exec "encrypt") "Trying to write high values in low memory")
;;(assert_failure (symb_exec "decrypt") "Trying to write high values in low memory")
