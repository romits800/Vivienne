(module $js 
   (memory $memory (export "memory") 1)
   (secret (i32.const 0) (i32.const 351)) ;; state + m (w) + data
   (public (i32.const 352) (i32.const 607)) ;; k
   (secret (i32.const 608) (i32.const 703)) ;; hash + input
   )
(register "js" $js)

(module
  (type (;0;) (func))
  (type (;1;) (func (param i32)))
  (import "js" "memory" (memory (;0;) 1))
  (func (;0;) (type 0)
    (local i32)
    i32.const 0
    global.set 0
    i64.const 0
    global.set 1
    i32.const 0
    local.set 0
    block  ;; label = @1
      loop  ;; label = @2
        local.get 0
        i32.const 64
        i32.ge_u
        br_if 1 (;@1;)
        global.get 3
        local.get 0
        i32.const 4
        i32.mul
        i32.add
        i32.const 0
        i32.store
        local.get 0
        i32.const 1
        i32.add
        local.set 0
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 0
    block  ;; label = @1
      loop  ;; label = @2
        local.get 0
        i32.const 64
        i32.ge_u
        br_if 1 (;@1;)
        global.get 4
        local.get 0
        i32.add
        i32.const 0
        i32.store8
        local.get 0
        i32.const 1
        i32.add
        local.set 0
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 0
    block  ;; label = @1
      loop  ;; label = @2
        local.get 0
        i32.const 32
        i32.ge_u
        br_if 1 (;@1;)
        global.get 6
        local.get 0
        i32.add
        i32.const 0
        i32.store8
        local.get 0
        i32.const 1
        i32.add
        local.set 0
        br 0 (;@2;)
      end
    end
    global.get 2
    i32.const 0
    i32.add
    i32.const 1779033703
    i32.store
    global.get 2
    i32.const 4
    i32.add
    i32.const -1150833019
    i32.store
    global.get 2
    i32.const 8
    i32.add
    i32.const 1013904242
    i32.store
    global.get 2
    i32.const 12
    i32.add
    i32.const -1521486534
    i32.store
    global.get 2
    i32.const 16
    i32.add
    i32.const 1359893119
    i32.store
    global.get 2
    i32.const 20
    i32.add
    i32.const -1694144372
    i32.store
    global.get 2
    i32.const 24
    i32.add
    i32.const 528734635
    i32.store
    global.get 2
    i32.const 28
    i32.add
    i32.const 1541459225
    i32.store)
  (func (;1;) (type 0)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    i32.const 0
    local.set 8
    i32.const 0
    local.set 9
    block  ;; label = @1
      loop  ;; label = @2
        local.get 8
        i32.const 16
        i32.ge_u
        br_if 1 (;@1;)
        global.get 3
        local.get 8
        i32.const 4
        i32.mul
        i32.add
        global.get 4
        local.get 9
        i32.add
        i32.load8_u
        i32.const 24
        i32.shl
        global.get 4
        local.get 9
        i32.const 1
        i32.add
        i32.add
        i32.load8_u
        i32.const 16
        i32.shl
        global.get 4
        local.get 9
        i32.const 2
        i32.add
        i32.add
        i32.load8_u
        i32.const 8
        i32.shl
        global.get 4
        local.get 9
        i32.const 3
        i32.add
        i32.add
        i32.load8_u
        i32.or
        i32.or
        i32.or
        i32.store
        local.get 8
        i32.const 1
        i32.add
        local.set 8
        local.get 9
        i32.const 4
        i32.add
        local.set 9
        br 0 (;@2;)
      end
    end
    block  ;; label = @1
      loop  ;; label = @2
        local.get 8
        i32.const 64
        i32.ge_u
        br_if 1 (;@1;)
        global.get 3
        local.get 8
        i32.const 4
        i32.mul
        i32.add
        global.get 3
        local.get 8
        i32.const 7
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        global.get 3
        local.get 8
        i32.const 16
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        global.get 3
        local.get 8
        i32.const 2
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.const 17
        i32.rotr
        global.get 3
        local.get 8
        i32.const 2
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.const 19
        i32.rotr
        global.get 3
        local.get 8
        i32.const 2
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.const 10
        i32.shr_u
        i32.xor
        i32.xor
        global.get 3
        local.get 8
        i32.const 15
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.const 7
        i32.rotr
        global.get 3
        local.get 8
        i32.const 15
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.const 18
        i32.rotr
        global.get 3
        local.get 8
        i32.const 15
        i32.sub
        i32.const 4
        i32.mul
        i32.add
        i32.load
        i32.const 3
        i32.shr_u
        i32.xor
        i32.xor
        i32.add
        i32.add
        i32.add
        i32.store
        local.get 8
        i32.const 1
        i32.add
        local.set 8
        br 0 (;@2;)
      end
    end
    global.get 2
    i32.const 0
    i32.add
    i32.load
    local.set 0
    global.get 2
    i32.const 4
    i32.add
    i32.load
    local.set 1
    global.get 2
    i32.const 8
    i32.add
    i32.load
    local.set 2
    global.get 2
    i32.const 12
    i32.add
    i32.load
    local.set 3
    global.get 2
    i32.const 16
    i32.add
    i32.load
    local.set 4
    global.get 2
    i32.const 20
    i32.add
    i32.load
    local.set 5
    global.get 2
    i32.const 24
    i32.add
    i32.load
    local.set 6
    global.get 2
    i32.const 28
    i32.add
    i32.load
    local.set 7
    i32.const 0
    local.set 8
    block  ;; label = @1
      loop  ;; label = @2
        local.get 8
        i32.const 64
        i32.ge_u
        br_if 1 (;@1;)
        local.get 7
        global.get 5
        local.get 8
        i32.const 4
        i32.mul
        i32.add
        i32.load
        global.get 3
        local.get 8
        i32.const 4
        i32.mul
        i32.add
        i32.load
        local.get 4
        i32.const 6
        i32.rotr
        local.get 4
        i32.const 11
        i32.rotr
        local.get 4
        i32.const 25
        i32.rotr
        i32.xor
        i32.xor
        local.get 4
        local.get 5
        i32.and
        local.get 4
        i32.const -1
        i32.xor
        local.get 6
        i32.and
        i32.xor
        i32.add
        i32.add
        i32.add
        i32.add
        local.set 10
        local.get 0
        i32.const 2
        i32.rotr
        local.get 0
        i32.const 13
        i32.rotr
        local.get 0
        i32.const 22
        i32.rotr
        i32.xor
        i32.xor
        local.get 0
        local.get 1
        i32.and
        local.get 0
        local.get 2
        i32.and
        local.get 1
        local.get 2
        i32.and
        i32.xor
        i32.xor
        i32.add
        local.set 11
        local.get 6
        local.set 7
        local.get 5
        local.set 6
        local.get 4
        local.set 5
        local.get 3
        local.get 10
        i32.add
        local.set 4
        local.get 2
        local.set 3
        local.get 1
        local.set 2
        local.get 0
        local.set 1
        local.get 10
        local.get 11
        i32.add
        local.set 0
        local.get 8
        i32.const 1
        i32.add
        local.set 8
        br 0 (;@2;)
      end
    end
    global.get 2
    i32.const 0
    i32.add
    global.get 2
    i32.const 0
    i32.add
    i32.load
    local.get 0
    i32.add
    i32.store
    global.get 2
    i32.const 4
    i32.add
    global.get 2
    i32.const 4
    i32.add
    i32.load
    local.get 1
    i32.add
    i32.store
    global.get 2
    i32.const 8
    i32.add
    global.get 2
    i32.const 8
    i32.add
    i32.load
    local.get 2
    i32.add
    i32.store
    global.get 2
    i32.const 12
    i32.add
    global.get 2
    i32.const 12
    i32.add
    i32.load
    local.get 3
    i32.add
    i32.store
    global.get 2
    i32.const 16
    i32.add
    global.get 2
    i32.const 16
    i32.add
    i32.load
    local.get 4
    i32.add
    i32.store
    global.get 2
    i32.const 20
    i32.add
    global.get 2
    i32.const 20
    i32.add
    i32.load
    local.get 5
    i32.add
    i32.store
    global.get 2
    i32.const 24
    i32.add
    global.get 2
    i32.const 24
    i32.add
    i32.load
    local.get 6
    i32.add
    i32.store
    global.get 2
    i32.const 28
    i32.add
    global.get 2
    i32.const 28
    i32.add
    i32.load
    local.get 7
    i32.add
    i32.store)
  (func (;2;) (type 1) (param i32)
    (local i32)
    i32.const 0
    local.set 1
    block  ;; label = @1
      loop  ;; label = @2
        local.get 1
        local.get 0
        i32.ge_u
        br_if 1 (;@1;)
        global.get 4
        global.get 0
        i32.add
        global.get 7
        local.get 1
        i32.add
        i32.load8_u
        i32.store8
        global.get 0
        i32.const 1
        i32.add
        global.set 0
        global.get 0
        i32.const 64
        i32.eq
        if  ;; label = @3
          call 1
          global.get 1
          i64.const 512
          i64.add
          global.set 1
          i32.const 0
          global.set 0
        end
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        br 0 (;@2;)
      end
    end)
  (func (;3;) (type 0)
    (local i32)
    global.get 0
    local.set 0
    local.get 0
    i32.const 56
    i32.lt_u
    if  ;; label = @1
      global.get 4
      local.get 0
      i32.add
      i32.const 128
      i32.store8
      local.get 0
      i32.const 1
      i32.add
      local.set 0
      block  ;; label = @2
        loop  ;; label = @3
          local.get 0
          i32.const 56
          i32.ge_u
          br_if 1 (;@2;)
          global.get 4
          local.get 0
          i32.add
          i32.const 0
          i32.store8
          local.get 0
          i32.const 1
          i32.add
          local.set 0
          br 0 (;@3;)
        end
      end
    else
      global.get 4
      local.get 0
      i32.add
      i32.const 128
      i32.store8
      local.get 0
      i32.const 1
      i32.add
      local.set 0
      block  ;; label = @2
        loop  ;; label = @3
          local.get 0
          i32.const 64
          i32.ge_u
          br_if 1 (;@2;)
          global.get 4
          local.get 0
          i32.add
          i32.const 0
          i32.store8
          local.get 0
          i32.const 1
          i32.add
          local.set 0
          br 0 (;@3;)
        end
      end
      call 1
      i32.const 0
      local.set 0
      block  ;; label = @2
        loop  ;; label = @3
          local.get 0
          i32.const 56
          i32.ge_u
          br_if 1 (;@2;)
          global.get 4
          local.get 0
          i32.add
          i32.const 0
          i32.store8
          local.get 0
          i32.const 1
          i32.add
          local.set 0
          br 0 (;@3;)
        end
      end
    end
    global.get 1
    global.get 0
    i64.extend_i32_u
    i64.const 8
    i64.mul
    i64.add
    global.set 1
    global.get 4
    i32.const 63
    i32.add
    global.get 1
    i64.const 0
    i64.shr_u
    i64.store8
    global.get 4
    i32.const 62
    i32.add
    global.get 1
    i64.const 8
    i64.shr_u
    i64.store8
    global.get 4
    i32.const 61
    i32.add
    global.get 1
    i64.const 16
    i64.shr_u
    i64.store8
    global.get 4
    i32.const 60
    i32.add
    global.get 1
    i64.const 24
    i64.shr_u
    i64.store8
    global.get 4
    i32.const 59
    i32.add
    global.get 1
    i64.const 32
    i64.shr_u
    i64.store8
    global.get 4
    i32.const 58
    i32.add
    global.get 1
    i64.const 40
    i64.shr_u
    i64.store8
    global.get 4
    i32.const 57
    i32.add
    global.get 1
    i64.const 48
    i64.shr_u
    i64.store8
    global.get 4
    i32.const 56
    i32.add
    global.get 1
    i64.const 56
    i64.shr_u
    i64.store8
    call 1
    i32.const 0
    local.set 0
    block  ;; label = @1
      loop  ;; label = @2
        local.get 0
        i32.const 4
        i32.ge_u
        br_if 1 (;@1;)
        global.get 6
        local.get 0
        i32.add
        global.get 2
        i32.const 3
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        global.get 6
        local.get 0
        i32.const 4
        i32.add
        i32.add
        global.get 2
        i32.const 7
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        global.get 6
        local.get 0
        i32.const 8
        i32.add
        i32.add
        global.get 2
        i32.const 11
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        global.get 6
        local.get 0
        i32.const 12
        i32.add
        i32.add
        global.get 2
        i32.const 15
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        global.get 6
        local.get 0
        i32.const 16
        i32.add
        i32.add
        global.get 2
        i32.const 19
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        global.get 6
        local.get 0
        i32.const 20
        i32.add
        i32.add
        global.get 2
        i32.const 23
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        global.get 6
        local.get 0
        i32.const 24
        i32.add
        i32.add
        global.get 2
        i32.const 27
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        global.get 6
        local.get 0
        i32.const 28
        i32.add
        i32.add
        global.get 2
        i32.const 31
        i32.add
        local.get 0
        i32.sub
        i32.load8_u
        i32.store8
        local.get 0
        i32.const 1
        i32.add
        local.set 0
        br 0 (;@2;)
      end
    end)
  (global (;0;) (mut i32) (i32.const 0))
  (global (;1;) (mut i64) (i64.const 0))
  (global (;2;) i32 (i32.const 0))
  (global (;3;) i32 (i32.const 32))
  (global (;4;) i32 (i32.const 288))
  (global (;5;) i32 (i32.const 352))
  (global (;6;) i32 (i32.const 608))
  (global (;7;) i32 (i32.const 640))
  (export "init" (func 0))
  (export "transform" (func 1))
  (export "update" (func 2))
  (export "final" (func 3)))


(symb_exec "transform")
(symb_exec "update" (i32.sconst 64))
