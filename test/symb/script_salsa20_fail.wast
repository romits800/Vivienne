;; This is a comment

(module $js 
   (memory $memory (export "memory") 2)
   (secret (i32.const 0) (i32.const 187))
   (public (i32.const 188) (i32.const 255))
   )
(register "js" $js)

(module
  (type (;0;) (func))
  (type (;1;) (func (param i32 i32 i32 i32 i32 i32 i32 i32)))
  (type (;2;) (func (param i32 i32)))
  (type (;3;) (func (param i32)))
  (import "js" "memory" (memory (;0;) 2))
  (func (;0;) (type 0)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    i32.const 0
    i32.load
    local.tee 17
    local.set 1
    i32.const 4
    i32.load
    local.tee 18
    local.set 2
    i32.const 8
    i32.load
    local.tee 19
    local.set 3
    i32.const 12
    i32.load
    local.tee 20
    local.set 4
    i32.const 16
    i32.load
    local.tee 21
    local.set 5
    i32.const 20
    i32.load
    local.tee 22
    local.set 6
    i32.const 24
    i32.load
    local.tee 23
    local.set 7
    i32.const 28
    i32.load
    local.tee 24
    local.set 8
    i32.const 32
    i32.load
    local.tee 25
    local.set 9
    i32.const 36
    i32.load
    local.tee 26
    local.set 10
    i32.const 40
    i32.load
    local.tee 27
    local.set 11
    i32.const 44
    i32.load
    local.tee 28
    local.set 12
    i32.const 48
    i32.load
    local.tee 29
    local.set 13
    i32.const 52
    i32.load
    local.tee 30
    local.set 14
    i32.const 56
    i32.load
    local.tee 31
    local.set 15
    i32.const 60
    i32.load
    local.tee 32
    local.set 16
    i32.const 0
    local.set 0
    block  ;; label = @1
      loop  ;; label = @2
        ;;nop 
        local.get 0
        i32.const 20
        i32.ge_u
        br_if 1 (;@1;)
        local.get 5
        local.get 1
        local.get 13
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 5
        local.get 9
        local.get 5
        local.get 1
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 9
        local.get 13
        local.get 9
        local.get 5
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 13
        local.get 1
        local.get 13
        local.get 9
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 1
        local.get 10
        local.get 6
        local.get 2
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 10
        local.get 14
        local.get 10
        local.get 6
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 14
        local.get 2
        local.get 14
        local.get 10
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 2
        local.get 6
        local.get 2
        local.get 14
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 6
        local.get 15
        local.get 11
        local.get 7
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 15
        local.get 3
        local.get 15
        local.get 11
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 3
        local.get 7
        local.get 3
        local.get 15
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 7
        local.get 11
        local.get 7
        local.get 3
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 11
        local.get 4
        local.get 16
        local.get 12
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 4
        local.get 8
        local.get 4
        local.get 16
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 8
        local.get 12
        local.get 8
        local.get 4
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 12
        local.get 16
        local.get 12
        local.get 8
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 16
        local.get 2
        local.get 1
        local.get 4
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 2
        local.get 3
        local.get 2
        local.get 1
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 3
        local.get 4
        local.get 3
        local.get 2
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 4
        local.get 1
        local.get 4
        local.get 3
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 1
        local.get 7
        local.get 6
        local.get 5
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 7
        local.get 8
        local.get 7
        local.get 6
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 8
        local.get 5
        local.get 8
        local.get 7
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 5
        local.get 6
        local.get 5
        local.get 8
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 6
        local.get 12
        local.get 11
        local.get 10
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 12
        local.get 9
        local.get 12
        local.get 11
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 9
        local.get 10
        local.get 9
        local.get 12
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 10
        local.get 11
        local.get 10
        local.get 9
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 11
        local.get 13
        local.get 16
        local.get 15
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 13
        local.get 14
        local.get 13
        local.get 16
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 14
        local.get 15
        local.get 14
        local.get 13
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 15
        local.get 16
        local.get 15
        local.get 14
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 16
        local.get 0
        i32.const 2
        i32.add
        local.set 0
        br 0 (;@2;)
      end
    end
    i32.const 64
    local.get 1
    local.get 17
    i32.add
    i32.store
    i32.const 68
    local.get 2
    local.get 18
    i32.add
    i32.store
    i32.const 72
    local.get 3
    local.get 19
    i32.add
    i32.store
    i32.const 76
    local.get 4
    local.get 20
    i32.add
    i32.store
    i32.const 80
    local.get 5
    local.get 21
    i32.add
    i32.store
    i32.const 84
    local.get 6
    local.get 22
    i32.add
    i32.store
    i32.const 88
    local.get 7
    local.get 23
    i32.add
    i32.store
    i32.const 92
    local.get 8
    local.get 24
    i32.add
    i32.store
    i32.const 96
    local.get 9
    local.get 25
    i32.add
    i32.store
    i32.const 100
    local.get 10
    local.get 26
    i32.add
    i32.store
    i32.const 104
    local.get 11
    local.get 27
    i32.add
    i32.store
    i32.const 108
    local.get 12
    local.get 28
    i32.add
    i32.store
    i32.const 112
    local.get 13
    local.get 29
    i32.add
    i32.store
    i32.const 116
    local.get 14
    local.get 30
    i32.add
    i32.store
    i32.const 120
    local.get 15
    local.get 31
    i32.add
    i32.store
    i32.const 124
    local.get 16
    local.get 32
    i32.add
    i32.store)
  (func (;1;) (type 1) (param i32 i32 i32 i32 i32 i32 i32 i32)
    i32.const 0
    i32.const 1634760805
    i32.store
    i32.const 4
    local.get 0
    i32.store
    i32.const 8
    local.get 1
    i32.store
    i32.const 12
    local.get 2
    i32.store
    i32.const 16
    local.get 3
    i32.store
    i32.const 20
    i32.const 857760878
    i32.store
    i32.const 40
    i32.const 2036477234
    i32.store
    i32.const 44
    local.get 4
    i32.store
    i32.const 48
    local.get 5
    i32.store
    i32.const 52
    local.get 6
    i32.store
    i32.const 56
    local.get 7
    i32.store
    i32.const 60
    i32.const 1797285236
    i32.store)
  (func (;2;) (type 2) (param i32 i32)
    i32.const 24
    local.get 0
    i32.store
    i32.const 28
    local.get 1
    i32.store
    i32.const 32
    i64.const 0
    i64.store)
  (func (;3;) (type 3) (param i32)
    (local i32 i32 i32 i32 i32 i32)
    local.get 0
    i32.const 0
    i32.ne
    if  ;; label = @1
      i32.const 128
      local.set 5
      i32.const 128
      local.get 0
      i32.add
      local.set 6
      block  ;; label = @2
        loop  ;; label = @3
          local.get 0
          i32.const 64
          i32.le_u
          br_if 1 (;@2;)
          call 0
          i32.const 32
          i64.const 1
          i32.const 32
          i64.load
          i64.add
          i64.store
          i32.const 0
          local.set 1
          block  ;; label = @4
            loop  ;; label = @5
              local.get 1
              local.get 0
              i32.ge_u
              br_if 1 (;@4;)
              local.get 5
              local.get 1
              i32.add
              i32.const 64
              local.get 1
              i32.add
              i32.load
              local.get 6
              local.get 1
              i32.add
              i32.load
              i32.xor
              i32.store
              local.get 1
              i32.const 4
              i32.add
              local.set 1
              br 0 (;@5;)
            end
          end
          local.get 0
          i32.const 64
          i32.sub
          local.set 0
          local.get 5
          i32.const 64
          i32.add
          local.set 5
          local.get 6
          i32.const 64
          i32.add
          local.set 6
          br 0 (;@3;)
        end
      end
      call 0
      i32.const 32
      i64.const 1
      i32.const 32
      i64.load
      i64.add
      i64.store
      i32.const 0
      local.set 1
      block  ;; label = @2
        loop  ;; label = @3
          local.get 1
          local.get 0
          i32.ge_u
          br_if 1 (;@2;)
          local.get 5
          local.get 1
          i32.add
          i32.const 64
          local.get 1
          i32.add
          i32.load8_u
          local.get 6
          local.get 1
          i32.add
          i32.load8_u
          local.tee 4
          i32.xor
          local.tee 3
          i32.store8
          local.get 1
          i32.const 1
          i32.add
          local.set 1
          br 0 (;@3;)
        end
      end
    end)
  (func (;4;) (type 2) (param i32 i32)
    (local i32)
    i32.const 0
    local.set 2
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        local.get 0
        i32.ge_u
        br_if 1 (;@1;)
        i32.const 32
        i64.const 0
        i64.store
        local.get 1
        call 3
        local.get 2
        i32.const 1
        i32.add
        local.set 2
        br 0 (;@2;)
      end
    end)
  (func (;5;) (type 3) (param i32)
    (local i32)
    i32.const 0
    local.set 1
    block  ;; label = @1
      loop  ;; label = @2
        local.get 1
        local.get 0
        i32.ge_u
        br_if 1 (;@1;)
        call 0
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        br 0 (;@2;)
      end
    end)
  (func (;6;) (type 3) (param i32)
    local.get 0
    call 3)
  (func (;7;) (type 3) (param i32)
    local.get 0
    call 3)
  (export "keysetup" (func 1))
  (export "noncesetup" (func 2))
  (export "encrypt" (func 3))
  (export "encrypt_many" (func 4))
  (export "sm" (func 5))
  (export "decrypt" (func 6))
  (export "keystream" (func 7)))
;; This is a comment

(assert_failure (symb_exec "encrypt" (i32.sconst 64)) "Trying to write high values in low memory") 
