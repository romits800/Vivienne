(module $js 
	(memory $memory (export "mem") 1)
	(secret (i32.const 2000) (i32.const 2035)) ;; pad + s
	(public (i32.const 2036) (i32.const 2039)) ;; leftover
	(secret (i32.const 2040) (i32.const 2059)) ;; h
	(public (i32.const 2060) (i32.const 2063)) ;; final
	(secret (i32.const 2064) (i32.const 2079)) ;; buffer
	(secret (i32.const 2080) (i32.const 2111)) ;; key
	(secret (i32.const 2112) (i32.const 2127)) ;; mac
	(secret (i32.const 2128) (i32.const 2143)) ;; mm
	;;(public (i32.const 2128) (i32.const 2143)) ;; mm
   )
(register "js" $js)


(module
  (type (;0;) (func (param i32 i32 i32 i32)))
  (type (;1;) (func (param i32 i32 i32 i32 i32 i32 i32) (result i32)))
  (type (;2;) (func (param i32 i32 i32 i32 i32)))
  (type (;3;) (func (param i32 i32 i32 i32 i32) (result i32)))
  (type (;4;) (func (param i32 i32 i32)))
  (type (;5;) (func (param i32 i32 i32 i32 i32 i32) (result i32)))
  (type (;6;) (func (param i32 i32 i32 i32 i32 i32)))
  (type (;7;) (func (param i32 i32 i32) (result i32)))
  (type (;8;) (func (param i32 i32) (result i32)))
  (type (;9;) (func (param i32 i32)))
  (type (;10;) (func (param i32)))
  (import "js" "mem" (memory (;0;) 1))
  (func (;0;) (type 0) (param i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    local.get 3
    i32.load
    local.tee 4
    local.set 20
    local.get 2
    i32.load
    local.tee 5
    local.set 21
    local.get 2
    i32.load offset=4
    local.tee 6
    local.set 22
    local.get 2
    i32.load offset=8
    local.tee 7
    local.set 23
    local.get 2
    i32.load offset=12
    local.tee 8
    local.set 24
    local.get 3
    i32.load offset=4
    local.tee 9
    local.set 25
    local.get 1
    i32.load
    local.tee 10
    local.set 26
    local.get 1
    i32.load offset=4
    local.tee 11
    local.set 27
    local.get 1
    i32.load offset=8
    local.tee 12
    local.set 28
    local.get 1
    i32.load offset=12
    local.tee 13
    local.set 29
    local.get 3
    i32.load offset=8
    local.tee 14
    local.set 30
    local.get 2
    i32.load offset=16
    local.tee 15
    local.set 31
    local.get 2
    i32.load offset=20
    local.tee 16
    local.set 32
    local.get 2
    i32.load offset=24
    local.tee 17
    local.set 33
    local.get 2
    i32.load offset=28
    local.tee 18
    local.set 34
    local.get 3
    i32.load offset=12
    local.tee 19
    local.set 35
    block  ;; label = @1
      loop  ;; label = @2
        local.get 36
        i32.const 20
        i32.eq
        br_if 1 (;@1;)
        local.get 24
        local.get 20
        local.get 32
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 24
        local.get 28
        local.get 24
        local.get 20
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 28
        local.get 32
        local.get 28
        local.get 24
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 32
        local.get 20
        local.get 32
        local.get 28
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 20
        local.get 29
        local.get 25
        local.get 21
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 29
        local.get 33
        local.get 29
        local.get 25
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 33
        local.get 21
        local.get 33
        local.get 29
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 21
        local.get 25
        local.get 21
        local.get 33
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 25
        local.get 34
        local.get 30
        local.get 26
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 34
        local.get 22
        local.get 34
        local.get 30
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 22
        local.get 26
        local.get 22
        local.get 34
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 26
        local.get 30
        local.get 26
        local.get 22
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 30
        local.get 23
        local.get 35
        local.get 31
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 23
        local.get 27
        local.get 23
        local.get 35
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 27
        local.get 31
        local.get 27
        local.get 23
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 31
        local.get 35
        local.get 31
        local.get 27
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 35
        local.get 21
        local.get 20
        local.get 23
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 21
        local.get 22
        local.get 21
        local.get 20
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 22
        local.get 23
        local.get 22
        local.get 21
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 23
        local.get 20
        local.get 23
        local.get 22
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 20
        local.get 26
        local.get 25
        local.get 24
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 26
        local.get 27
        local.get 26
        local.get 25
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 27
        local.get 24
        local.get 27
        local.get 26
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 24
        local.get 25
        local.get 24
        local.get 27
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 25
        local.get 31
        local.get 30
        local.get 29
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 31
        local.get 28
        local.get 31
        local.get 30
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 28
        local.get 29
        local.get 28
        local.get 31
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 29
        local.get 30
        local.get 29
        local.get 28
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 30
        local.get 32
        local.get 35
        local.get 34
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 32
        local.get 33
        local.get 32
        local.get 35
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 33
        local.get 34
        local.get 33
        local.get 32
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 34
        local.get 35
        local.get 34
        local.get 33
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 35
        local.get 36
        i32.const 2
        i32.add
        local.set 36
        br 0 (;@2;)
      end
    end
    local.get 0
    local.get 20
    i32.store
    local.get 0
    local.get 25
    i32.store offset=4
    local.get 0
    local.get 30
    i32.store offset=8
    local.get 0
    local.get 35
    i32.store offset=12
    local.get 0
    local.get 26
    i32.store offset=16
    local.get 0
    local.get 27
    i32.store offset=20
    local.get 0
    local.get 28
    i32.store offset=24
    local.get 0
    local.get 29
    i32.store offset=28)
  (func (;1;) (type 0) (param i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    local.get 3
    i32.load
    local.tee 4
    local.set 20
    local.get 2
    i32.load
    local.tee 5
    local.set 21
    local.get 2
    i32.load offset=4
    local.tee 6
    local.set 22
    local.get 2
    i32.load offset=8
    local.tee 7
    local.set 23
    local.get 2
    i32.load offset=12
    local.tee 8
    local.set 24
    local.get 3
    i32.load offset=4
    local.tee 9
    local.set 25
    local.get 1
    i32.load
    local.tee 10
    local.set 26
    local.get 1
    i32.load offset=4
    local.tee 11
    local.set 27
    local.get 1
    i32.load offset=8
    local.tee 12
    local.set 28
    local.get 1
    i32.load offset=12
    local.tee 13
    local.set 29
    local.get 3
    i32.load offset=8
    local.tee 14
    local.set 30
    local.get 2
    i32.load offset=16
    local.tee 15
    local.set 31
    local.get 2
    i32.load offset=20
    local.tee 16
    local.set 32
    local.get 2
    i32.load offset=24
    local.tee 17
    local.set 33
    local.get 2
    i32.load offset=28
    local.tee 18
    local.set 34
    local.get 3
    i32.load offset=12
    local.tee 19
    local.set 35
    block  ;; label = @1
      loop  ;; label = @2
        local.get 36
        i32.const 20
        i32.eq
        br_if 1 (;@1;)
        local.get 24
        local.get 20
        local.get 32
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 24
        local.get 28
        local.get 24
        local.get 20
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 28
        local.get 32
        local.get 28
        local.get 24
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 32
        local.get 20
        local.get 32
        local.get 28
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 20
        local.get 29
        local.get 25
        local.get 21
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 29
        local.get 33
        local.get 29
        local.get 25
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 33
        local.get 21
        local.get 33
        local.get 29
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 21
        local.get 25
        local.get 21
        local.get 33
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 25
        local.get 34
        local.get 30
        local.get 26
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 34
        local.get 22
        local.get 34
        local.get 30
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 22
        local.get 26
        local.get 22
        local.get 34
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 26
        local.get 30
        local.get 26
        local.get 22
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 30
        local.get 23
        local.get 35
        local.get 31
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 23
        local.get 27
        local.get 23
        local.get 35
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 27
        local.get 31
        local.get 27
        local.get 23
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 31
        local.get 35
        local.get 31
        local.get 27
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 35
        local.get 21
        local.get 20
        local.get 23
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 21
        local.get 22
        local.get 21
        local.get 20
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 22
        local.get 23
        local.get 22
        local.get 21
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 23
        local.get 20
        local.get 23
        local.get 22
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 20
        local.get 26
        local.get 25
        local.get 24
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 26
        local.get 27
        local.get 26
        local.get 25
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 27
        local.get 24
        local.get 27
        local.get 26
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 24
        local.get 25
        local.get 24
        local.get 27
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 25
        local.get 31
        local.get 30
        local.get 29
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 31
        local.get 28
        local.get 31
        local.get 30
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 28
        local.get 29
        local.get 28
        local.get 31
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 29
        local.get 30
        local.get 29
        local.get 28
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 30
        local.get 32
        local.get 35
        local.get 34
        i32.add
        i32.const 7
        i32.rotl
        i32.xor
        local.set 32
        local.get 33
        local.get 32
        local.get 35
        i32.add
        i32.const 9
        i32.rotl
        i32.xor
        local.set 33
        local.get 34
        local.get 33
        local.get 32
        i32.add
        i32.const 13
        i32.rotl
        i32.xor
        local.set 34
        local.get 35
        local.get 34
        local.get 33
        i32.add
        i32.const 18
        i32.rotl
        i32.xor
        local.set 35
        local.get 36
        i32.const 2
        i32.add
        local.set 36
        br 0 (;@2;)
      end
    end
    local.get 0
    local.get 20
    local.get 4
    i32.add
    i32.store
    local.get 0
    local.get 21
    local.get 5
    i32.add
    i32.store offset=4
    local.get 0
    local.get 22
    local.get 6
    i32.add
    i32.store offset=8
    local.get 0
    local.get 23
    local.get 7
    i32.add
    i32.store offset=12
    local.get 0
    local.get 24
    local.get 8
    i32.add
    i32.store offset=16
    local.get 0
    local.get 25
    local.get 9
    i32.add
    i32.store offset=20
    local.get 0
    local.get 26
    local.get 10
    i32.add
    i32.store offset=24
    local.get 0
    local.get 27
    local.get 11
    i32.add
    i32.store offset=28
    local.get 0
    local.get 28
    local.get 12
    i32.add
    i32.store offset=32
    local.get 0
    local.get 29
    local.get 13
    i32.add
    i32.store offset=36
    local.get 0
    local.get 30
    local.get 14
    i32.add
    i32.store offset=40
    local.get 0
    local.get 31
    local.get 15
    i32.add
    i32.store offset=44
    local.get 0
    local.get 32
    local.get 16
    i32.add
    i32.store offset=48
    local.get 0
    local.get 33
    local.get 17
    i32.add
    i32.store offset=52
    local.get 0
    local.get 34
    local.get 18
    i32.add
    i32.store offset=56
    local.get 0
    local.get 35
    local.get 19
    i32.add
    i32.store offset=60)
  (func (;2;) (type 1) (param i32 i32 i32 i32 i32 i32 i32) (result i32)
    (local i32)
    i32.const 960
    local.get 6
    i32.add
    local.set 7
    local.get 7
    local.get 4
    local.get 5
    local.get 6
    call 3
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    local.get 7
    local.get 6
    call 11)
  (func (;3;) (type 0) (param i32 i32 i32 i32)
    (local i32)
    i32.const 928
    local.get 3
    i32.add
    local.set 4
    local.get 4
    local.get 2
    local.get 1
    local.get 3
    call 10
    local.get 0
    global.get 1
    local.get 4
    global.get 12
    call 0)
  (func (;4;) (type 1) (param i32 i32 i32 i32 i32 i32 i32) (result i32)
    (local i32)
    i32.const 960
    local.get 6
    i32.add
    local.set 7
    local.get 7
    local.get 4
    local.get 5
    local.get 6
    call 3
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    local.get 7
    local.get 6
    call 12)
  (func (;5;) (type 0) (param i32 i32 i32 i32)
    (local i32 i32 i32 i64)
    i32.const 128
    local.get 3
    i32.add
    local.set 4
    local.get 0
    i64.const 7640891576956012808
    i64.store
    local.get 0
    i64.const -4942790177534073029
    i64.store offset=8
    local.get 0
    i64.const 4354685564936845355
    i64.store offset=16
    local.get 0
    i64.const -6534734903238641935
    i64.store offset=24
    local.get 0
    i64.const 5840696475078001361
    i64.store offset=32
    local.get 0
    i64.const -7276294671716946913
    i64.store offset=40
    local.get 0
    i64.const 2270897969802886507
    i64.store offset=48
    local.get 0
    i64.const 6620516959819538809
    i64.store offset=56
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    call 6
    local.get 2
    local.get 1
    local.get 2
    i32.add
    local.set 1
    local.get 2
    i32.const 127
    i32.and
    local.set 2
    local.get 1
    local.get 2
    i32.sub
    local.set 1
    local.get 4
    local.set 6
    block  ;; label = @1
      loop  ;; label = @2
        local.get 5
        local.get 2
        i32.eq
        br_if 1 (;@1;)
        local.get 6
        local.get 1
        i32.load8_u
        i32.store8
        i32.const 1
        local.get 5
        i32.add
        local.set 5
        i32.const 1
        local.get 6
        i32.add
        local.set 6
        i32.const 1
        local.get 1
        i32.add
        local.set 1
        br 0 (;@2;)
      end
    end
    local.get 6
    i32.const 128
    i32.store8
    local.get 5
    i32.const 1
    i32.add
    local.set 5
    block  ;; label = @1
      loop  ;; label = @2
        local.get 5
        i32.const 256
        i32.eq
        br_if 1 (;@1;)
        local.get 6
        i32.const 0
        i32.store8 offset=1
        i32.const 1
        local.get 5
        i32.add
        local.set 5
        i32.const 1
        local.get 6
        i32.add
        local.set 6
        br 0 (;@2;)
      end
    end
    local.set 6
    i32.const 128
    i32.const 256
    local.get 2
    i32.const 112
    i32.lt_u
    select
    local.set 2
    local.get 0
    local.get 4
    local.get 2
    local.get 3
    local.get 4
    local.get 2
    i32.add
    i32.const 9
    i32.sub
    local.set 4
    local.get 4
    i32.const 0
    i32.store8
    local.get 4
    i32.const 0
    i32.store8 offset=1
    local.get 4
    i32.const 0
    i32.store8 offset=2
    local.get 4
    i32.const 0
    i32.store8 offset=3
    local.get 4
    local.get 6
    i32.const 29
    i32.shr_u
    i32.store8 offset=4
    local.get 4
    local.get 6
    i32.const 21
    i32.shr_u
    i32.store8 offset=5
    local.get 4
    local.get 6
    i32.const 13
    i32.shr_u
    i32.store8 offset=6
    local.get 4
    local.get 6
    i32.const 5
    i32.shr_u
    i32.store8 offset=7
    local.get 4
    local.get 6
    i32.const 3
    i32.shl
    i32.store8 offset=8
    call 6
    local.get 0
    i64.load
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=1
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=2
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=3
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=4
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=5
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=6
    local.get 0
    local.get 7
    i64.store8 offset=7
    local.get 0
    i64.load offset=8
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8 offset=8
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=9
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=10
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=11
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=12
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=13
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=14
    local.get 0
    local.get 7
    i64.store8 offset=15
    local.get 0
    i64.load offset=16
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8 offset=16
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=17
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=18
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=19
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=20
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=21
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=22
    local.get 0
    local.get 7
    i64.store8 offset=23
    local.get 0
    i64.load offset=24
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8 offset=24
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=25
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=26
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=27
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=28
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=29
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=30
    local.get 0
    local.get 7
    i64.store8 offset=31
    local.get 0
    i64.load offset=32
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8 offset=32
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=33
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=34
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=35
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=36
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=37
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=38
    local.get 0
    local.get 7
    i64.store8 offset=39
    local.get 0
    i64.load offset=40
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8 offset=40
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=41
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=42
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=43
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=44
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=45
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=46
    local.get 0
    local.get 7
    i64.store8 offset=47
    local.get 0
    i64.load offset=48
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8 offset=48
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=49
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=50
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=51
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=52
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=53
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=54
    local.get 0
    local.get 7
    i64.store8 offset=55
    local.get 0
    i64.load offset=56
    local.set 7
    local.get 0
    local.get 7
    i64.const 56
    i64.shr_u
    i64.store8 offset=56
    local.get 0
    local.get 7
    i64.const 48
    i64.shr_u
    i64.store8 offset=57
    local.get 0
    local.get 7
    i64.const 40
    i64.shr_u
    i64.store8 offset=58
    local.get 0
    local.get 7
    i64.const 32
    i64.shr_u
    i64.store8 offset=59
    local.get 0
    local.get 7
    i64.const 24
    i64.shr_u
    i64.store8 offset=60
    local.get 0
    local.get 7
    i64.const 16
    i64.shr_u
    i64.store8 offset=61
    local.get 0
    local.get 7
    i64.const 8
    i64.shr_u
    i64.store8 offset=62
    local.get 0
    local.get 7
    i64.store8 offset=63)
  (func (;6;) (type 0) (param i32 i32 i32 i32)
    (local i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i32 i32 i32 i32 i32)
    local.get 3
    local.set 24
    local.get 0
    i64.load
    local.set 12
    local.get 0
    i64.load offset=8
    local.set 13
    local.get 0
    i64.load offset=16
    local.set 14
    local.get 0
    i64.load offset=24
    local.set 15
    local.get 0
    i64.load offset=32
    local.set 16
    local.get 0
    i64.load offset=40
    local.set 17
    local.get 0
    i64.load offset=48
    local.set 18
    local.get 0
    i64.load offset=56
    local.set 19
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        i32.const 128
        i32.lt_u
        br_if 1 (;@1;)
        i32.const 0
        local.set 25
        local.get 1
        local.set 26
        local.get 24
        local.set 27
        block  ;; label = @3
          loop  ;; label = @4
            local.get 25
            i32.const 16
            i32.eq
            br_if 1 (;@3;)
            local.get 27
            local.get 26
            i64.load8_u
            i64.const 56
            i64.shl
            local.get 26
            i64.load8_u offset=1
            i64.const 48
            i64.shl
            i64.or
            local.get 26
            i64.load8_u offset=2
            i64.const 40
            i64.shl
            local.get 26
            i64.load8_u offset=3
            i64.const 32
            i64.shl
            i64.or
            i64.or
            local.get 26
            i64.load8_u offset=4
            i64.const 24
            i64.shl
            local.get 26
            i64.load8_u offset=5
            i64.const 16
            i64.shl
            i64.or
            local.get 26
            i64.load8_u offset=6
            i64.const 8
            i64.shl
            local.get 26
            i64.load8_u offset=7
            i64.or
            i64.or
            i64.or
            i64.store
            i32.const 1
            local.get 25
            i32.add
            local.set 25
            i32.const 8
            local.get 26
            i32.add
            local.set 26
            i32.const 8
            local.get 27
            i32.add
            local.set 27
            br 0 (;@4;)
          end
        end
        i32.const 0
        local.set 25
        global.get 9
        local.set 28
        block  ;; label = @3
          loop  ;; label = @4
            local.get 25
            i32.const 80
            i32.eq
            br_if 1 (;@3;)
            local.get 12
            local.set 4
            local.get 13
            local.set 5
            local.get 14
            local.set 6
            local.get 15
            local.set 7
            local.get 16
            local.set 8
            local.get 17
            local.set 9
            local.get 18
            local.set 10
            local.get 19
            local.set 11
            local.get 19
            local.get 16
            i64.const 14
            i64.rotr
            local.get 16
            i64.const 18
            i64.rotr
            i64.xor
            local.get 16
            i64.const 41
            i64.rotr
            i64.xor
            i64.add
            local.get 16
            local.get 17
            i64.and
            local.get 16
            i64.const -1
            i64.xor
            local.get 18
            i64.and
            i64.xor
            local.get 28
            i64.load
            local.get 24
            local.get 25
            i32.const 15
            i32.and
            i32.const 3
            i32.shl
            i32.add
            i64.load
            i64.add
            i64.add
            i64.add
            local.set 20
            local.get 20
            local.get 12
            i64.const 28
            i64.rotr
            local.get 12
            i64.const 34
            i64.rotr
            i64.xor
            local.get 12
            i64.const 39
            i64.rotr
            i64.xor
            i64.add
            local.get 12
            local.get 13
            i64.and
            local.get 12
            local.get 14
            i64.and
            i64.xor
            local.get 13
            local.get 14
            i64.and
            i64.xor
            i64.add
            local.set 11
            local.get 7
            local.get 20
            i64.add
            local.set 7
            local.get 4
            local.set 13
            local.get 5
            local.set 14
            local.get 6
            local.set 15
            local.get 7
            local.set 16
            local.get 8
            local.set 17
            local.get 9
            local.set 18
            local.get 10
            local.set 19
            local.get 11
            local.set 12
            local.get 25
            i32.const 15
            i32.and
            i32.const 15
            i32.eq
            if  ;; label = @5
              local.get 24
              i64.load offset=72
              local.set 21
              local.get 24
              i64.load offset=8
              local.set 22
              local.get 24
              i64.load offset=112
              local.set 23
              local.get 24
              local.get 24
              i64.load
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store
              local.get 24
              i64.load offset=80
              local.set 21
              local.get 24
              i64.load offset=16
              local.set 22
              local.get 24
              i64.load offset=120
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=8
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=8
              local.get 24
              i64.load offset=88
              local.set 21
              local.get 24
              i64.load offset=24
              local.set 22
              local.get 24
              i64.load
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=16
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=16
              local.get 24
              i64.load offset=96
              local.set 21
              local.get 24
              i64.load offset=32
              local.set 22
              local.get 24
              i64.load offset=8
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=24
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=24
              local.get 24
              i64.load offset=104
              local.set 21
              local.get 24
              i64.load offset=40
              local.set 22
              local.get 24
              i64.load offset=16
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=32
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=32
              local.get 24
              i64.load offset=112
              local.set 21
              local.get 24
              i64.load offset=48
              local.set 22
              local.get 24
              i64.load offset=24
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=40
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=40
              local.get 24
              i64.load offset=120
              local.set 21
              local.get 24
              i64.load offset=56
              local.set 22
              local.get 24
              i64.load offset=32
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=48
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=48
              local.get 24
              i64.load
              local.set 21
              local.get 24
              i64.load offset=64
              local.set 22
              local.get 24
              i64.load offset=40
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=56
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=56
              local.get 24
              i64.load offset=8
              local.set 21
              local.get 24
              i64.load offset=72
              local.set 22
              local.get 24
              i64.load offset=48
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=64
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=64
              local.get 24
              i64.load offset=16
              local.set 21
              local.get 24
              i64.load offset=80
              local.set 22
              local.get 24
              i64.load offset=56
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=72
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=72
              local.get 24
              i64.load offset=24
              local.set 21
              local.get 24
              i64.load offset=88
              local.set 22
              local.get 24
              i64.load offset=64
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=80
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=80
              local.get 24
              i64.load offset=32
              local.set 21
              local.get 24
              i64.load offset=96
              local.set 22
              local.get 24
              i64.load offset=72
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=88
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=88
              local.get 24
              i64.load offset=40
              local.set 21
              local.get 24
              i64.load offset=104
              local.set 22
              local.get 24
              i64.load offset=80
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=96
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=96
              local.get 24
              i64.load offset=48
              local.set 21
              local.get 24
              i64.load offset=112
              local.set 22
              local.get 24
              i64.load offset=88
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=104
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=104
              local.get 24
              i64.load offset=56
              local.set 21
              local.get 24
              i64.load offset=120
              local.set 22
              local.get 24
              i64.load offset=96
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=112
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=112
              local.get 24
              i64.load offset=64
              local.set 21
              local.get 24
              i64.load
              local.set 22
              local.get 24
              i64.load offset=104
              local.set 23
              local.get 24
              local.get 24
              i64.load offset=120
              local.get 21
              i64.add
              local.get 22
              i64.const 1
              i64.rotr
              local.get 22
              i64.const 8
              i64.rotr
              i64.xor
              local.get 22
              i64.const 7
              i64.shr_u
              i64.xor
              local.get 23
              i64.const 19
              i64.rotr
              local.get 23
              i64.const 61
              i64.rotr
              i64.xor
              local.get 23
              i64.const 6
              i64.shr_u
              i64.xor
              i64.add
              i64.add
              i64.store offset=120
            end
            i32.const 1
            local.get 25
            i32.add
            local.set 25
            i32.const 8
            local.get 28
            i32.add
            local.set 28
            br 0 (;@4;)
          end
        end
        local.get 0
        local.get 12
        local.get 0
        i64.load
        i64.add
        local.tee 12
        i64.store
        local.get 0
        local.get 13
        local.get 0
        i64.load offset=8
        i64.add
        local.tee 13
        i64.store offset=8
        local.get 0
        local.get 14
        local.get 0
        i64.load offset=16
        i64.add
        local.tee 14
        i64.store offset=16
        local.get 0
        local.get 15
        local.get 0
        i64.load offset=24
        i64.add
        local.tee 15
        i64.store offset=24
        local.get 0
        local.get 16
        local.get 0
        i64.load offset=32
        i64.add
        local.tee 16
        i64.store offset=32
        local.get 0
        local.get 17
        local.get 0
        i64.load offset=40
        i64.add
        local.tee 17
        i64.store offset=40
        local.get 0
        local.get 18
        local.get 0
        i64.load offset=48
        i64.add
        local.tee 18
        i64.store offset=48
        local.get 0
        local.get 19
        local.get 0
        i64.load offset=56
        i64.add
        local.tee 19
        i64.store offset=56
        i32.const 128
        local.get 1
        i32.add
        local.set 1
        local.get 2
        i32.const 128
        i32.sub
        local.set 2
        br 0 (;@2;)
      end
    end)
  (func (;7;) (type 2) (param i32 i32 i32 i32 i32)

    local.get 4
    i32.load offset=36
    drop


    local.get 4
    local.get 3
    call 27

    local.get 4
    i32.load offset=36
    drop

    local.get 4
    local.get 1
    local.get 2
    call 28
    local.get 4
    local.get 0
    call 26)
  (func (;8;) (type 3) (param i32 i32 i32 i32 i32) (result i32)
    local.get 4
    i32.const 80
    i32.add
    local.get 1
    local.get 2
    local.get 3
    local.get 4
    call 7
    local.get 0
    local.get 4
    i32.const 80
    i32.add
    call 21)
  (func (;9;) (type 4) (param i32 i32 i32)
    local.get 0
    local.get 1
    global.get 11
    local.get 2
    call 10)
  (func (;10;) (type 0) (param i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    local.get 3
    local.tee 4
    i32.const 32
    i32.add
    local.tee 5
    i32.const 128
    i32.add
    local.tee 8
    i32.const 128
    i32.add
    local.tee 10
    i32.const 128
    i32.add
    local.tee 9
    i32.const 128
    i32.add
    local.tee 11
    i32.const 128
    i32.add
    local.tee 12
    i32.const 128
    i32.add
    local.set 13
    local.get 4
    local.get 1
    i64.load
    i64.store
    local.get 4
    local.get 1
    i64.load offset=8
    i64.store offset=8
    local.get 4
    local.get 1
    i64.load offset=16
    i64.store offset=16
    local.get 4
    local.get 1
    i64.load offset=24
    i64.store offset=24
    local.get 4
    local.get 1
    i32.load8_u offset=31
    i32.const 127
    i32.and
    i32.const 64
    i32.or
    i32.store8 offset=31
    local.get 4
    local.get 4
    i32.load8_u
    i32.const 248
    i32.and
    i32.store8
    local.get 5
    local.get 2
    call 49
    local.get 9
    local.get 5
    i64.load
    i64.store
    local.get 11
    i64.const 1
    i64.store
    local.get 8
    i64.const 1
    i64.store
    local.get 10
    i64.const 0
    i64.store
    local.get 9
    local.get 5
    i64.load offset=8
    i64.store offset=8
    local.get 11
    i64.const 0
    i64.store offset=8
    local.get 8
    i64.const 0
    i64.store offset=8
    local.get 10
    i64.const 0
    i64.store offset=8
    local.get 9
    local.get 5
    i64.load offset=16
    i64.store offset=16
    local.get 11
    i64.const 0
    i64.store offset=16
    local.get 8
    i64.const 0
    i64.store offset=16
    local.get 10
    i64.const 0
    i64.store offset=16
    local.get 9
    local.get 5
    i64.load offset=24
    i64.store offset=24
    local.get 11
    i64.const 0
    i64.store offset=24
    local.get 8
    i64.const 0
    i64.store offset=24
    local.get 10
    i64.const 0
    i64.store offset=24
    local.get 9
    local.get 5
    i64.load offset=32
    i64.store offset=32
    local.get 11
    i64.const 0
    i64.store offset=32
    local.get 8
    i64.const 0
    i64.store offset=32
    local.get 10
    i64.const 0
    i64.store offset=32
    local.get 9
    local.get 5
    i64.load offset=40
    i64.store offset=40
    local.get 11
    i64.const 0
    i64.store offset=40
    local.get 8
    i64.const 0
    i64.store offset=40
    local.get 10
    i64.const 0
    i64.store offset=40
    local.get 9
    local.get 5
    i64.load offset=48
    i64.store offset=48
    local.get 11
    i64.const 0
    i64.store offset=48
    local.get 8
    i64.const 0
    i64.store offset=48
    local.get 10
    i64.const 0
    i64.store offset=48
    local.get 9
    local.get 5
    i64.load offset=56
    i64.store offset=56
    local.get 11
    i64.const 0
    i64.store offset=56
    local.get 8
    i64.const 0
    i64.store offset=56
    local.get 10
    i64.const 0
    i64.store offset=56
    local.get 9
    local.get 5
    i64.load offset=64
    i64.store offset=64
    local.get 11
    i64.const 0
    i64.store offset=64
    local.get 8
    i64.const 0
    i64.store offset=64
    local.get 10
    i64.const 0
    i64.store offset=64
    local.get 9
    local.get 5
    i64.load offset=72
    i64.store offset=72
    local.get 11
    i64.const 0
    i64.store offset=72
    local.get 8
    i64.const 0
    i64.store offset=72
    local.get 10
    i64.const 0
    i64.store offset=72
    local.get 9
    local.get 5
    i64.load offset=80
    i64.store offset=80
    local.get 11
    i64.const 0
    i64.store offset=80
    local.get 8
    i64.const 0
    i64.store offset=80
    local.get 10
    i64.const 0
    i64.store offset=80
    local.get 9
    local.get 5
    i64.load offset=88
    i64.store offset=88
    local.get 11
    i64.const 0
    i64.store offset=88
    local.get 8
    i64.const 0
    i64.store offset=88
    local.get 10
    i64.const 0
    i64.store offset=88
    local.get 9
    local.get 5
    i64.load offset=96
    i64.store offset=96
    local.get 11
    i64.const 0
    i64.store offset=96
    local.get 8
    i64.const 0
    i64.store offset=96
    local.get 10
    i64.const 0
    i64.store offset=96
    local.get 9
    local.get 5
    i64.load offset=104
    i64.store offset=104
    local.get 11
    i64.const 0
    i64.store offset=104
    local.get 8
    i64.const 0
    i64.store offset=104
    local.get 10
    i64.const 0
    i64.store offset=104
    local.get 9
    local.get 5
    i64.load offset=112
    i64.store offset=112
    local.get 11
    i64.const 0
    i64.store offset=112
    local.get 8
    i64.const 0
    i64.store offset=112
    local.get 10
    i64.const 0
    i64.store offset=112
    local.get 9
    local.get 5
    i64.load offset=120
    i64.store offset=120
    local.get 11
    i64.const 0
    i64.store offset=120
    local.get 8
    i64.const 0
    i64.store offset=120
    local.get 10
    i64.const 0
    i64.store offset=120
    i32.const 254
    local.set 7
    block  ;; label = @1
      loop  ;; label = @2
        local.get 7
        i32.const 0
        i32.lt_s
        br_if 1 (;@1;)
        i32.const 1
        local.get 4
        local.get 7
        i32.const 3
        i32.shr_u
        i32.add
        i32.load8_u
        local.get 7
        i32.const 7
        i32.and
        i32.shr_u
        i32.and
        local.set 6
        local.get 8
        local.get 9
        local.get 6
        call 48
        local.get 10
        local.get 11
        local.get 6
        call 48
        local.get 12
        local.get 8
        local.get 10
        call 41
        local.get 8
        local.get 8
        local.get 10
        call 44
        local.get 10
        local.get 9
        local.get 11
        call 41
        local.get 9
        local.get 9
        local.get 11
        call 44
        local.get 11
        local.get 12
        call 43
        local.get 13
        local.get 8
        call 43
        local.get 8
        local.get 10
        local.get 8
        call 42
        local.get 10
        local.get 9
        local.get 12
        call 42
        local.get 12
        local.get 8
        local.get 10
        call 41
        local.get 8
        local.get 8
        local.get 10
        call 44
        local.get 9
        local.get 8
        call 43
        local.get 10
        local.get 11
        local.get 13
        call 44
        local.get 8
        local.get 10
        global.get 3
        call 42
        local.get 8
        local.get 8
        local.get 11
        call 41
        local.get 10
        local.get 10
        local.get 8
        call 42
        local.get 8
        local.get 11
        local.get 13
        call 42
        local.get 11
        local.get 9
        local.get 5
        call 42
        local.get 9
        local.get 12
        call 43
        local.get 8
        local.get 9
        local.get 6
        call 48
        local.get 10
        local.get 11
        local.get 6
        call 48
        local.get 7
        i32.const 1
        i32.sub
        local.set 7
        br 0 (;@2;)
      end
    end
    local.get 5
    i32.const 256
    i32.add
    local.set 14
    local.get 5
    i32.const 128
    i32.add
    local.set 15
    local.get 14
    local.get 14
    local.get 12
    call 46
    local.get 15
    local.get 15
    local.get 14
    call 42
    local.get 0
    local.get 15
    local.get 12
    call 47)
  (func (;11;) (type 5) (param i32 i32 i32 i32 i32 i32) (result i32)
    local.get 2
    i32.const 32
    i32.ge_u
    if  ;; label = @1
      local.get 0
      local.get 1
      local.get 2
      local.get 3
      local.get 4
      local.get 5
      call 19
      i32.const 16
      local.get 0
      i32.add
      i32.const 32
      local.get 0
      i32.add
      local.get 2
      i32.const 32
      i32.sub
      local.get 0
      local.get 5
      call 7
      local.get 0
      i64.const 0
      i64.store
      local.get 0
      i64.const 0
      i64.store offset=8
      i32.const 0
      return
    end
    i32.const -1)
  (func (;12;) (type 5) (param i32 i32 i32 i32 i32 i32) (result i32)
    (local i32)
    local.get 2
    i32.const 32
    i32.ge_u
    if  ;; label = @1
      i32.const 120
      local.get 5
      i32.add
      local.set 6
      local.get 6
      i32.const 32
      local.get 3
      local.get 4
      local.get 5
      call 16
      i32.const 16
      local.get 1
      i32.add
      i32.const 32
      local.get 1
      i32.add
      local.get 2
      i32.const 32
      i32.sub
      local.get 6
      local.get 5
      call 8
      i32.const 0
      i32.eq
      if  ;; label = @2
        local.get 0
        local.get 1
        local.get 2
        local.get 3
        local.get 4
        local.get 5
        call 19
        local.get 0
        i64.const 0
        i64.store
        local.get 0
        i64.const 0
        i64.store offset=8
        local.get 0
        i64.const 0
        i64.store offset=16
        local.get 0
        i64.const 0
        i64.store offset=24
        i32.const 0
        return
      end
    end
    i32.const -1)
  (func (;13;) (type 0) (param i32 i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32)
    local.get 3
    i32.const 896
    i32.add
    local.tee 4
    i32.const 64
    i32.add
    local.tee 5
    i32.const 64
    i32.add
    local.tee 6
    i32.const 64
    i32.add
    local.tee 7
    i32.const 512
    i32.add
    local.set 8
    local.get 4
    local.get 2
    i32.const 32
    local.get 3
    call 5
    local.get 4
    local.get 4
    i32.load8_u
    i32.const 248
    i32.and
    i32.store8
    local.get 4
    local.get 4
    i32.load8_u offset=31
    i32.const 127
    i32.and
    i32.store8 offset=31
    local.get 4
    local.get 4
    i32.load8_u offset=31
    i32.const 64
    i32.or
    i32.store8 offset=31
    local.get 0
    local.get 4
    i64.load offset=32
    i64.store offset=32
    local.get 0
    local.get 4
    i64.load offset=40
    i64.store offset=40
    local.get 0
    local.get 4
    i64.load offset=48
    i64.store offset=48
    local.get 0
    local.get 4
    i64.load offset=56
    i64.store offset=56
    local.get 6
    local.get 0
    i32.const 32
    i32.add
    local.get 1
    i32.const 32
    i32.add
    local.get 3
    call 5
    local.get 6
    local.get 3
    call 36
    local.get 8
    local.get 6
    local.get 3
    call 37
    local.get 0
    local.get 8
    local.get 3
    call 33
    local.get 0
    local.get 2
    i64.load offset=32
    i64.store offset=32
    local.get 0
    local.get 2
    i64.load offset=40
    i64.store offset=40
    local.get 0
    local.get 2
    i64.load offset=48
    i64.store offset=48
    local.get 0
    local.get 2
    i64.load offset=56
    i64.store offset=56
    local.get 5
    local.get 0
    local.get 1
    i32.const 64
    i32.add
    local.get 3
    call 5
    local.get 5
    local.get 3
    call 36
    block  ;; label = @1
      loop  ;; label = @2
        local.get 9
        i32.const 32
        i32.eq
        br_if 1 (;@1;)
        local.get 7
        local.get 9
        i32.const 3
        i32.shl
        i32.add
        local.get 6
        local.get 9
        i32.add
        i64.load8_u
        i64.store
        local.get 9
        i32.const 1
        i32.add
        local.set 9
        br 0 (;@2;)
      end
    end
    block  ;; label = @1
      loop  ;; label = @2
        local.get 9
        i32.const 64
        i32.eq
        br_if 1 (;@1;)
        local.get 7
        local.get 9
        i32.const 3
        i32.shl
        i32.add
        i64.const 0
        i64.store
        local.get 9
        i32.const 1
        i32.add
        local.set 9
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 9
    block  ;; label = @1
      loop  ;; label = @2
        local.get 9
        i32.const 32
        i32.eq
        br_if 1 (;@1;)
        local.get 7
        local.get 9
        i32.const 3
        i32.shl
        i32.add
        local.set 11
        i32.const 0
        local.set 10
        block  ;; label = @3
          loop  ;; label = @4
            local.get 10
            i32.const 32
            i32.eq
            br_if 1 (;@3;)
            local.get 11
            local.get 11
            i64.load
            local.get 5
            local.get 9
            i32.add
            i64.load8_u
            local.get 4
            local.get 10
            i32.add
            i64.load8_u
            i64.mul
            i64.add
            i64.store
            local.get 11
            i32.const 8
            i32.add
            local.set 11
            local.get 10
            i32.const 1
            i32.add
            local.set 10
            br 0 (;@4;)
          end
        end
        local.get 9
        i32.const 1
        i32.add
        local.set 9
        br 0 (;@2;)
      end
    end
    local.get 0
    i32.const 32
    i32.add
    local.get 7
    call 31)
  (func (;14;) (type 4) (param i32 i32 i32)
    (local i32 i32)
    local.get 2
    i32.const 896
    i32.add
    local.tee 3
    i32.const 64
    i32.add
    local.set 4
    local.get 3
    local.get 1
    i32.const 32
    local.get 2
    call 5
    local.get 3
    local.get 3
    i32.load8_u
    i32.const 248
    i32.and
    i32.store8
    local.get 3
    local.get 3
    i32.load8_u offset=31
    i32.const 127
    i32.and
    i32.store8 offset=31
    local.get 3
    local.get 3
    i32.load8_u offset=31
    i32.const 64
    i32.or
    i32.store8 offset=31
    local.get 4
    local.get 3
    local.get 2
    call 37
    local.get 0
    local.get 4
    local.get 2
    call 33
    local.get 1
    local.get 0
    i64.load
    i64.store offset=32
    local.get 1
    local.get 0
    i64.load offset=8
    i64.store offset=40
    local.get 1
    local.get 0
    i64.load offset=16
    i64.store offset=48
    local.get 1
    local.get 0
    i64.load offset=24
    i64.store offset=56)
  (func (;15;) (type 3) (param i32 i32 i32 i32 i32) (result i32)
    (local i32 i32 i32 i32)
    local.get 4
    i32.const 896
    i32.add
    local.tee 5
    i32.const 32
    i32.add
    local.tee 6
    i32.const 64
    i32.add
    local.tee 7
    i32.const 512
    i32.add
    local.set 8
    local.get 2
    i32.const 64
    i32.lt_u
    if  ;; label = @1
      i32.const -1
      return
    end
    local.get 8
    local.get 3
    local.get 4
    call 40
    if  ;; label = @1
      i32.const -1
      return
    end
    local.get 0
    local.get 3
    i64.load
    i64.store offset=32
    local.get 0
    local.get 3
    i64.load offset=8
    i64.store offset=40
    local.get 0
    local.get 3
    i64.load offset=16
    i64.store offset=48
    local.get 0
    local.get 3
    i64.load offset=24
    i64.store offset=56
    local.get 6
    local.get 0
    local.get 2
    local.get 4
    call 5
    local.get 6
    local.get 4
    call 36
    local.get 7
    local.get 8
    local.get 6
    local.get 4
    call 38
    local.get 8
    local.get 1
    i32.const 32
    i32.add
    local.get 4
    call 37
    local.get 7
    local.get 8
    local.get 4
    call 29
    local.get 5
    local.get 7
    local.get 4
    call 33
    local.get 2
    i32.const 64
    i32.sub
    local.set 2
    local.get 1
    local.get 5
    call 22
    if  ;; label = @1
      i32.const -1
      return
    end
    local.get 2)
  (func (;16;) (type 2) (param i32 i32 i32 i32 i32)
    (local i32 i32)
    i32.const 32
    local.get 4
    local.tee 5
    i32.add
    local.set 6
    local.get 5
    local.get 2
    local.get 3
    global.get 12
    call 0
    local.get 6
    local.get 2
    i64.load offset=16
    i64.store
    local.get 0
    local.get 1
    local.get 6
    local.get 5
    i32.const 40
    local.get 4
    i32.add
    call 17)
  (func (;17;) (type 2) (param i32 i32 i32 i32 i32)
    (local i32 i32 i32)
    local.get 4
    local.set 5
    local.get 4
    i32.const 16
    i32.add
    local.set 6
    local.get 5
    local.get 2
    i64.load
    i64.store
    local.get 5
    i64.const 0
    i64.store offset=8
    block  ;; label = @1
      loop  ;; label = @2
        local.get 1
        i32.const 64
        i32.lt_u
        br_if 1 (;@1;)
        local.get 6
        local.get 5
        local.get 3
        global.get 12
        call 1
        local.get 0
        local.get 6
        i64.load
        i64.store
        local.get 0
        local.get 6
        i64.load offset=8
        i64.store offset=8
        local.get 0
        local.get 6
        i64.load offset=16
        i64.store offset=16
        local.get 0
        local.get 6
        i64.load offset=24
        i64.store offset=24
        local.get 0
        local.get 6
        i64.load offset=32
        i64.store offset=32
        local.get 0
        local.get 6
        i64.load offset=40
        i64.store offset=40
        local.get 0
        local.get 6
        i64.load offset=48
        i64.store offset=48
        local.get 0
        local.get 6
        i64.load offset=56
        i64.store offset=56
        local.get 5
        local.get 5
        i64.load offset=8
        i64.const 1
        i64.add
        i64.store offset=8
        local.get 1
        i32.const 64
        i32.sub
        local.set 1
        local.get 0
        i32.const 64
        i32.add
        local.set 0
        br 0 (;@2;)
      end
    end
    local.get 1
    i32.const 0
    i32.gt_u
    if  ;; label = @1
      local.get 6
      local.get 5
      local.get 3
      global.get 12
      call 1
      block  ;; label = @2
        loop  ;; label = @3
          local.get 1
          i32.const 0
          i32.eq
          br_if 1 (;@2;)
          local.get 0
          local.get 6
          i32.load8_u
          i32.store8
          local.get 1
          i32.const 1
          i32.sub
          local.set 1
          local.get 0
          i32.const 1
          i32.add
          local.set 0
          local.get 6
          i32.const 1
          i32.add
          local.set 6
          br 0 (;@3;)
        end
      end
    end)
  (func (;18;) (type 6) (param i32 i32 i32 i32 i32 i32)
    (local i32 i32 i32)
    local.get 5
    local.set 6
    local.get 5
    i32.const 16
    i32.add
    local.set 7
    local.get 6
    local.get 3
    i64.load
    i64.store
    local.get 6
    i64.const 0
    i64.store offset=8
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        i32.const 64
        i32.lt_u
        br_if 1 (;@1;)
        local.get 7
        local.get 6
        local.get 4
        global.get 12
        call 1
        local.get 0
        local.get 1
        i64.load
        local.get 7
        i64.load
        i64.xor
        i64.store
        local.get 0
        local.get 1
        i64.load offset=8
        local.get 7
        i64.load offset=8
        i64.xor
        i64.store offset=8
        local.get 0
        local.get 1
        i64.load offset=16
        local.get 7
        i64.load offset=16
        i64.xor
        i64.store offset=16
        local.get 0
        local.get 1
        i64.load offset=24
        local.get 7
        i64.load offset=24
        i64.xor
        i64.store offset=24
        local.get 0
        local.get 1
        i64.load offset=32
        local.get 7
        i64.load offset=32
        i64.xor
        i64.store offset=32
        local.get 0
        local.get 1
        i64.load offset=40
        local.get 7
        i64.load offset=40
        i64.xor
        i64.store offset=40
        local.get 0
        local.get 1
        i64.load offset=48
        local.get 7
        i64.load offset=48
        i64.xor
        i64.store offset=48
        local.get 0
        local.get 1
        i64.load offset=56
        local.get 7
        i64.load offset=56
        i64.xor
        i64.store offset=56
        local.get 6
        local.get 6
        i64.load offset=8
        i64.const 1
        i64.add
        i64.store offset=8
        local.get 2
        i32.const 64
        i32.sub
        local.set 2
        local.get 0
        i32.const 64
        i32.add
        local.set 0
        local.get 1
        i32.const 64
        i32.add
        local.set 1
        br 0 (;@2;)
      end
    end
    local.get 2
    i32.const 0
    i32.gt_u
    if  ;; label = @1
      local.get 7
      local.get 6
      local.get 4
      global.get 12
      call 1
      block  ;; label = @2
        loop  ;; label = @3
          local.get 2
          i32.const 0
          i32.eq
          br_if 1 (;@2;)
          local.get 0
          local.get 1
          i32.load8_u
          local.get 7
          i32.load8_u
          i32.xor
          i32.store8
          local.get 2
          i32.const 1
          i32.sub
          local.set 2
          local.get 0
          i32.const 1
          i32.add
          local.set 0
          local.get 1
          i32.const 1
          i32.add
          local.set 1
          local.get 7
          i32.const 1
          i32.add
          local.set 7
          br 0 (;@3;)
        end
      end
    end)
  (func (;19;) (type 6) (param i32 i32 i32 i32 i32 i32)
    (local i32 i32)
    i32.const 32
    local.get 5
    local.tee 6
    i32.add
    local.set 7
    local.get 6
    local.get 3
    local.get 4
    global.get 12
    call 0
    local.get 7
    local.get 3
    i64.load offset=16
    i64.store
    local.get 0
    local.get 1
    local.get 2
    local.get 7
    local.get 6
    i32.const 40
    local.get 5
    i32.add
    call 18)
  (func (;20;) (type 7) (param i32 i32 i32) (result i32)
    (local i64)
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        i32.const 8
        i32.lt_u
        br_if 1 (;@1;)
        local.get 3
        local.get 0
        i64.load
        local.get 1
        i64.load
        i64.xor
        i64.or
        local.set 3
        local.get 2
        i32.const 8
        i32.sub
        local.set 2
        local.get 0
        i32.const 8
        i32.add
        local.set 0
        local.get 1
        i32.const 8
        i32.add
        local.set 1
        br 0 (;@2;)
      end
    end
    local.get 3
    i64.const 4294967295
    i64.and
    local.get 3
    i64.const 32
    i64.shr_u
    i64.or
    local.set 3
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        i32.eqz
        br_if 1 (;@1;)
        local.get 3
        local.get 0
        i64.load8_u
        local.get 1
        i64.load8_u
        i64.xor
        i64.or
        local.set 3
        local.get 2
        i32.const 1
        i32.sub
        local.set 2
        local.get 0
        i32.const 1
        i32.add
        local.set 0
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        br 0 (;@2;)
      end
    end
    i64.const 1
    local.get 3
    i64.const 1
    i64.sub
    i64.const 32
    i64.shr_u
    i64.and
    i64.const 1
    i64.sub
    i32.wrap_i64)
  (func (;21;) (type 8) (param i32 i32) (result i32)
    (local i64)
    local.get 0
    i64.load
    local.get 1
    i64.load
    i64.xor
    local.get 0
    i64.load offset=8
    local.get 1
    i64.load offset=8
    i64.xor
    i64.or
    local.set 2
    local.get 2
    i64.const 4294967295
    i64.and
    local.get 2
    i64.const 32
    i64.shr_u
    i64.or
    local.set 2
    i64.const 1
    local.get 2
    i64.const 1
    i64.sub
    i64.const 32
    i64.shr_u
    i64.and
    i64.const 1
    i64.sub
    i32.wrap_i64)
  (func (;22;) (type 8) (param i32 i32) (result i32)
    (local i64)
    local.get 0
    i64.load
    local.get 1
    i64.load
    i64.xor
    local.get 0
    i64.load offset=8
    local.get 1
    i64.load offset=8
    i64.xor
    i64.or
    local.get 0
    i64.load offset=16
    local.get 1
    i64.load offset=16
    i64.xor
    local.get 0
    i64.load offset=24
    local.get 1
    i64.load offset=24
    i64.xor
    i64.or
    i64.or
    local.set 2
    local.get 2
    i64.const 4294967295
    i64.and
    local.get 2
    i64.const 32
    i64.shr_u
    i64.or
    local.set 2
    i64.const 1
    local.get 2
    i64.const 1
    i64.sub
    i64.const 32
    i64.shr_u
    i64.and
    i64.const 1
    i64.sub
    i32.wrap_i64)
  (func (;23;) (type 5) (param i32 i32 i32 i32 i32 i32) (result i32)
    local.get 1
    i64.const 0
    i64.store
    local.get 1
    i64.const 0
    i64.store offset=8
    local.get 1
    i64.const 0
    i64.store offset=16
    local.get 1
    i64.const 0
    i64.store offset=24
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    local.get 4
    local.get 5
    call 11
    drop
    local.get 0
    i32.const 16
    i32.add)
  (func (;24;) (type 5) (param i32 i32 i32 i32 i32 i32) (result i32)
    local.get 1
    i64.const 0
    i64.store
    local.get 1
    i64.const 0
    i64.store offset=8
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    local.get 4
    local.get 5
    call 12
    i32.const 0
    i32.ne
    if  ;; label = @1
      i32.const -1
      return
    end
    local.get 0
    i32.const 32
    i32.add)
  (func (;25;) (type 4) (param i32 i32 i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i64 i64 i64 i64 i32)
    local.get 0
    i32.load offset=60
    i32.const 0
    i32.eq
    if  ;; label = @1
      i32.const 16777216
      local.set 3
    end
    local.get 0
    i32.load offset=16
    local.set 4
    i32.const 5
    local.get 0
    i32.load offset=20
    local.tee 5
    i32.mul
    local.set 9
    i32.const 5
    local.get 0
    i32.load offset=24
    local.tee 6
    i32.mul
    local.set 10
    i32.const 5
    local.get 0
    i32.load offset=28
    local.tee 7
    i32.mul
    local.set 11
    i32.const 5
    local.get 0
    i32.load offset=32
    local.tee 8
    i32.mul
    local.set 12
    local.get 0
    i32.load offset=40
    local.set 13
    local.get 0
    i32.load offset=44
    local.set 14
    local.get 0
    i32.load offset=48
    local.set 15
    local.get 0
    i32.load offset=52
    local.set 16
    local.get 0
    i32.load offset=56
    local.set 17
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        i32.const 16
        i32.lt_u
        br_if 1 (;@1;)
        local.get 13
        local.get 1
        i32.load
        i32.const 67108863
        i32.and
        i32.add
        local.set 13
        local.get 14
        local.get 1
        i32.load offset=3
        i32.const 2
        i32.shr_u
        i32.const 67108863
        i32.and
        i32.add
        local.set 14
        local.get 15
        local.get 1
        i32.load offset=6
        i32.const 4
        i32.shr_u
        i32.const 67108863
        i32.and
        i32.add
        local.set 15
        local.get 16
        local.get 1
        i32.load offset=9
        i32.const 6
        i32.shr_u
        i32.const 67108863
        i32.and
        i32.add
        local.set 16
        local.get 17
        local.get 1
        i32.load offset=12
        i32.const 8
        i32.shr_u
        local.get 3
        i32.or
        i32.add
        local.set 17
        local.get 13
        i64.extend_i32_u
        local.get 4
        i64.extend_i32_u
        i64.mul
        local.get 14
        i64.extend_i32_u
        local.get 12
        i64.extend_i32_u
        i64.mul
        i64.add
        local.get 15
        i64.extend_i32_u
        local.get 11
        i64.extend_i32_u
        i64.mul
        local.get 16
        i64.extend_i32_u
        local.get 10
        i64.extend_i32_u
        i64.mul
        local.get 17
        i64.extend_i32_u
        local.get 9
        i64.extend_i32_u
        i64.mul
        i64.add
        i64.add
        i64.add
        local.set 18
        local.get 13
        i64.extend_i32_u
        local.get 5
        i64.extend_i32_u
        i64.mul
        local.get 14
        i64.extend_i32_u
        local.get 4
        i64.extend_i32_u
        i64.mul
        i64.add
        local.get 15
        i64.extend_i32_u
        local.get 12
        i64.extend_i32_u
        i64.mul
        local.get 16
        i64.extend_i32_u
        local.get 11
        i64.extend_i32_u
        i64.mul
        local.get 17
        i64.extend_i32_u
        local.get 10
        i64.extend_i32_u
        i64.mul
        i64.add
        i64.add
        i64.add
        local.set 19
        local.get 13
        i64.extend_i32_u
        local.get 6
        i64.extend_i32_u
        i64.mul
        local.get 14
        i64.extend_i32_u
        local.get 5
        i64.extend_i32_u
        i64.mul
        i64.add
        local.get 15
        i64.extend_i32_u
        local.get 4
        i64.extend_i32_u
        i64.mul
        local.get 16
        i64.extend_i32_u
        local.get 12
        i64.extend_i32_u
        i64.mul
        local.get 17
        i64.extend_i32_u
        local.get 11
        i64.extend_i32_u
        i64.mul
        i64.add
        i64.add
        i64.add
        local.set 20
        local.get 13
        i64.extend_i32_u
        local.get 7
        i64.extend_i32_u
        i64.mul
        local.get 14
        i64.extend_i32_u
        local.get 6
        i64.extend_i32_u
        i64.mul
        i64.add
        local.get 15
        i64.extend_i32_u
        local.get 5
        i64.extend_i32_u
        i64.mul
        local.get 16
        i64.extend_i32_u
        local.get 4
        i64.extend_i32_u
        i64.mul
        local.get 17
        i64.extend_i32_u
        local.get 12
        i64.extend_i32_u
        i64.mul
        i64.add
        i64.add
        i64.add
        local.set 21
        local.get 13
        i64.extend_i32_u
        local.get 8
        i64.extend_i32_u
        i64.mul
        local.get 14
        i64.extend_i32_u
        local.get 7
        i64.extend_i32_u
        i64.mul
        i64.add
        local.get 15
        i64.extend_i32_u
        local.get 6
        i64.extend_i32_u
        i64.mul
        local.get 16
        i64.extend_i32_u
        local.get 5
        i64.extend_i32_u
        i64.mul
        local.get 17
        i64.extend_i32_u
        local.get 4
        i64.extend_i32_u
        i64.mul
        i64.add
        i64.add
        i64.add
        local.set 22
        local.get 18
        i64.const 26
        i64.shr_u
        i32.wrap_i64
        local.set 23
        local.get 18
        i64.const 67108863
        i64.and
        i32.wrap_i64
        local.set 13
        local.get 19
        local.get 23
        i64.extend_i32_u
        i64.add
        local.set 19
        local.get 19
        i64.const 26
        i64.shr_u
        i32.wrap_i64
        local.set 23
        local.get 19
        i64.const 67108863
        i64.and
        i32.wrap_i64
        local.set 14
        local.get 20
        local.get 23
        i64.extend_i32_u
        i64.add
        local.set 20
        local.get 20
        i64.const 26
        i64.shr_u
        i32.wrap_i64
        local.set 23
        local.get 20
        i64.const 67108863
        i64.and
        i32.wrap_i64
        local.set 15
        local.get 21
        local.get 23
        i64.extend_i32_u
        i64.add
        local.set 21
        local.get 21
        i64.const 26
        i64.shr_u
        i32.wrap_i64
        local.set 23
        local.get 21
        i64.const 67108863
        i64.and
        i32.wrap_i64
        local.set 16
        local.get 22
        local.get 23
        i64.extend_i32_u
        i64.add
        local.set 22
        local.get 22
        i64.const 26
        i64.shr_u
        i32.wrap_i64
        local.set 23
        local.get 22
        i64.const 67108863
        i64.and
        i32.wrap_i64
        local.set 17
        local.get 13
        i32.const 5
        local.get 23
        i32.mul
        i32.add
        local.set 13
        local.get 13
        i32.const 26
        i32.shr_u
        local.set 23
        local.get 13
        i32.const 67108863
        i32.and
        local.set 13
        local.get 14
        local.get 23
        i32.add
        local.set 14
        local.get 1
        i32.const 16
        i32.add
        local.set 1
        local.get 2
        i32.const 16
        i32.sub
        local.set 2
        br 0 (;@2;)
      end
    end
    local.get 0
    local.get 13
    i32.store offset=40
    local.get 0
    local.get 14
    i32.store offset=44
    local.get 0
    local.get 15
    i32.store offset=48
    local.get 0
    local.get 16
    i32.store offset=52
    local.get 0
    local.get 17
    i32.store offset=56)
  (func (;26;) (type 9) (param i32 i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i64 i32 i32 i32)
    local.get 0
    i32.load offset=36
    i32.const 0
    i32.gt_u
    if  ;; label = @1
      i32.const 1
      local.get 0
      i32.load offset=36
      i32.add
      local.set 15
      local.get 0
      local.get 15
      i32.add
      local.set 16
      local.get 16
      i32.const 1
      i32.store8 offset=63
      block  ;; label = @2
        loop  ;; label = @3
          local.get 15
          i32.const 16
          i32.eq
          br_if 1 (;@2;)
          local.get 16
          i32.const 0
          i32.store8 offset=64
          local.get 15
          i32.const 1
          i32.add
          local.set 15
          local.get 16
          i32.const 1
          i32.add
          local.set 16
          br 0 (;@3;)
        end
      end
      local.get 0
      i32.const 1
      i32.store offset=60
      local.get 0
      local.get 0
      i32.const 64
      i32.add
      i32.const 16
      call 25
    end
    local.get 0
    i32.load offset=40
    local.set 2
    local.get 0
    i32.load offset=44
    local.set 3
    local.get 0
    i32.load offset=48
    local.set 4
    local.get 0
    i32.load offset=52
    local.set 5
    local.get 0
    i32.load offset=56
    local.set 6
    local.get 3
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 3
    i32.const 67108863
    i32.and
    local.set 3
    local.get 4
    local.get 7
    i32.add
    local.set 4
    local.get 4
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 4
    i32.const 67108863
    i32.and
    local.set 4
    local.get 5
    local.get 7
    i32.add
    local.set 5
    local.get 5
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 5
    i32.const 67108863
    i32.and
    local.set 5
    local.get 6
    local.get 7
    i32.add
    local.set 6
    local.get 6
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 6
    i32.const 67108863
    i32.and
    local.set 6
    local.get 2
    local.get 7
    i32.const 5
    i32.mul
    i32.add
    local.set 2
    local.get 2
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 2
    i32.const 67108863
    i32.and
    local.set 2
    local.get 3
    local.get 7
    i32.add
    local.set 3
    local.get 2
    i32.const 5
    i32.add
    local.set 8
    local.get 8
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 8
    i32.const 67108863
    i32.and
    local.set 8
    local.get 3
    local.get 7
    i32.add
    local.set 9
    local.get 9
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 9
    i32.const 67108863
    i32.and
    local.set 9
    local.get 4
    local.get 7
    i32.add
    local.set 10
    local.get 10
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 10
    i32.const 67108863
    i32.and
    local.set 10
    local.get 5
    local.get 7
    i32.add
    local.set 11
    local.get 11
    i32.const 26
    i32.shr_u
    local.set 7
    local.get 11
    i32.const 67108863
    i32.and
    local.set 11
    local.get 6
    local.get 7
    i32.add
    i32.const 67108864
    i32.sub
    local.set 12
    local.get 12
    i32.const 31
    i32.shr_u
    i32.const 1
    i32.sub
    local.set 14
    local.get 8
    local.get 14
    i32.and
    local.set 8
    local.get 9
    local.get 14
    i32.and
    local.set 9
    local.get 10
    local.get 14
    i32.and
    local.set 10
    local.get 11
    local.get 14
    i32.and
    local.set 11
    local.get 12
    local.get 14
    i32.and
    local.set 12
    i32.const -1
    local.get 14
    i32.sub
    local.set 14
    local.get 2
    local.get 14
    i32.and
    local.get 8
    i32.or
    local.set 2
    local.get 3
    local.get 14
    i32.and
    local.get 8
    i32.or
    local.set 3
    local.get 4
    local.get 14
    i32.and
    local.get 8
    i32.or
    local.set 4
    local.get 5
    local.get 14
    i32.and
    local.get 8
    i32.or
    local.set 5
    local.get 6
    local.get 14
    i32.and
    local.get 8
    i32.or
    local.set 6
    local.get 2
    local.get 3
    i32.const 26
    i32.shl
    i32.or
    local.set 2
    local.get 3
    i32.const 6
    i32.shr_u
    local.get 4
    i32.const 20
    i32.shl
    i32.or
    local.set 3
    local.get 4
    i32.const 12
    i32.shr_u
    local.get 5
    i32.const 14
    i32.shl
    i32.or
    local.set 4
    local.get 5
    i32.const 18
    i32.shr_u
    local.get 6
    i32.const 8
    i32.shl
    i32.or
    local.set 5
    local.get 2
    i64.extend_i32_u
    local.get 0
    i64.load32_u
    i64.add
    local.set 13
    local.get 13
    i32.wrap_i64
    local.set 2
    local.get 3
    i64.extend_i32_u
    local.get 0
    i64.load32_u offset=4
    i64.add
    local.get 13
    i64.const 32
    i64.shr_u
    i64.add
    local.set 13
    local.get 13
    i32.wrap_i64
    local.set 3
    local.get 4
    i64.extend_i32_u
    local.get 0
    i64.load32_u offset=8
    i64.add
    local.get 13
    i64.const 32
    i64.shr_u
    i64.add
    local.set 13
    local.get 13
    i32.wrap_i64
    local.set 4
    local.get 5
    i64.extend_i32_u
    local.get 0
    i64.load32_u offset=12
    i64.add
    local.get 13
    i64.const 32
    i64.shr_u
    i64.add
    local.set 13
    local.get 13
    i32.wrap_i64
    local.set 5
    local.get 1
    local.get 2
    i32.store
    local.get 1
    local.get 3
    i32.store offset=4
    local.get 1
    local.get 4
    i32.store offset=8
    local.get 1
    local.get 5
    i32.store offset=12
    local.get 0
    i64.const 0
    i64.store
    local.get 0
    i64.const 0
    i64.store offset=8
    local.get 0
    i64.const 0
    i64.store offset=16
    local.get 0
    i64.const 0
    i64.store offset=24
    local.get 0
    i64.const 0
    i64.store offset=32
    local.get 0
    i64.const 0
    i64.store offset=40
    local.get 0
    i64.const 0
    i64.store offset=48
    local.get 0
    i64.const 0
    i64.store offset=56
    local.get 0
    i64.const 0
    i64.store offset=64
    local.get 0
    i64.const 0
    i64.store offset=72)
  (func (;27;) (type 9) (param i32 i32)
    local.get 0
    local.get 1
    i32.load
    i32.const 67108863
    i32.and
    i32.store offset=16
    local.get 0
    local.get 1
    i32.load offset=3
    i32.const 2
    i32.shr_u
    i32.const 67108611
    i32.and
    i32.store offset=20
    local.get 0
    local.get 1
    i32.load offset=6
    i32.const 4
    i32.shr_u
    i32.const 67092735
    i32.and
    i32.store offset=24
    local.get 0
    local.get 1
    i32.load offset=9
    i32.const 6
    i32.shr_u
    i32.const 66076671
    i32.and
    i32.store offset=28
    local.get 0
    local.get 1
    i32.load offset=12
    i32.const 8
    i32.shr_u
    i32.const 1048575
    i32.and
    i32.store offset=32
    local.get 0
    local.get 1
    i64.load offset=16
    i64.store
    local.get 0
    local.get 1
    i64.load offset=24
    i64.store offset=8
    local.get 0
    i32.const 0
    i32.store offset=36
    local.get 0
    i64.const 0
    i64.store offset=40
    local.get 0
    i64.const 0
    i64.store offset=48
    local.get 0
    i64.const 0
    i64.store offset=56

    local.get 0
    i32.load offset=36
    drop
 
    
    )
  (func (;28;) (type 4) (param i32 i32 i32)
    (local i32 i32 i32 i32)
    local.get 0
    i32.load offset=36
    i32.const 0
    i32.ne
    if  ;; label = @1
      i32.const 16
      local.get 0
      i32.load offset=36
      i32.sub
      local.set 4
      local.get 4
      local.get 2
      i32.gt_u
      if  ;; label = @2
        local.get 2
        local.set 4
      end
      local.get 0
      local.get 0
      i32.load offset=36
      i32.add
      local.set 5
      local.get 1
      local.set 6
      block  ;; label = @2
        loop  ;; label = @3
          local.get 3
          local.get 4
          i32.eq
          br_if 1 (;@2;)
          local.get 5
          local.get 6
          i32.load8_u
          i32.store8 offset=64
          local.get 3
          i32.const 1
          i32.add
          local.set 3
          local.get 5
          i32.const 1
          i32.add
          local.set 5
          local.get 6
          i32.const 1
          i32.add
          local.set 6
          br 0 (;@3;)
        end
      end
      local.get 2
      local.get 4
      i32.sub
      local.set 2
      local.get 1
      local.get 4
      i32.add
      local.set 1
      local.get 0
      local.get 4
      local.get 0
      i32.load offset=36
      i32.add
      i32.store offset=36
      local.get 0
      i32.load offset=36
      i32.const 16
      i32.lt_u
      if  ;; label = @2
        return
      end
      local.get 0
      local.get 0
      i32.const 64
      i32.add
      i32.const 16
      call 25
      local.get 0
      i32.const 0
      i32.store offset=36
    end
    local.get 2
    i32.const 16
    i32.ge_u
    if  ;; label = @1
      local.get 2
      i32.const -16
      i32.and
      local.set 4
      local.get 0
      local.get 1
      local.get 4
      call 25
      local.get 1
      local.get 4
      i32.add
      local.set 1
      local.get 2
      local.get 4
      i32.sub
      local.set 2
    end
    local.get 2
    i32.const 0
    i32.gt_u
    if  ;; label = @1
      i32.const 0
      local.set 3
      local.get 0
      local.get 0
      i32.load offset=36
      i32.add
      local.set 5
      local.get 1
      local.set 6
      block  ;; label = @2
        loop  ;; label = @3
          local.get 3
          local.get 2
          i32.eq
          br_if 1 (;@2;)
          local.get 5
          local.get 6
          i32.load8_u
          i32.store8 offset=64
          local.get 3
          i32.const 1
          i32.add
          local.set 3
          local.get 5
          i32.const 1
          i32.add
          local.set 5
          local.get 6
          i32.const 1
          i32.add
          local.set 6
          br 0 (;@3;)
        end
      end
      local.get 0
      local.get 0
      i32.load offset=36
      local.get 2
      i32.add
      i32.store offset=36
    end)
  (func (;29;) (type 4) (param i32 i32 i32)
    (local i32 i32 i32 i32 i32)
    local.get 0
    i32.const 128
    i32.add
    local.set 3
    local.get 0
    i32.const 256
    i32.add
    local.set 4
    local.get 0
    i32.const 384
    i32.add
    local.set 5
    local.get 2
    i32.const 128
    i32.add
    local.set 6
    local.get 2
    i32.const 256
    i32.add
    local.set 7
    local.get 2
    local.get 0
    local.get 3
    call 41
    local.get 7
    local.get 1
    local.get 1
    i32.const 128
    i32.add
    call 41
    local.get 6
    local.get 1
    i32.const 128
    i32.add
    local.get 1
    call 44
    local.get 3
    local.get 3
    local.get 0
    call 44
    local.get 0
    local.get 2
    local.get 7
    call 42
    local.get 3
    local.get 3
    local.get 6
    call 42
    local.get 4
    local.get 4
    local.get 1
    i32.const 256
    i32.add
    call 42
    local.get 4
    local.get 4
    local.get 4
    call 41
    local.get 5
    local.get 5
    local.get 1
    i32.const 384
    i32.add
    call 42
    local.get 5
    local.get 5
    global.get 5
    call 42
    local.get 2
    local.get 4
    local.get 5
    call 41
    local.get 4
    local.get 4
    local.get 5
    call 44
    local.get 5
    local.get 0
    local.get 3
    call 41
    local.get 0
    local.get 0
    local.get 3
    call 44
    local.get 3
    local.get 5
    local.get 2
    call 42
    local.get 5
    local.get 0
    local.get 5
    call 42
    local.get 0
    local.get 0
    local.get 4
    call 42
    local.get 4
    local.get 2
    local.get 4
    call 42)
  (func (;30;) (type 4) (param i32 i32 i32)
    local.get 0
    local.get 1
    local.get 2
    call 48
    local.get 0
    i32.const 128
    i32.add
    local.get 1
    i32.const 128
    i32.add
    local.get 2
    call 48
    local.get 0
    i32.const 256
    i32.add
    local.get 1
    i32.const 256
    i32.add
    local.get 2
    call 48
    local.get 0
    i32.const 384
    i32.add
    local.get 1
    i32.const 384
    i32.add
    local.get 2
    call 48)
  (func (;31;) (type 9) (param i32 i32)
    (local i64 i32 i32 i32 i32 i32)
    i32.const 63
    local.set 3
    local.get 1
    i32.const 504
    i32.add
    local.set 6
    block  ;; label = @1
      loop  ;; label = @2
        local.get 3
        i32.const 31
        i32.eq
        br_if 1 (;@1;)
        i64.const 0
        local.set 2
        local.get 3
        i32.const 32
        i32.sub
        local.set 4
        local.get 3
        i32.const 12
        i32.sub
        local.set 5
        local.get 1
        local.get 4
        i32.const 3
        i32.shl
        i32.add
        local.set 7
        block  ;; label = @3
          loop  ;; label = @4
            local.get 4
            local.get 5
            i32.eq
            br_if 1 (;@3;)
            local.get 7
            local.get 7
            i64.load
            local.get 2
            local.get 6
            i64.load
            global.get 10
            local.get 4
            local.get 3
            i32.const 32
            i32.sub
            i32.sub
            i32.const 3
            i32.shl
            i32.add
            i64.load
            i64.mul
            i64.const 4
            i64.shl
            i64.sub
            i64.add
            i64.store
            local.get 7
            i64.load
            i64.const 128
            i64.add
            i64.const 8
            i64.shr_s
            local.set 2
            local.get 7
            local.get 7
            i64.load
            local.get 2
            i64.const 8
            i64.shl
            i64.sub
            i64.store
            local.get 4
            i32.const 1
            i32.add
            local.set 4
            local.get 7
            i32.const 8
            i32.add
            local.set 7
            br 0 (;@4;)
          end
        end
        local.get 7
        local.get 7
        i64.load
        local.get 2
        i64.add
        i64.store
        local.get 6
        i64.const 0
        i64.store
        local.get 3
        i32.const 1
        i32.sub
        local.set 3
        local.get 6
        i32.const 8
        i32.sub
        local.set 6
        br 0 (;@2;)
      end
    end
    i64.const 0
    local.set 2
    i32.const 0
    local.set 4
    local.get 1
    local.set 7
    block  ;; label = @1
      loop  ;; label = @2
        local.get 4
        i32.const 32
        i32.eq
        br_if 1 (;@1;)
        local.get 7
        local.get 7
        i64.load
        local.get 2
        local.get 1
        i64.load offset=248
        i64.const 4
        i64.shr_s
        global.get 10
        local.get 4
        i32.const 3
        i32.shl
        i32.add
        i64.load
        i64.mul
        i64.sub
        i64.add
        i64.store
        local.get 7
        i64.load
        i64.const 8
        i64.shr_s
        local.set 2
        local.get 7
        local.get 7
        i64.load
        i64.const 255
        i64.and
        i64.store
        local.get 4
        i32.const 1
        i32.add
        local.set 4
        local.get 7
        i32.const 8
        i32.add
        local.set 7
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 4
    local.get 1
    local.set 7
    block  ;; label = @1
      loop  ;; label = @2
        local.get 4
        i32.const 32
        i32.eq
        br_if 1 (;@1;)
        local.get 7
        local.get 7
        i64.load
        local.get 2
        global.get 10
        local.get 4
        i32.const 3
        i32.shl
        i32.add
        i64.load
        i64.mul
        i64.sub
        i64.store
        local.get 4
        i32.const 1
        i32.add
        local.set 4
        local.get 7
        i32.const 8
        i32.add
        local.set 7
        br 0 (;@2;)
      end
    end
    i32.const 0
    local.set 3
    local.get 1
    local.set 6
    block  ;; label = @1
      loop  ;; label = @2
        local.get 3
        i32.const 32
        i32.eq
        br_if 1 (;@1;)
        local.get 6
        local.get 6
        i64.load offset=8
        local.get 6
        i64.load
        i64.const 8
        i64.shr_s
        i64.add
        i64.store offset=8
        local.get 0
        local.get 3
        i32.add
        local.get 6
        i64.load
        i64.store8
        local.get 3
        i32.const 1
        i32.add
        local.set 3
        local.get 6
        i32.const 8
        i32.add
        local.set 6
        br 0 (;@2;)
      end
    end)
  (func (;32;) (type 7) (param i32 i32 i32) (result i32)
    local.get 2
    local.get 0
    local.get 2
    i32.const 64
    i32.add
    call 47
    local.get 2
    i32.const 32
    i32.add
    local.get 1
    local.get 2
    i32.const 64
    i32.add
    call 47
    local.get 2
    local.get 2
    i32.const 32
    i32.add
    call 22)
  (func (;33;) (type 4) (param i32 i32 i32)
    (local i32 i32)
    local.get 1
    i32.const 128
    i32.add
    local.set 3
    local.get 1
    i32.const 256
    i32.add
    local.tee 4
    local.get 1
    i32.const 256
    i32.add
    local.get 2
    call 46
    local.get 2
    local.get 1
    local.get 4
    call 42
    local.get 3
    local.get 1
    i32.const 128
    i32.add
    local.get 4
    call 42
    local.get 0
    local.get 3
    local.get 4
    call 47
    local.get 0
    local.get 0
    i32.load8_u offset=31
    local.get 2
    local.get 3
    call 34
    i32.const 7
    i32.shl
    i32.xor
    i32.store8 offset=31)
  (func (;34;) (type 8) (param i32 i32) (result i32)
    (local i32)
    local.get 1
    i32.const 256
    i32.add
    local.tee 2
    local.get 0
    local.get 1
    call 47
    i32.const 1
    local.get 2
    i32.load8_u
    i32.and)
  (func (;35;) (type 4) (param i32 i32 i32)
    (local i32)
    local.get 2
    local.get 1
    i64.load
    i64.store
    local.get 2
    local.get 1
    i64.load offset=8
    i64.store offset=8
    local.get 2
    local.get 1
    i64.load offset=16
    i64.store offset=16
    local.get 2
    local.get 1
    i64.load offset=24
    i64.store offset=24
    local.get 2
    local.get 1
    i64.load offset=32
    i64.store offset=32
    local.get 2
    local.get 1
    i64.load offset=40
    i64.store offset=40
    local.get 2
    local.get 1
    i64.load offset=48
    i64.store offset=48
    local.get 2
    local.get 1
    i64.load offset=56
    i64.store offset=56
    local.get 2
    local.get 1
    i64.load offset=64
    i64.store offset=64
    local.get 2
    local.get 1
    i64.load offset=72
    i64.store offset=72
    local.get 2
    local.get 1
    i64.load offset=80
    i64.store offset=80
    local.get 2
    local.get 1
    i64.load offset=88
    i64.store offset=88
    local.get 2
    local.get 1
    i64.load offset=96
    i64.store offset=96
    local.get 2
    local.get 1
    i64.load offset=104
    i64.store offset=104
    local.get 2
    local.get 1
    i64.load offset=112
    i64.store offset=112
    local.get 2
    local.get 1
    i64.load offset=120
    i64.store offset=120
    i32.const 251
    local.set 3
    block  ;; label = @1
      loop  ;; label = @2
        local.get 3
        i32.eqz
        br_if 1 (;@1;)
        local.get 2
        local.get 2
        call 43
        local.get 3
        i32.const 2
        i32.ne
        if  ;; label = @3
          local.get 2
          local.get 2
          local.get 1
          call 42
        end
        local.get 3
        i32.const 1
        i32.sub
        local.set 3
        br 0 (;@2;)
      end
    end
    local.get 0
    local.get 2
    i64.load
    i64.store
    local.get 0
    local.get 2
    i64.load offset=8
    i64.store offset=8
    local.get 0
    local.get 2
    i64.load offset=16
    i64.store offset=16
    local.get 0
    local.get 2
    i64.load offset=24
    i64.store offset=24
    local.get 0
    local.get 2
    i64.load offset=32
    i64.store offset=32
    local.get 0
    local.get 2
    i64.load offset=40
    i64.store offset=40
    local.get 0
    local.get 2
    i64.load offset=48
    i64.store offset=48
    local.get 0
    local.get 2
    i64.load offset=56
    i64.store offset=56
    local.get 0
    local.get 2
    i64.load offset=64
    i64.store offset=64
    local.get 0
    local.get 2
    i64.load offset=72
    i64.store offset=72
    local.get 0
    local.get 2
    i64.load offset=80
    i64.store offset=80
    local.get 0
    local.get 2
    i64.load offset=88
    i64.store offset=88
    local.get 0
    local.get 2
    i64.load offset=96
    i64.store offset=96
    local.get 0
    local.get 2
    i64.load offset=104
    i64.store offset=104
    local.get 0
    local.get 2
    i64.load offset=112
    i64.store offset=112
    local.get 0
    local.get 2
    i64.load offset=120
    i64.store offset=120)
  (func (;36;) (type 9) (param i32 i32)
    (local i32)
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        i32.const 64
        i32.eq
        br_if 1 (;@1;)
        local.get 1
        local.get 2
        i32.const 3
        i32.shl
        i32.add
        local.get 0
        local.get 2
        i32.add
        i64.load8_u
        i64.store
        local.get 2
        i32.const 1
        i32.add
        local.set 2
        br 0 (;@2;)
      end
    end
    local.get 0
    i64.const 0
    i64.store
    local.get 0
    i64.const 0
    i64.store offset=8
    local.get 0
    i64.const 0
    i64.store offset=16
    local.get 0
    i64.const 0
    i64.store offset=24
    local.get 0
    i64.const 0
    i64.store offset=32
    local.get 0
    i64.const 0
    i64.store offset=40
    local.get 0
    i64.const 0
    i64.store offset=48
    local.get 0
    i64.const 0
    i64.store offset=56
    local.get 0
    local.get 1
    call 31)
  (func (;37;) (type 4) (param i32 i32 i32)
    local.get 2
    global.get 6
    call 39
    local.get 2
    i32.const 128
    i32.add
    global.get 7
    call 39
    local.get 2
    i32.const 256
    i32.add
    global.get 2
    call 39
    local.get 2
    i32.const 384
    i32.add
    global.get 6
    global.get 7
    call 42
    local.get 0
    local.get 2
    local.get 1
    local.get 2
    i32.const 512
    i32.add
    call 38)
  (func (;38;) (type 0) (param i32 i32 i32 i32)
    (local i32 i32)
    local.get 0
    global.get 0
    call 39
    local.get 0
    i32.const 128
    i32.add
    global.get 2
    call 39
    local.get 0
    i32.const 256
    i32.add
    global.get 2
    call 39
    local.get 0
    i32.const 384
    i32.add
    global.get 0
    call 39
    i32.const 255
    local.set 5
    block  ;; label = @1
      loop  ;; label = @2
        local.get 2
        local.get 5
        i32.const 3
        i32.shr_u
        i32.add
        i32.load8_u
        local.get 5
        i32.const 7
        i32.and
        i32.shr_u
        i32.const 1
        i32.and
        local.set 4
        local.get 0
        local.get 1
        local.get 4
        call 30
        local.get 1
        local.get 0
        local.get 3
        call 29
        local.get 0
        local.get 0
        local.get 3
        call 29
        local.get 0
        local.get 1
        local.get 4
        call 30
        local.get 5
        i32.const 1
        i32.sub
        local.set 5
        local.get 5
        i32.const 0
        i32.ge_s
        br_if 0 (;@2;)
        br 1 (;@1;)
      end
    end)
  (func (;39;) (type 9) (param i32 i32)
    local.get 0
    local.get 1
    i64.load
    i64.store
    local.get 0
    local.get 1
    i64.load offset=8
    i64.store offset=8
    local.get 0
    local.get 1
    i64.load offset=16
    i64.store offset=16
    local.get 0
    local.get 1
    i64.load offset=24
    i64.store offset=24
    local.get 0
    local.get 1
    i64.load offset=32
    i64.store offset=32
    local.get 0
    local.get 1
    i64.load offset=40
    i64.store offset=40
    local.get 0
    local.get 1
    i64.load offset=48
    i64.store offset=48
    local.get 0
    local.get 1
    i64.load offset=56
    i64.store offset=56
    local.get 0
    local.get 1
    i64.load offset=64
    i64.store offset=64
    local.get 0
    local.get 1
    i64.load offset=72
    i64.store offset=72
    local.get 0
    local.get 1
    i64.load offset=80
    i64.store offset=80
    local.get 0
    local.get 1
    i64.load offset=88
    i64.store offset=88
    local.get 0
    local.get 1
    i64.load offset=96
    i64.store offset=96
    local.get 0
    local.get 1
    i64.load offset=104
    i64.store offset=104
    local.get 0
    local.get 1
    i64.load offset=112
    i64.store offset=112
    local.get 0
    local.get 1
    i64.load offset=120
    i64.store offset=120)
  (func (;40;) (type 7) (param i32 i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    local.get 2
    local.tee 3
    i32.const 128
    i32.add
    local.tee 4
    i32.const 128
    i32.add
    local.tee 5
    i32.const 128
    i32.add
    local.tee 6
    i32.const 128
    i32.add
    local.tee 7
    i32.const 128
    i32.add
    local.tee 8
    i32.const 128
    i32.add
    local.set 9
    local.get 0
    i32.const 256
    i32.add
    global.get 2
    call 39
    local.get 0
    i32.const 128
    i32.add
    local.get 1
    call 49
    local.get 5
    local.get 0
    i32.const 128
    i32.add
    call 43
    local.get 6
    local.get 5
    global.get 4
    call 42
    local.get 5
    local.get 5
    local.get 0
    i32.const 256
    i32.add
    call 44
    local.get 6
    local.get 0
    i32.const 256
    i32.add
    local.get 6
    call 41
    local.get 7
    local.get 6
    call 43
    local.get 8
    local.get 7
    call 43
    local.get 9
    local.get 8
    local.get 7
    call 42
    local.get 3
    local.get 9
    local.get 5
    call 42
    local.get 3
    local.get 3
    local.get 6
    call 42
    local.get 3
    local.get 3
    local.get 7
    call 35
    local.get 3
    local.get 3
    local.get 5
    call 42
    local.get 3
    local.get 3
    local.get 6
    call 42
    local.get 3
    local.get 3
    local.get 6
    call 42
    local.get 0
    local.get 3
    local.get 6
    call 42
    local.get 4
    local.get 0
    call 43
    local.get 4
    local.get 4
    local.get 6
    call 42
    local.get 4
    local.get 5
    local.get 7
    call 32
    if  ;; label = @1
      local.get 0
      local.get 0
      global.get 8
      call 42
    end
    local.get 4
    local.get 0
    call 43
    local.get 4
    local.get 4
    local.get 6
    call 42
    local.get 4
    local.get 5
    local.get 7
    call 32
    if  ;; label = @1
      i32.const -1
      return
    end
    local.get 0
    local.get 7
    call 34
    local.get 1
    i32.load8_u offset=31
    i32.const 7
    i32.shr_u
    i32.eq
    if  ;; label = @1
      local.get 0
      global.get 0
      local.get 0
      call 44
    end
    local.get 0
    i32.const 384
    i32.add
    local.get 0
    local.get 0
    i32.const 128
    i32.add
    call 42
    i32.const 0)
  (func (;41;) (type 4) (param i32 i32 i32)
    local.get 0
    local.get 1
    i64.load
    local.get 2
    i64.load
    i64.add
    i64.store
    local.get 0
    local.get 1
    i64.load offset=8
    local.get 2
    i64.load offset=8
    i64.add
    i64.store offset=8
    local.get 0
    local.get 1
    i64.load offset=16
    local.get 2
    i64.load offset=16
    i64.add
    i64.store offset=16
    local.get 0
    local.get 1
    i64.load offset=24
    local.get 2
    i64.load offset=24
    i64.add
    i64.store offset=24
    local.get 0
    local.get 1
    i64.load offset=32
    local.get 2
    i64.load offset=32
    i64.add
    i64.store offset=32
    local.get 0
    local.get 1
    i64.load offset=40
    local.get 2
    i64.load offset=40
    i64.add
    i64.store offset=40
    local.get 0
    local.get 1
    i64.load offset=48
    local.get 2
    i64.load offset=48
    i64.add
    i64.store offset=48
    local.get 0
    local.get 1
    i64.load offset=56
    local.get 2
    i64.load offset=56
    i64.add
    i64.store offset=56
    local.get 0
    local.get 1
    i64.load offset=64
    local.get 2
    i64.load offset=64
    i64.add
    i64.store offset=64
    local.get 0
    local.get 1
    i64.load offset=72
    local.get 2
    i64.load offset=72
    i64.add
    i64.store offset=72
    local.get 0
    local.get 1
    i64.load offset=80
    local.get 2
    i64.load offset=80
    i64.add
    i64.store offset=80
    local.get 0
    local.get 1
    i64.load offset=88
    local.get 2
    i64.load offset=88
    i64.add
    i64.store offset=88
    local.get 0
    local.get 1
    i64.load offset=96
    local.get 2
    i64.load offset=96
    i64.add
    i64.store offset=96
    local.get 0
    local.get 1
    i64.load offset=104
    local.get 2
    i64.load offset=104
    i64.add
    i64.store offset=104
    local.get 0
    local.get 1
    i64.load offset=112
    local.get 2
    i64.load offset=112
    i64.add
    i64.store offset=112
    local.get 0
    local.get 1
    i64.load offset=120
    local.get 2
    i64.load offset=120
    i64.add
    i64.store offset=120)
  (func (;42;) (type 4) (param i32 i32 i32)
    (local i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64)
    local.get 2
    i64.load
    local.set 36
    local.get 2
    i64.load offset=8
    local.set 37
    local.get 2
    i64.load offset=16
    local.set 38
    local.get 2
    i64.load offset=24
    local.set 39
    local.get 2
    i64.load offset=32
    local.set 40
    local.get 2
    i64.load offset=40
    local.set 41
    local.get 2
    i64.load offset=48
    local.set 42
    local.get 2
    i64.load offset=56
    local.set 43
    local.get 2
    i64.load offset=64
    local.set 44
    local.get 2
    i64.load offset=72
    local.set 45
    local.get 2
    i64.load offset=80
    local.set 46
    local.get 2
    i64.load offset=88
    local.set 47
    local.get 2
    i64.load offset=96
    local.set 48
    local.get 2
    i64.load offset=104
    local.set 49
    local.get 2
    i64.load offset=112
    local.set 50
    local.get 2
    i64.load offset=120
    local.set 51
    local.get 1
    i64.load
    local.set 3
    local.get 5
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 5
    local.get 6
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 6
    local.get 7
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 7
    local.get 8
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 8
    local.get 9
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 9
    local.get 10
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 10
    local.get 11
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 11
    local.get 12
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 20
    local.get 1
    i64.load offset=8
    local.set 3
    local.get 6
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 6
    local.get 7
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 7
    local.get 8
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 8
    local.get 9
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 9
    local.get 10
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 10
    local.get 11
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 11
    local.get 12
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 21
    local.get 1
    i64.load offset=16
    local.set 3
    local.get 7
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 7
    local.get 8
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 8
    local.get 9
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 9
    local.get 10
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 10
    local.get 11
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 11
    local.get 12
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 22
    local.get 1
    i64.load offset=24
    local.set 3
    local.get 8
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 8
    local.get 9
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 9
    local.get 10
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 10
    local.get 11
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 11
    local.get 12
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 23
    local.get 1
    i64.load offset=32
    local.set 3
    local.get 9
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 9
    local.get 10
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 10
    local.get 11
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 11
    local.get 12
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 24
    local.get 1
    i64.load offset=40
    local.set 3
    local.get 10
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 10
    local.get 11
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 11
    local.get 12
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 25
    local.get 1
    i64.load offset=48
    local.set 3
    local.get 11
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 11
    local.get 12
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 26
    local.get 1
    i64.load offset=56
    local.set 3
    local.get 12
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 12
    local.get 13
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 27
    local.get 1
    i64.load offset=64
    local.set 3
    local.get 13
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 13
    local.get 14
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 28
    local.get 1
    i64.load offset=72
    local.set 3
    local.get 14
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 14
    local.get 15
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 28
    local.get 29
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 29
    local.get 1
    i64.load offset=80
    local.set 3
    local.get 15
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 15
    local.get 16
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 28
    local.get 29
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 29
    local.get 30
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 30
    local.get 1
    i64.load offset=88
    local.set 3
    local.get 16
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 16
    local.get 17
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 28
    local.get 29
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 29
    local.get 30
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 30
    local.get 31
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 31
    local.get 1
    i64.load offset=96
    local.set 3
    local.get 17
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 17
    local.get 18
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 28
    local.get 29
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 29
    local.get 30
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 30
    local.get 31
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 31
    local.get 32
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 32
    local.get 1
    i64.load offset=104
    local.set 3
    local.get 18
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 18
    local.get 19
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 28
    local.get 29
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 29
    local.get 30
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 30
    local.get 31
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 31
    local.get 32
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 32
    local.get 33
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 33
    local.get 1
    i64.load offset=112
    local.set 3
    local.get 19
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 19
    local.get 20
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 28
    local.get 29
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 29
    local.get 30
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 30
    local.get 31
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 31
    local.get 32
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 32
    local.get 33
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 33
    local.get 34
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 34
    local.get 1
    i64.load offset=120
    local.set 3
    local.get 20
    local.get 3
    local.get 36
    i64.mul
    i64.add
    local.set 20
    local.get 21
    local.get 3
    local.get 37
    i64.mul
    i64.add
    local.set 21
    local.get 22
    local.get 3
    local.get 38
    i64.mul
    i64.add
    local.set 22
    local.get 23
    local.get 3
    local.get 39
    i64.mul
    i64.add
    local.set 23
    local.get 24
    local.get 3
    local.get 40
    i64.mul
    i64.add
    local.set 24
    local.get 25
    local.get 3
    local.get 41
    i64.mul
    i64.add
    local.set 25
    local.get 26
    local.get 3
    local.get 42
    i64.mul
    i64.add
    local.set 26
    local.get 27
    local.get 3
    local.get 43
    i64.mul
    i64.add
    local.set 27
    local.get 28
    local.get 3
    local.get 44
    i64.mul
    i64.add
    local.set 28
    local.get 29
    local.get 3
    local.get 45
    i64.mul
    i64.add
    local.set 29
    local.get 30
    local.get 3
    local.get 46
    i64.mul
    i64.add
    local.set 30
    local.get 31
    local.get 3
    local.get 47
    i64.mul
    i64.add
    local.set 31
    local.get 32
    local.get 3
    local.get 48
    i64.mul
    i64.add
    local.set 32
    local.get 33
    local.get 3
    local.get 49
    i64.mul
    i64.add
    local.set 33
    local.get 34
    local.get 3
    local.get 50
    i64.mul
    i64.add
    local.set 34
    local.get 35
    local.get 3
    local.get 51
    i64.mul
    i64.add
    local.set 35
    local.get 5
    i64.const 38
    local.get 21
    i64.mul
    i64.add
    local.set 5
    local.get 6
    i64.const 38
    local.get 22
    i64.mul
    i64.add
    local.set 6
    local.get 7
    i64.const 38
    local.get 23
    i64.mul
    i64.add
    local.set 7
    local.get 8
    i64.const 38
    local.get 24
    i64.mul
    i64.add
    local.set 8
    local.get 9
    i64.const 38
    local.get 25
    i64.mul
    i64.add
    local.set 9
    local.get 10
    i64.const 38
    local.get 26
    i64.mul
    i64.add
    local.set 10
    local.get 11
    i64.const 38
    local.get 27
    i64.mul
    i64.add
    local.set 11
    local.get 12
    i64.const 38
    local.get 28
    i64.mul
    i64.add
    local.set 12
    local.get 13
    i64.const 38
    local.get 29
    i64.mul
    i64.add
    local.set 13
    local.get 14
    i64.const 38
    local.get 30
    i64.mul
    i64.add
    local.set 14
    local.get 15
    i64.const 38
    local.get 31
    i64.mul
    i64.add
    local.set 15
    local.get 16
    i64.const 38
    local.get 32
    i64.mul
    i64.add
    local.set 16
    local.get 17
    i64.const 38
    local.get 33
    i64.mul
    i64.add
    local.set 17
    local.get 18
    i64.const 38
    local.get 34
    i64.mul
    i64.add
    local.set 18
    local.get 19
    i64.const 38
    local.get 35
    i64.mul
    i64.add
    local.set 19
    i64.const 1
    local.set 4
    local.get 5
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 5
    local.get 6
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 6
    local.get 7
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 7
    local.get 8
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 8
    local.get 9
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 9
    local.get 10
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 10
    local.get 11
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 11
    local.get 12
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 12
    local.get 13
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 13
    local.get 14
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 14
    local.get 15
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 15
    local.get 16
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 16
    local.get 17
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 17
    local.get 18
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 18
    local.get 19
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 19
    local.get 20
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 20
    local.get 5
    i64.const 38
    local.get 4
    i64.const 1
    i64.sub
    i64.mul
    i64.add
    local.set 5
    i64.const 1
    local.set 4
    local.get 5
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 5
    local.get 6
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 6
    local.get 7
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 7
    local.get 8
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 8
    local.get 9
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 9
    local.get 10
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 10
    local.get 11
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 11
    local.get 12
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 12
    local.get 13
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 13
    local.get 14
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 14
    local.get 15
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 15
    local.get 16
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 16
    local.get 17
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 17
    local.get 18
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 18
    local.get 19
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 19
    local.get 20
    local.get 4
    i64.add
    i64.const 65535
    i64.add
    local.set 3
    local.get 3
    i64.const 16
    i64.shr_s
    local.set 4
    local.get 3
    local.get 4
    i64.const 16
    i64.shl
    i64.sub
    local.set 20
    local.get 5
    i64.const 38
    local.get 4
    i64.const 1
    i64.sub
    i64.mul
    i64.add
    local.set 5
    local.get 0
    local.get 5
    i64.store
    local.get 0
    local.get 6
    i64.store offset=8
    local.get 0
    local.get 7
    i64.store offset=16
    local.get 0
    local.get 8
    i64.store offset=24
    local.get 0
    local.get 9
    i64.store offset=32
    local.get 0
    local.get 10
    i64.store offset=40
    local.get 0
    local.get 11
    i64.store offset=48
    local.get 0
    local.get 12
    i64.store offset=56
    local.get 0
    local.get 13
    i64.store offset=64
    local.get 0
    local.get 14
    i64.store offset=72
    local.get 0
    local.get 15
    i64.store offset=80
    local.get 0
    local.get 16
    i64.store offset=88
    local.get 0
    local.get 17
    i64.store offset=96
    local.get 0
    local.get 18
    i64.store offset=104
    local.get 0
    local.get 19
    i64.store offset=112
    local.get 0
    local.get 20
    i64.store offset=120)
  (func (;43;) (type 9) (param i32 i32)
    local.get 0
    local.get 1
    local.get 1
    call 42)
  (func (;44;) (type 4) (param i32 i32 i32)
    local.get 0
    local.get 1
    i64.load
    local.get 2
    i64.load
    i64.sub
    i64.store
    local.get 0
    local.get 1
    i64.load offset=8
    local.get 2
    i64.load offset=8
    i64.sub
    i64.store offset=8
    local.get 0
    local.get 1
    i64.load offset=16
    local.get 2
    i64.load offset=16
    i64.sub
    i64.store offset=16
    local.get 0
    local.get 1
    i64.load offset=24
    local.get 2
    i64.load offset=24
    i64.sub
    i64.store offset=24
    local.get 0
    local.get 1
    i64.load offset=32
    local.get 2
    i64.load offset=32
    i64.sub
    i64.store offset=32
    local.get 0
    local.get 1
    i64.load offset=40
    local.get 2
    i64.load offset=40
    i64.sub
    i64.store offset=40
    local.get 0
    local.get 1
    i64.load offset=48
    local.get 2
    i64.load offset=48
    i64.sub
    i64.store offset=48
    local.get 0
    local.get 1
    i64.load offset=56
    local.get 2
    i64.load offset=56
    i64.sub
    i64.store offset=56
    local.get 0
    local.get 1
    i64.load offset=64
    local.get 2
    i64.load offset=64
    i64.sub
    i64.store offset=64
    local.get 0
    local.get 1
    i64.load offset=72
    local.get 2
    i64.load offset=72
    i64.sub
    i64.store offset=72
    local.get 0
    local.get 1
    i64.load offset=80
    local.get 2
    i64.load offset=80
    i64.sub
    i64.store offset=80
    local.get 0
    local.get 1
    i64.load offset=88
    local.get 2
    i64.load offset=88
    i64.sub
    i64.store offset=88
    local.get 0
    local.get 1
    i64.load offset=96
    local.get 2
    i64.load offset=96
    i64.sub
    i64.store offset=96
    local.get 0
    local.get 1
    i64.load offset=104
    local.get 2
    i64.load offset=104
    i64.sub
    i64.store offset=104
    local.get 0
    local.get 1
    i64.load offset=112
    local.get 2
    i64.load offset=112
    i64.sub
    i64.store offset=112
    local.get 0
    local.get 1
    i64.load offset=120
    local.get 2
    i64.load offset=120
    i64.sub
    i64.store offset=120)
  (func (;45;) (type 10) (param i32)
    (local i64 i64)
    i64.const 1
    local.set 2
    local.get 0
    i64.load
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store
    local.get 0
    i64.load offset=8
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=8
    local.get 0
    i64.load offset=16
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=16
    local.get 0
    i64.load offset=24
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=24
    local.get 0
    i64.load offset=32
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=32
    local.get 0
    i64.load offset=40
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=40
    local.get 0
    i64.load offset=48
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=48
    local.get 0
    i64.load offset=56
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=56
    local.get 0
    i64.load offset=64
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=64
    local.get 0
    i64.load offset=72
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=72
    local.get 0
    i64.load offset=80
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=80
    local.get 0
    i64.load offset=88
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=88
    local.get 0
    i64.load offset=96
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=96
    local.get 0
    i64.load offset=104
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=104
    local.get 0
    i64.load offset=112
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=112
    local.get 0
    i64.load offset=120
    local.get 2
    i64.add
    i64.const 65535
    i64.add
    local.set 1
    local.get 1
    i64.const 16
    i64.shr_s
    local.set 2
    local.get 0
    local.get 1
    local.get 2
    i64.const 16
    i64.shl
    i64.sub
    i64.store offset=120
    local.get 0
    local.get 0
    i64.load
    i64.const 38
    local.get 2
    i64.const 1
    i64.sub
    i64.mul
    i64.add
    i64.store)
  (func (;46;) (type 4) (param i32 i32 i32)
    (local i32)
    local.get 2
    local.get 1
    i64.load
    i64.store
    local.get 2
    local.get 1
    i64.load offset=8
    i64.store offset=8
    local.get 2
    local.get 1
    i64.load offset=16
    i64.store offset=16
    local.get 2
    local.get 1
    i64.load offset=24
    i64.store offset=24
    local.get 2
    local.get 1
    i64.load offset=32
    i64.store offset=32
    local.get 2
    local.get 1
    i64.load offset=40
    i64.store offset=40
    local.get 2
    local.get 1
    i64.load offset=48
    i64.store offset=48
    local.get 2
    local.get 1
    i64.load offset=56
    i64.store offset=56
    local.get 2
    local.get 1
    i64.load offset=64
    i64.store offset=64
    local.get 2
    local.get 1
    i64.load offset=72
    i64.store offset=72
    local.get 2
    local.get 1
    i64.load offset=80
    i64.store offset=80
    local.get 2
    local.get 1
    i64.load offset=88
    i64.store offset=88
    local.get 2
    local.get 1
    i64.load offset=96
    i64.store offset=96
    local.get 2
    local.get 1
    i64.load offset=104
    i64.store offset=104
    local.get 2
    local.get 1
    i64.load offset=112
    i64.store offset=112
    local.get 2
    local.get 1
    i64.load offset=120
    i64.store offset=120
    i32.const 253
    local.set 3
    block  ;; label = @1
      loop  ;; label = @2
        local.get 3
        i32.const 0
        i32.lt_s
        br_if 1 (;@1;)
        local.get 2
        local.get 2
        call 43
        local.get 3
        i32.const 2
        i32.ne
        local.get 3
        i32.const 4
        i32.ne
        i32.and
        if  ;; label = @3
          local.get 2
          local.get 2
          local.get 1
          call 42
        end
        local.get 3
        i32.const 1
        i32.sub
        local.set 3
        br 0 (;@2;)
      end
    end
    local.get 0
    local.get 2
    i64.load
    i64.store
    local.get 0
    local.get 2
    i64.load offset=8
    i64.store offset=8
    local.get 0
    local.get 2
    i64.load offset=16
    i64.store offset=16
    local.get 0
    local.get 2
    i64.load offset=24
    i64.store offset=24
    local.get 0
    local.get 2
    i64.load offset=32
    i64.store offset=32
    local.get 0
    local.get 2
    i64.load offset=40
    i64.store offset=40
    local.get 0
    local.get 2
    i64.load offset=48
    i64.store offset=48
    local.get 0
    local.get 2
    i64.load offset=56
    i64.store offset=56
    local.get 0
    local.get 2
    i64.load offset=64
    i64.store offset=64
    local.get 0
    local.get 2
    i64.load offset=72
    i64.store offset=72
    local.get 0
    local.get 2
    i64.load offset=80
    i64.store offset=80
    local.get 0
    local.get 2
    i64.load offset=88
    i64.store offset=88
    local.get 0
    local.get 2
    i64.load offset=96
    i64.store offset=96
    local.get 0
    local.get 2
    i64.load offset=104
    i64.store offset=104
    local.get 0
    local.get 2
    i64.load offset=112
    i64.store offset=112
    local.get 0
    local.get 2
    i64.load offset=120
    i64.store offset=120)
  (func (;47;) (type 4) (param i32 i32 i32)
    (local i32 i32 i32)
    local.get 2
    local.tee 4
    i32.const 128
    i32.add
    local.set 5
    local.get 5
    local.get 1
    i64.load
    i64.store
    local.get 5
    local.get 1
    i64.load offset=8
    i64.store offset=8
    local.get 5
    local.get 1
    i64.load offset=16
    i64.store offset=16
    local.get 5
    local.get 1
    i64.load offset=24
    i64.store offset=24
    local.get 5
    local.get 1
    i64.load offset=32
    i64.store offset=32
    local.get 5
    local.get 1
    i64.load offset=40
    i64.store offset=40
    local.get 5
    local.get 1
    i64.load offset=48
    i64.store offset=48
    local.get 5
    local.get 1
    i64.load offset=56
    i64.store offset=56
    local.get 5
    local.get 1
    i64.load offset=64
    i64.store offset=64
    local.get 5
    local.get 1
    i64.load offset=72
    i64.store offset=72
    local.get 5
    local.get 1
    i64.load offset=80
    i64.store offset=80
    local.get 5
    local.get 1
    i64.load offset=88
    i64.store offset=88
    local.get 5
    local.get 1
    i64.load offset=96
    i64.store offset=96
    local.get 5
    local.get 1
    i64.load offset=104
    i64.store offset=104
    local.get 5
    local.get 1
    i64.load offset=112
    i64.store offset=112
    local.get 5
    local.get 1
    i64.load offset=120
    i64.store offset=120
    local.get 5
    call 45
    local.get 5
    call 45
    local.get 5
    call 45
    local.get 4
    local.get 5
    i64.load
    i64.const 65517
    i64.sub
    i64.store
    local.get 4
    local.get 5
    i64.load offset=8
    i64.const 65535
    i64.sub
    local.get 4
    i64.load
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=8
    local.get 4
    local.get 4
    i64.load
    i64.const 65535
    i64.and
    i64.store
    local.get 4
    local.get 5
    i64.load offset=16
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=8
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=16
    local.get 4
    local.get 4
    i64.load offset=8
    i64.const 65535
    i64.and
    i64.store offset=8
    local.get 4
    local.get 5
    i64.load offset=24
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=16
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=24
    local.get 4
    local.get 4
    i64.load offset=16
    i64.const 65535
    i64.and
    i64.store offset=16
    local.get 4
    local.get 5
    i64.load offset=32
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=24
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=32
    local.get 4
    local.get 4
    i64.load offset=24
    i64.const 65535
    i64.and
    i64.store offset=24
    local.get 4
    local.get 5
    i64.load offset=40
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=32
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=40
    local.get 4
    local.get 4
    i64.load offset=32
    i64.const 65535
    i64.and
    i64.store offset=32
    local.get 4
    local.get 5
    i64.load offset=48
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=40
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=48
    local.get 4
    local.get 4
    i64.load offset=40
    i64.const 65535
    i64.and
    i64.store offset=40
    local.get 4
    local.get 5
    i64.load offset=56
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=48
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=56
    local.get 4
    local.get 4
    i64.load offset=48
    i64.const 65535
    i64.and
    i64.store offset=48
    local.get 4
    local.get 5
    i64.load offset=64
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=56
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=64
    local.get 4
    local.get 4
    i64.load offset=56
    i64.const 65535
    i64.and
    i64.store offset=56
    local.get 4
    local.get 5
    i64.load offset=72
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=64
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=72
    local.get 4
    local.get 4
    i64.load offset=64
    i64.const 65535
    i64.and
    i64.store offset=64
    local.get 4
    local.get 5
    i64.load offset=80
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=72
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=80
    local.get 4
    local.get 4
    i64.load offset=72
    i64.const 65535
    i64.and
    i64.store offset=72
    local.get 4
    local.get 5
    i64.load offset=88
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=80
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=88
    local.get 4
    local.get 4
    i64.load offset=80
    i64.const 65535
    i64.and
    i64.store offset=80
    local.get 4
    local.get 5
    i64.load offset=96
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=88
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=96
    local.get 4
    local.get 4
    i64.load offset=88
    i64.const 65535
    i64.and
    i64.store offset=88
    local.get 4
    local.get 5
    i64.load offset=104
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=96
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=104
    local.get 4
    local.get 4
    i64.load offset=96
    i64.const 65535
    i64.and
    i64.store offset=96
    local.get 4
    local.get 5
    i64.load offset=112
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=104
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=112
    local.get 4
    local.get 4
    i64.load offset=104
    i64.const 65535
    i64.and
    i64.store offset=104
    local.get 4
    local.get 5
    i64.load offset=120
    i64.const 32767
    i64.sub
    local.get 4
    i64.load offset=112
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=120
    local.get 4
    i64.load offset=120
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i32.wrap_i64
    local.set 3
    local.get 4
    local.get 4
    i64.load offset=112
    i64.const 65535
    i64.and
    i64.store offset=112
    local.get 5
    local.get 4
    i32.const 1
    local.get 3
    i32.sub
    call 48
    local.get 4
    local.get 5
    i64.load
    i64.const 65517
    i64.sub
    i64.store
    local.get 4
    local.get 5
    i64.load offset=8
    i64.const 65535
    i64.sub
    local.get 4
    i64.load
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=8
    local.get 4
    local.get 4
    i64.load
    i64.const 65535
    i64.and
    i64.store
    local.get 4
    local.get 5
    i64.load offset=16
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=8
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=16
    local.get 4
    local.get 4
    i64.load offset=8
    i64.const 65535
    i64.and
    i64.store offset=8
    local.get 4
    local.get 5
    i64.load offset=24
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=16
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=24
    local.get 4
    local.get 4
    i64.load offset=16
    i64.const 65535
    i64.and
    i64.store offset=16
    local.get 4
    local.get 5
    i64.load offset=32
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=24
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=32
    local.get 4
    local.get 4
    i64.load offset=24
    i64.const 65535
    i64.and
    i64.store offset=24
    local.get 4
    local.get 5
    i64.load offset=40
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=32
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=40
    local.get 4
    local.get 4
    i64.load offset=32
    i64.const 65535
    i64.and
    i64.store offset=32
    local.get 4
    local.get 5
    i64.load offset=48
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=40
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=48
    local.get 4
    local.get 4
    i64.load offset=40
    i64.const 65535
    i64.and
    i64.store offset=40
    local.get 4
    local.get 5
    i64.load offset=56
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=48
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=56
    local.get 4
    local.get 4
    i64.load offset=48
    i64.const 65535
    i64.and
    i64.store offset=48
    local.get 4
    local.get 5
    i64.load offset=64
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=56
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=64
    local.get 4
    local.get 4
    i64.load offset=56
    i64.const 65535
    i64.and
    i64.store offset=56
    local.get 4
    local.get 5
    i64.load offset=72
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=64
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=72
    local.get 4
    local.get 4
    i64.load offset=64
    i64.const 65535
    i64.and
    i64.store offset=64
    local.get 4
    local.get 5
    i64.load offset=80
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=72
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=80
    local.get 4
    local.get 4
    i64.load offset=72
    i64.const 65535
    i64.and
    i64.store offset=72
    local.get 4
    local.get 5
    i64.load offset=88
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=80
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=88
    local.get 4
    local.get 4
    i64.load offset=80
    i64.const 65535
    i64.and
    i64.store offset=80
    local.get 4
    local.get 5
    i64.load offset=96
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=88
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=96
    local.get 4
    local.get 4
    i64.load offset=88
    i64.const 65535
    i64.and
    i64.store offset=88
    local.get 4
    local.get 5
    i64.load offset=104
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=96
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=104
    local.get 4
    local.get 4
    i64.load offset=96
    i64.const 65535
    i64.and
    i64.store offset=96
    local.get 4
    local.get 5
    i64.load offset=112
    i64.const 65535
    i64.sub
    local.get 4
    i64.load offset=104
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=112
    local.get 4
    local.get 4
    i64.load offset=104
    i64.const 65535
    i64.and
    i64.store offset=104
    local.get 4
    local.get 5
    i64.load offset=120
    i64.const 32767
    i64.sub
    local.get 4
    i64.load offset=112
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i64.sub
    i64.store offset=120
    local.get 4
    i64.load offset=120
    i64.const 16
    i64.shr_s
    i64.const 1
    i64.and
    i32.wrap_i64
    local.set 3
    local.get 4
    local.get 4
    i64.load offset=112
    i64.const 65535
    i64.and
    i64.store offset=112
    local.get 5
    local.get 4
    i32.const 1
    local.get 3
    i32.sub
    call 48
    local.get 0
    local.get 5
    i64.load
    i64.store16
    local.get 0
    local.get 5
    i64.load offset=8
    i64.store16 offset=2
    local.get 0
    local.get 5
    i64.load offset=16
    i64.store16 offset=4
    local.get 0
    local.get 5
    i64.load offset=24
    i64.store16 offset=6
    local.get 0
    local.get 5
    i64.load offset=32
    i64.store16 offset=8
    local.get 0
    local.get 5
    i64.load offset=40
    i64.store16 offset=10
    local.get 0
    local.get 5
    i64.load offset=48
    i64.store16 offset=12
    local.get 0
    local.get 5
    i64.load offset=56
    i64.store16 offset=14
    local.get 0
    local.get 5
    i64.load offset=64
    i64.store16 offset=16
    local.get 0
    local.get 5
    i64.load offset=72
    i64.store16 offset=18
    local.get 0
    local.get 5
    i64.load offset=80
    i64.store16 offset=20
    local.get 0
    local.get 5
    i64.load offset=88
    i64.store16 offset=22
    local.get 0
    local.get 5
    i64.load offset=96
    i64.store16 offset=24
    local.get 0
    local.get 5
    i64.load offset=104
    i64.store16 offset=26
    local.get 0
    local.get 5
    i64.load offset=112
    i64.store16 offset=28
    local.get 0
    local.get 5
    i64.load offset=120
    i64.store16 offset=30)
  (func (;48;) (type 4) (param i32 i32 i32)
    (local i64 i64)
    local.get 2
    i64.extend_i32_u
    i64.const 1
    i64.sub
    i64.const -1
    i64.xor
    local.set 4
    local.get 4
    local.get 0
    i64.load
    local.get 1
    i64.load
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load
    local.get 3
    i64.xor
    i64.store
    local.get 1
    local.get 1
    i64.load
    local.get 3
    i64.xor
    i64.store
    local.get 4
    local.get 0
    i64.load offset=8
    local.get 1
    i64.load offset=8
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=8
    local.get 3
    i64.xor
    i64.store offset=8
    local.get 1
    local.get 1
    i64.load offset=8
    local.get 3
    i64.xor
    i64.store offset=8
    local.get 4
    local.get 0
    i64.load offset=16
    local.get 1
    i64.load offset=16
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=16
    local.get 3
    i64.xor
    i64.store offset=16
    local.get 1
    local.get 1
    i64.load offset=16
    local.get 3
    i64.xor
    i64.store offset=16
    local.get 4
    local.get 0
    i64.load offset=24
    local.get 1
    i64.load offset=24
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=24
    local.get 3
    i64.xor
    i64.store offset=24
    local.get 1
    local.get 1
    i64.load offset=24
    local.get 3
    i64.xor
    i64.store offset=24
    local.get 4
    local.get 0
    i64.load offset=32
    local.get 1
    i64.load offset=32
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=32
    local.get 3
    i64.xor
    i64.store offset=32
    local.get 1
    local.get 1
    i64.load offset=32
    local.get 3
    i64.xor
    i64.store offset=32
    local.get 4
    local.get 0
    i64.load offset=40
    local.get 1
    i64.load offset=40
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=40
    local.get 3
    i64.xor
    i64.store offset=40
    local.get 1
    local.get 1
    i64.load offset=40
    local.get 3
    i64.xor
    i64.store offset=40
    local.get 4
    local.get 0
    i64.load offset=48
    local.get 1
    i64.load offset=48
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=48
    local.get 3
    i64.xor
    i64.store offset=48
    local.get 1
    local.get 1
    i64.load offset=48
    local.get 3
    i64.xor
    i64.store offset=48
    local.get 4
    local.get 0
    i64.load offset=56
    local.get 1
    i64.load offset=56
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=56
    local.get 3
    i64.xor
    i64.store offset=56
    local.get 1
    local.get 1
    i64.load offset=56
    local.get 3
    i64.xor
    i64.store offset=56
    local.get 4
    local.get 0
    i64.load offset=64
    local.get 1
    i64.load offset=64
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=64
    local.get 3
    i64.xor
    i64.store offset=64
    local.get 1
    local.get 1
    i64.load offset=64
    local.get 3
    i64.xor
    i64.store offset=64
    local.get 4
    local.get 0
    i64.load offset=72
    local.get 1
    i64.load offset=72
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=72
    local.get 3
    i64.xor
    i64.store offset=72
    local.get 1
    local.get 1
    i64.load offset=72
    local.get 3
    i64.xor
    i64.store offset=72
    local.get 4
    local.get 0
    i64.load offset=80
    local.get 1
    i64.load offset=80
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=80
    local.get 3
    i64.xor
    i64.store offset=80
    local.get 1
    local.get 1
    i64.load offset=80
    local.get 3
    i64.xor
    i64.store offset=80
    local.get 4
    local.get 0
    i64.load offset=88
    local.get 1
    i64.load offset=88
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=88
    local.get 3
    i64.xor
    i64.store offset=88
    local.get 1
    local.get 1
    i64.load offset=88
    local.get 3
    i64.xor
    i64.store offset=88
    local.get 4
    local.get 0
    i64.load offset=96
    local.get 1
    i64.load offset=96
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=96
    local.get 3
    i64.xor
    i64.store offset=96
    local.get 1
    local.get 1
    i64.load offset=96
    local.get 3
    i64.xor
    i64.store offset=96
    local.get 4
    local.get 0
    i64.load offset=104
    local.get 1
    i64.load offset=104
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=104
    local.get 3
    i64.xor
    i64.store offset=104
    local.get 1
    local.get 1
    i64.load offset=104
    local.get 3
    i64.xor
    i64.store offset=104
    local.get 4
    local.get 0
    i64.load offset=112
    local.get 1
    i64.load offset=112
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=112
    local.get 3
    i64.xor
    i64.store offset=112
    local.get 1
    local.get 1
    i64.load offset=112
    local.get 3
    i64.xor
    i64.store offset=112
    local.get 4
    local.get 0
    i64.load offset=120
    local.get 1
    i64.load offset=120
    i64.xor
    i64.and
    local.set 3
    local.get 0
    local.get 0
    i64.load offset=120
    local.get 3
    i64.xor
    i64.store offset=120
    local.get 1
    local.get 1
    i64.load offset=120
    local.get 3
    i64.xor
    i64.store offset=120)
  (func (;49;) (type 9) (param i32 i32)
    local.get 0
    local.get 1
    i64.load16_u
    i64.store
    local.get 0
    local.get 1
    i64.load16_u offset=2
    i64.store offset=8
    local.get 0
    local.get 1
    i64.load16_u offset=4
    i64.store offset=16
    local.get 0
    local.get 1
    i64.load16_u offset=6
    i64.store offset=24
    local.get 0
    local.get 1
    i64.load16_u offset=8
    i64.store offset=32
    local.get 0
    local.get 1
    i64.load16_u offset=10
    i64.store offset=40
    local.get 0
    local.get 1
    i64.load16_u offset=12
    i64.store offset=48
    local.get 0
    local.get 1
    i64.load16_u offset=14
    i64.store offset=56
    local.get 0
    local.get 1
    i64.load16_u offset=16
    i64.store offset=64
    local.get 0
    local.get 1
    i64.load16_u offset=18
    i64.store offset=72
    local.get 0
    local.get 1
    i64.load16_u offset=20
    i64.store offset=80
    local.get 0
    local.get 1
    i64.load16_u offset=22
    i64.store offset=88
    local.get 0
    local.get 1
    i64.load16_u offset=24
    i64.store offset=96
    local.get 0
    local.get 1
    i64.load16_u offset=26
    i64.store offset=104
    local.get 0
    local.get 1
    i64.load16_u offset=28
    i64.store offset=112
    local.get 0
    local.get 1
    i64.load16_u offset=30
    i64.const 32767
    i64.and
    i64.store offset=120)
  (func (;50;) (type 4) (param i32 i32 i32)
    local.get 0
    i32.load offset=36
    i32.const 16
    i32.lt_u
    if  ;; label = @1
      local.get 0
      local.get 1
      local.get 2
      call 28
    end)
  (func (;51;) (type 9) (param i32 i32)
    local.get 0
    i32.load offset=36
    i32.const 16
    i32.lt_u
    if  ;; label = @1
      local.get 0
      local.get 1
      call 26
    end)
  (global (;0;) i32 (i32.const 0))
  (global (;1;) i32 (i32.const 0))
  (global (;2;) i32 (i32.const 128))
  (global (;3;) i32 (i32.const 256))
  (global (;4;) i32 (i32.const 384))
  (global (;5;) i32 (i32.const 512))
  (global (;6;) i32 (i32.const 640))
  (global (;7;) i32 (i32.const 768))
  (global (;8;) i32 (i32.const 896))
  (global (;9;) i32 (i32.const 1024))
  (global (;10;) i32 (i32.const 1664))
  (global (;11;) i32 (i32.const 1920))
  (global (;12;) i32 (i32.const 1952))
  (global (;13;) i32 (i32.const 1968))
  (export "core_hsalsa20" (func 0))
  (export "core_salsa20" (func 1))
  (export "crypto_box" (func 2))
  (export "crypto_box_beforenm" (func 3))
  (export "crypto_box_open" (func 4))
  (export "crypto_hash" (func 5))
  (export "crypto_hashblocks" (func 6))
  (export "crypto_onetimeauth" (func 7))
  (export "crypto_onetimeauth_verify" (func 8))
  (export "crypto_scalarmult_base" (func 9))
  (export "crypto_scalarmult" (func 10))
  (export "crypto_secretbox" (func 11))
  (export "crypto_secretbox_open" (func 12))
  (export "crypto_sign" (func 13))
  (export "crypto_sign_keypair" (func 14))
  (export "crypto_sign_open" (func 15))
  (export "crypto_stream" (func 16))
  (export "crypto_stream_salsa20" (func 17))
  (export "crypto_stream_salsa20_xor" (func 18))
  (export "crypto_stream_xor" (func 19))
  (export "vn" (func 20))
  (export "crypto_verify_16" (func 21))
  (export "crypto_verify_32" (func 22))
  (export "globalsEnd" (global 13))
  (export "nacl_secretbox" (func 23))
  (export "nacl_secretbox_open" (func 24))
  (export "poly1305_blocks" (func 25))
  (export "poly1305_finish" (func 26))
  (export "poly1305_init" (func 27))
  (export "poly1305_update" (func 28))
  (export "add" (func 29))
  (export "cswap" (func 30))
  (export "modL" (func 31))
  (export "neq25519" (func 32))
  (export "pack" (func 33))
  (export "par25519" (func 34))
  (export "pow2523" (func 35))
  (export "reduce" (func 36))
  (export "scalarbase" (func 37))
  (export "scalarmult" (func 38))
  (export "set25519" (func 39))
  (export "unpackneg" (func 40))
  (export "A" (func 41))
  (export "M" (func 42))
  (export "S" (func 43))
  (export "Z" (func 44))
  (export "car25519" (func 45))
  (export "inv25519" (func 46))
  (export "pack25519" (func 47))
  (export "sel25519" (func 48))
  (export "unpack25519" (func 49))
  (export "wrap_poly1305_update" (func 50))
  (export "wrap_poly1305_finish" (func 51))
  (data (;0;) (i32.const 128) "\01")
  (data (;1;) (i32.const 256) "A\db\00\00\00\00\00\00\01")
  (data (;2;) (i32.const 384) "\a3x\00\00\00\00\00\00Y\13\00\00\00\00\00\00\caM\00\00\00\00\00\00\ebu\00\00\00\00\00\00\ab\d8\00\00\00\00\00\00AA\00\00\00\00\00\00M\0a\00\00\00\00\00\00p\00\00\00\00\00\00\00\98\e8\00\00\00\00\00\00yw\00\00\00\00\00\00y@\00\00\00\00\00\00\c7\8c\00\00\00\00\00\00s\fe\00\00\00\00\00\00o+\00\00\00\00\00\00\eel\00\00\00\00\00\00\03R")
  (data (;3;) (i32.const 512) "Y\f1\00\00\00\00\00\00\b2&\00\00\00\00\00\00\94\9b\00\00\00\00\00\00\d6\eb\00\00\00\00\00\00V\b1\00\00\00\00\00\00\83\82\00\00\00\00\00\00\9a\14\00\00\00\00\00\00\e0\00\00\00\00\00\00\000\d1\00\00\00\00\00\00\f3\ee\00\00\00\00\00\00\f2\80\00\00\00\00\00\00\8e\19\00\00\00\00\00\00\e7\fc\00\00\00\00\00\00\dfV\00\00\00\00\00\00\dc\d9\00\00\00\00\00\00\06$")
  (data (;4;) (i32.const 640) "\1a\d5\00\00\00\00\00\00%\8f\00\00\00\00\00\00`-\00\00\00\00\00\00V\c9\00\00\00\00\00\00\b2\a7\00\00\00\00\00\00%\95\00\00\00\00\00\00`\c7\00\00\00\00\00\00,i\00\00\00\00\00\00\5c\dc\00\00\00\00\00\00\d6\fd\00\00\00\00\00\001\e2\00\00\00\00\00\00\a4\c0\00\00\00\00\00\00\feS\00\00\00\00\00\00n\cd\00\00\00\00\00\00\d36\00\00\00\00\00\00i!")
  (data (;5;) (i32.const 768) "Xf\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff\00\00\00\00\00\00ff")
  (data (;6;) (i32.const 896) "\b0\a0\00\00\00\00\00\00\0eJ\00\00\00\00\00\00'\1b\00\00\00\00\00\00\ee\c4\00\00\00\00\00\00x\e4\00\00\00\00\00\00/\ad\00\00\00\00\00\00\06\18\00\00\00\00\00\00C/\00\00\00\00\00\00\a7\d7\00\00\00\00\00\00\fb=\00\00\00\00\00\00\99\00\00\00\00\00\00\00M+\00\00\00\00\00\00\0b\df\00\00\00\00\00\00\c1O\00\00\00\00\00\00\80$\00\00\00\00\00\00\83+")
  (data (;7;) (i32.const 1024) "\22\ae(\d7\98/\8aB\cde\ef#\91D7q/;M\ec\cf\fb\c0\b5\bc\db\89\81\a5\db\b5\e98\b5H\f3[\c2V9\19\d0\05\b6\f1\11\f1Y\9bO\19\af\a4\82?\92\18\81m\da\d5^\1c\abB\02\03\a3\98\aa\07\d8\beopE\01[\83\12\8c\b2\e4N\be\851$\e2\b4\ff\d5\c3}\0cUo\89{\f2t]\ber\b1\96\16;\fe\b1\de\805\12\c7%\a7\06\dc\9b\94&i\cft\f1\9b\c1\d2J\f1\9e\c1i\9b\e4\e3%O8\86G\be\ef\b5\d5\8c\8b\c6\9d\c1\0fe\9c\acw\cc\a1\0c$u\02+Yo,\e9-\83\e4\a6n\aa\84tJ\d4\fbA\bd\dc\a9\b0\5c\b5S\11\83\da\88\f9v\ab\dff\eeRQ>\98\102\b4-m\c61\a8?!\fb\98\c8'\03\b0\e4\0e\ef\be\c7\7fY\bf\c2\8f\a8=\f3\0b\e0\c6%\a7\0a\93G\91\a7\d5o\82\03\e0Qc\ca\06pn\0e\0ag))\14\fc/\d2F\85\0a\b7'&\c9&\5c8!\1b.\ed*\c4Z\fcm,M\df\b3\95\9d\13\0d8S\dec\af\8bTs\0ae\a8\b2w<\bb\0ajv\e6\ae\edG.\c9\c2\81;5\82\14\85,r\92d\03\f1L\a1\e8\bf\a2\010B\bcKf\1a\a8\91\97\f8\d0p\8bK\c20\beT\06\a3Ql\c7\18R\ef\d6\19\e8\92\d1\10\a9eU$\06\99\d6* qW\855\0e\f4\b8\d1\bb2p\a0j\10\c8\d0\d2\b8\16\c1\a4\19S\abAQ\08l7\1e\99\eb\8e\dfLwH'\a8H\9b\e1\b5\bc\b04cZ\c9\c5\b3\0c\1c9\cb\8aA\e3J\aa\d8Ns\e3cwO\ca\9c[\a3\b8\b2\d6\f3o.h\fc\b2\ef]\ee\82\8ft`/\17Coc\a5xr\ab\f0\a1\14x\c8\84\ec9d\1a\08\02\c7\8c(\1ec#\fa\ff\be\90\e9\bd\82\de\eblP\a4\15y\c6\b2\f7\a3\f9\be+Sr\e3\f2xq\c6\9ca&\ea\ce>'\ca\07\c2\c0!\c7\b8\86\d1\1e\eb\e0\cd\d6}\da\eax\d1n\ee\7fO}\f5\bao\17r\aag\f0\06\a6\98\c8\a2\c5}c\0a\ae\0d\f9\be\04\98?\11\1bG\1c\135\0bq\1b\84}\04#\f5w\db(\93$\c7@{\ab\ca2\bc\be\c9\15\0a\be\9e<L\0d\10\9c\c4g\1dC\b6B>\cb\be\d4\c5L*~e\fc\9c)\7fY\ec\fa\d6:\abo\cb_\17XGJ\8c\19Dl")
  (data (;8;) (i32.const 1664) "\ed\00\00\00\00\00\00\00\d3\00\00\00\00\00\00\00\f5\00\00\00\00\00\00\00\5c\00\00\00\00\00\00\00\1a\00\00\00\00\00\00\00c\00\00\00\00\00\00\00\12\00\00\00\00\00\00\00X\00\00\00\00\00\00\00\d6\00\00\00\00\00\00\00\9c\00\00\00\00\00\00\00\f7\00\00\00\00\00\00\00\a2\00\00\00\00\00\00\00\de\00\00\00\00\00\00\00\f9\00\00\00\00\00\00\00\de\00\00\00\00\00\00\00\14\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\10")
  (data (;9;) (i32.const 1920) "\09")
  (data (;10;) (i32.const 1952) "expand 32-byte k"))

;;(symb_exec "poly1305_init" (i32.sconst 2000) (i32.sconst 2080))
;;(symb_exec "poly1305_finish" (i32.sconst 2000) (i32.sconst 2112)) ;; loop invariant - for (int i=leftover..; i<16; i++)
;;(symb_exec "poly1305_blocks" (i32.sconst 2000) (i32.sconst 2128) (i32.sconst 32))
;;(symb_exec "poly1305_update" (i32.sconst 2000) (i32.sconst 2128) (i32.sconst 16)) ;; fails with invariant i = 0 is not explicit before loop
;;(symb_exec "poly1305_finish" (i32.sconst 2000) (i32.sconst 2112)) ;; loop invariant - for (int i=leftover..; i<16; i++)
;;;; mac, m, bytes, key, polyobject
(symb_exec "crypto_onetimeauth" (i32.sconst 2112) (i32.sconst 2128) (i32.sconst 16) (i32.sconst 2080) (i32.sconst 2000)) ;; loop invariant - for (int i=leftover..; i<16; i++)
