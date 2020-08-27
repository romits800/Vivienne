(module
  (memory 1)
  (global (;0;) i32 (i32.const 32000))
  (func $add1 (export "add1") (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    (local.set 2
      (global.get 0))
    (local.set 3
      (i32.const 16))
    (local.set 4
      (i32.sub
        (local.get 2)
        (local.get 3)))
    (local.set 5
      (i32.const 5))
    (i32.store offset=8
      (local.get 4)
      (local.get 0))
    (i32.store offset=4
      (local.get 4)
      (local.get 1))
    (local.set 6
      (i32.load offset=4
        (local.get 4)))
    (local.set 7
      (local.get 6))
    (local.set 8
      (local.get 5))
    (local.set 9
      (i32.lt_s
        (local.get 7)
        (local.get 8)))
    (local.set 10
      (i32.const 1))
    (local.set 11
      (i32.and
        (local.get 9)
        (local.get 10)))
    (block  ;; label = @1
      (block  ;; label = @2
        (br_if 0 (;@2;)
          (i32.eqz
            (local.get 11)))
        (local.set 12
          (i32.load offset=8
            (local.get 4)))
        (local.set 13
          (i32.const 5))
        (local.set 14
          (i32.add
            (local.get 12)
            (local.get 13)))
        (i32.store offset=12
          (local.get 4)
          (local.get 14))
        (br 1 (;@1;)))
      (local.set 15
        (i32.load offset=8
          (local.get 4)))
      (local.set 16
        (i32.load offset=4
          (local.get 4)))
      (local.set 17
        (i32.add
          (local.get 15)
          (local.get 16)))
      (i32.store offset=12
        (local.get 4)
        (local.get 17)))
    (local.set 18
      (i32.load offset=12
        (local.get 4)))
    (return
      (local.get 18)))
)
