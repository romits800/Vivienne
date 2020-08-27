(module
  (import "env" "mem" (memory 1))
  (func $add (export "add") (param i32 i32) (result i32)
    (i32.add
      (i32.mul
        (local.get 1)
        (local.get 1))
      (local.get 0)))
  (func $add1 (export "add1") (param i32 i32) (result i32)
    (i32.add
      (select
        (local.get 1)
        (i32.const 5)
        (i32.gt_s
          (local.get 1)
          (i32.const 5)))
      (local.get 0)))
  (func $add2 (export "add2") (param i32 i32) (result i32)
    (i32.mul
      (local.get 1)
      (local.get 1)))
  (func $add3 (export "add3") (param i32 i32) (result i32)
    (select
      (local.get 1)
      (local.get 0)
      (i32.lt_s
        (local.get 1)
        (i32.const 5)))))
