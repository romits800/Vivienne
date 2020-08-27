(module
  (type (;0;) (func (param i32 i32) (result i32)))
  (func $add (type 0) (param i32 i32) (result i32)
    (i32.add
      (i32.mul
        (local.get 1)
        (local.get 1))
      (local.get 0)))
  (func $add1 (type 0) (param i32 i32) (result i32)
    (block  ;; label = @1
      (br_if 0 (;@1;)
        (i32.gt_s
          (local.get 1)
          (i32.const 4)))
      (return
        (call $add
          (local.get 0)
          (i32.const 5))))
    (i32.add
      (local.get 1)
      (local.get 0)))
  (func $add2 (export "add2") (param i32 i32) (result i32)
        (local i32)
        (local.set 2
          (call $add
            (local.get 0)
            (local.get 1)))
    (i32.mul
      (local.get 2)
      (local.get 1)))
  (func $add3 (type 0) (param i32 i32) (result i32)
    (select
      (local.get 1)
      (local.get 0)
      (i32.lt_s
        (local.get 1)
        (i32.const 5)))))
