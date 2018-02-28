(module
 (func trusted)
 (func trusted (param i32))
 (func (export "foo") trusted (param i32)))

(assert_invalid
  (module
    (func $t trusted)
    (func $u (call $t)))
  "trusted call in untrusted func"
)

(assert_invalid
  (module
    (type $trusted (func trusted))
    (func $nop)
    (table anyfunc (elem $nop))
    (func
      (call_indirect (type $trusted))))
  "trusted call in untrusted func"
)

(assert_invalid
    (module
        (func (param s32) (result i32)
            (i32.declassify (get_local 0))))
    "declassify in untrusted func"
)

(module
    (func (export "declassify") trusted (param s32) (result i32)
        (i32.declassify (get_local 0))))

(assert_return (invoke "declassify" (s32.const 65)) (i32.const 65))