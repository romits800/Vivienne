(module
 (func untrusted)
 (func untrusted (param i32))
 (func (export "foo") untrusted (param i32)))

(assert_invalid
  (module
    (func $t)
    (func $u untrusted (call $t)))
  "trusted call in untrusted func"
)

(assert_invalid
  (module
    (type $trusted (func))
    (func $nop)
    (table anyfunc (elem $nop))
    (func untrusted
      (call_indirect (type $trusted))))
  "trusted call in untrusted func"
)

(assert_invalid
    (module
        (func untrusted (param s32) (result i32)
            (i32.declassify (get_local 0))))
    "declassify in untrusted func"
)

(module
    (func (export "declassify") (param s32) (result i32)
        (i32.declassify (get_local 0))))

(assert_return (invoke "declassify" (s32.const 65)) (i32.const 65))