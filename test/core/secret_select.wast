(module
    (func (export "select_s32") (param s32 s32 s32) (result s32)
        (secret_select (get_local 0) (get_local 1) (get_local 2)))
    (func (export "select_s64") (param s64 s64 s32) (result s64)
        (secret_select (get_local 0) (get_local 1) (get_local 2))))

(assert_return (invoke "select_s32" (s32.const 1) (s32.const 2) (s32.const 1)) (s32.const 1))
(assert_return (invoke "select_s64" (s64.const 2) (s64.const 1) (s32.const 1)) (s64.const 2))

(assert_invalid
    (module (func (secret_select (i32.const 0) (i32.const 0) (s32.const 1))))
    "non-secret operands to secret_select")