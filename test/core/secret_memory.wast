(module (memory 0 1 secret))
(module (memory 0 1 secret) (memory 0 0))
(module (memory 0 0) (memory 0 1 secret))

(assert_invalid (module (memory 0 1 secret) (memory 0 2 secret)) "multiple memories are not allowed (yet)")

(module
    (memory 1)
    (memory 1 secret)

    (func (export "sec_write/pub_read") (result i32)
        (i32.store (i32.const 0) (i32.const 1))
        (s32.store (i32.const 0) (s32.const 2))
        (return (i32.load (i32.const 0))))

    (func (export "pub_write/sec_read") (result s32)
        (s32.store (i32.const 0) (s32.const 1))
        (i32.store (i32.const 0) (i32.const 2))
        (return (s32.load (i32.const 0)))))

(assert_return (invoke "sec_write/pub_read") (i32.const 1))
(assert_return (invoke "pub_write/sec_read") (s32.const 1))