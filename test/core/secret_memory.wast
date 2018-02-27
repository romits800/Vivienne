(module (memory secret 0 1))
(module (memory secret 0 1) (memory 0 0))
(module (memory 0 0) (memory secret 0 1))

(assert_invalid (module (memory secret 0 1) (memory secret 0 2)) "multiple memories are not allowed (yet)")

(module
    (memory $pub 1)
    (memory $sec secret 1)

    (data $pub (i32.const 0) "A")

    (data $sec (i32.const 0) "B")

    (func (export "sec_init") (result s32)
        (return (s32.load (i32.const 0))))

    (func (export "pub_init") (result i32)
        (return (i32.load (i32.const 0))))

    (func (export "sec_write/pub_read") (result i32)
        (i32.store (i32.const 0) (i32.const 1))
        (s32.store (i32.const 0) (s32.const 2))
        (return (i32.load (i32.const 0))))

    (func (export "pub_write/sec_read") (result s32)
        (s32.store (i32.const 0) (s32.const 1))
        (i32.store (i32.const 0) (i32.const 2))
        (return (s32.load (i32.const 0)))))

(assert_return (invoke "sec_init") (s32.const 66))
(assert_return (invoke "pub_init") (i32.const 65))
(assert_return (invoke "sec_write/pub_read") (i32.const 1))
(assert_return (invoke "pub_write/sec_read") (s32.const 1))

(module
    (memory secret 0)

    (func (export "load_at_zero") (result s32) (s32.load (i32.const 0)))
    (func (export "store_at_zero") (s32.store (i32.const 0) (s32.const 2)))

    (func (export "load_at_page_size") (result s32) (s32.load (i32.const 0x10000)))
    (func (export "store_at_page_size") (s32.store (i32.const 0x10000) (s32.const 3)))

    (func (export "grow") (param $sz i32) (result i32) (grow_secret_memory (get_local $sz)))
    (func (export "size") (result i32) (current_secret_memory))
)

(assert_return (invoke "size") (i32.const 0))
(assert_trap (invoke "store_at_zero") "out of bounds memory access")
(assert_trap (invoke "load_at_zero") "out of bounds memory access")
(assert_trap (invoke "store_at_page_size") "out of bounds memory access")
(assert_trap (invoke "load_at_page_size") "out of bounds memory access")
(assert_return (invoke "grow" (i32.const 1)) (i32.const 0))
(assert_return (invoke "size") (i32.const 1))
(assert_return (invoke "load_at_zero") (s32.const 0))
(assert_return (invoke "store_at_zero"))
(assert_return (invoke "load_at_zero") (s32.const 2))
(assert_trap (invoke "store_at_page_size") "out of bounds memory access")
(assert_trap (invoke "load_at_page_size") "out of bounds memory access")
(assert_return (invoke "grow" (i32.const 4)) (i32.const 1))
(assert_return (invoke "size") (i32.const 5))
(assert_return (invoke "load_at_zero") (s32.const 2))
(assert_return (invoke "store_at_zero"))
(assert_return (invoke "load_at_zero") (s32.const 2))
(assert_return (invoke "load_at_page_size") (s32.const 0))
(assert_return (invoke "store_at_page_size"))
(assert_return (invoke "load_at_page_size") (s32.const 3))


(module
  (memory secret 0)
  (func (export "grow") (param i32) (result i32) (grow_secret_memory (get_local 0)))
)

(assert_return (invoke "grow" (i32.const 0)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 0)) (i32.const 1))
(assert_return (invoke "grow" (i32.const 2)) (i32.const 1))
(assert_return (invoke "grow" (i32.const 800)) (i32.const 3))
(assert_return (invoke "grow" (i32.const 0x10000)) (i32.const -1))

(module
  (memory secret 0 10)
  (func (export "grow") (param i32) (result i32) (grow_secret_memory (get_local 0)))
)

(assert_return (invoke "grow" (i32.const 0)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 1))
(assert_return (invoke "grow" (i32.const 2)) (i32.const 2))
(assert_return (invoke "grow" (i32.const 6)) (i32.const 4))
(assert_return (invoke "grow" (i32.const 0)) (i32.const 10))
(assert_return (invoke "grow" (i32.const 1)) (i32.const -1))
(assert_return (invoke "grow" (i32.const 0x10000)) (i32.const -1))
