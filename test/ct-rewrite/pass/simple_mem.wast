(module
    (memory 1)
    (func (export "foo")
        (i32.store (i32.const 0) (i32.const 1))))

(rewrite)