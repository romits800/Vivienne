(module
    (memory 1)
    (func (export "foo")
        (i32.store
            (i32.eqz (i32.const 1))
            (i32.eqz (i32.const 2)))))

(rewrite)