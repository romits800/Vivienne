(module
    (memory 1)
    (func (export "foo")
        (i32.store
            (i32.add (i32.const 1) (i32.const 3))
            (i32.clz (i32.const 80)))))

(rewrite)
