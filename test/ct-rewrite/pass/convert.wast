
(module
    (memory 1)
    (func (export "foo")
        (i32.store
            (i32.wrap/i64 (i64.trunc_s/f64 (f64.const 1.3)))
            (i32.wrap/i64 (i64.trunc_s/f64 (f64.const 1.3))))))

(rewrite)