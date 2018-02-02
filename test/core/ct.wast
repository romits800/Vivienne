(module
  (func (export "wrap/s64") (param $x s64) (result s32) (s32.wrap/s64 (get_local $x)))
  (func (export "classify/i32") (param $x i32) (result s32) (s32.classify/i32 (get_local $x)))
)

(assert_return (invoke "wrap/s64" (s64.const 1)) (s32.const 1))
(assert_return (invoke "classify/i32" (i32.const 1)) (s32.const 1))
(assert_invalid
  (module (func $if-s32 (if (s32.const 0) (then))))
  "type mismatch"
)

(assert_invalid
  (module (func $br-if-s32 (block $x (s32.const 0) (br_if $x))))
  "type mismatch"
)
