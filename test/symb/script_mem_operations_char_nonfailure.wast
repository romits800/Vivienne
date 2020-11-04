;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 3))
   (public $memory (i32.const 4) (i32.const 8))
   )
(register "env" $env)


;; char test6(char i) {
;;     if (i > 3 && i<=8) {
;;         if (a[i] > 0)
;;             return a[i];
;;         else
;;             return a[i-1];
;;     }
;;     return 0;
;; }

(module
  (type (;0;) (func (param i32) (result i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test6 (type 0) (param i32) (result i32)
    (local i32)
    i32.const 0
    local.set 1
    block  ;; label = @1
      local.get 0
      i32.const -4
      i32.add
      i32.const 255
      i32.and
      i32.const 4
      i32.gt_u
      br_if 0 (;@1;)
      local.get 0
      i32.const 0
      i32.add
      i32.load8_s
      local.tee 1
      i32.const 0
      i32.gt_s
      br_if 0 (;@1;)
      local.get 0
      i32.const -1
      i32.add
      i32.load8_u
      local.set 1
    end
    local.get 1
    i32.const 24
    i32.shl
    i32.const 24
    i32.shr_s)
  (export "test6" (func $test6))
  (data (;0;) (i32.const 0) "\01\02\03\04\05\06\07\08"))


(assert_failure (symb_exec "test6" (i32.sconst l1)) "BrIf: Constant-time failure")

