;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 15))
   (public $memory (i32.const 16) (i32.const 35))
   )
(register "env" $env)

;; int test6 (int i) {
;;     if (i > 3 && i <= 8) {
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
      i32.const 4
      i32.gt_u
      br_if 0 (;@1;)
      local.get 0
      i32.const 2
      i32.shl
      local.tee 0
      i32.const 0
      i32.add
      i32.load
      local.tee 1
      i32.const 0
      i32.gt_s
      br_if 0 (;@1;)
      local.get 0
      i32.const -4
      i32.add
      i32.load
      local.set 1
    end
    local.get 1)
  (export "test6" (func $test6))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00"))


(symb_exec "test6" (i32.sconst l1))

