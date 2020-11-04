;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 39))
   (public $memory (i32.const 40) (i32.const 47))
   )
(register "env" $env)

;; int test13 (int n, int h) {
;;     a[0] = n;
;;     a[0] = h;
;;     if (a[0] == 0) {
;;         return 1;
;;     } 
;;     a[1] = 22;
;;     return 2;
;; }

(module
  (type (;0;) (func (param i32 i32) (result i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test13 (type 0) (param i32 i32) (result i32)
    i32.const 0
    local.get 0
    i32.store
    i32.const 0
    local.get 1
    i32.store
    block  ;; label = @1
      i32.const 0
      i32.load
      br_if 0 (;@1;)
      i32.const 1
      return
    end
    i32.const 0
    i32.const 22
    i32.store offset=4
    i32.const 2)
  (export "test13" (func $test13))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00"))

(symb_exec "test13" (i32.sconst l1) (i32.sconst l2))
(symb_exec "test13" (i32.sconst h1) (i32.sconst l2))
(assert_failure (symb_exec "test13" (i32.sconst l1) (i32.sconst h2)) "BrIf: Constant-time failure") 
