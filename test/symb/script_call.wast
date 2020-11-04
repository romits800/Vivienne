;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   ;; (secret $memory (i32.const 0) (i32.const 11))
   ;; (public $memory (i32.const 12) (i32.const 35))
   )
(register "env" $env)


;; int __attribute__((noinline)) test_callee (int i) {
;;   if (i>0) {
;;     a[i] = 5;
;;     return i;
;;   }
;;   else 
;;     return 0;
;; }
;; 
;; int test_caller (int i) {
;;    return test_callee(i);   
;; }



(module
  (type (;0;) (func (param i32) (result i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test_callee (type 0) (param i32) (result i32)
    block  ;; label = @1
      local.get 0
      i32.const 1
      i32.ge_s
      br_if 0 (;@1;)
      i32.const 0
      return
    end
    local.get 0
    i32.const 2
    i32.shl
    i32.const 0
    i32.add
    i32.const 5
    i32.store
    local.get 0)
  (func $test_caller (type 0) (param i32) (result i32)
    local.get 0
    call $test_callee)
  (export "test_callee" (func $test_callee))
  (export "test_caller" (func $test_caller))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00"))

(symb_exec "test_caller" (i32.sconst l1))
(assert_failure (symb_exec "test_callee" (i32.sconst h1)) "BrIf: Constant-time failure")
(assert_failure (symb_exec "test_caller" (i32.sconst h1)) "BrIf: Constant-time failure")
;;(assert_failure (symb_exec "test_caller" (i32.sconst h1)) "BrIf: Constant-time failure")
