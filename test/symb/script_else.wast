;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 23))
   (public $memory (i32.const 24) (i32.const 35))
   )
(register "env" $env)


;; int test_global (int i) {
;;     gl = i;
;;     return 0;
;; }


;; int test_else (int i, int n) {
;;     if (i < 4) {
;;         a[i] = n;
;; 	return a[i-1];
;;     }
;;     else {
;;         a[2*i-3] = n + i;
;; 	return test_global(i);
;;     }
;; }

;; Maybe add some result
(module
 (type (;0;) (func (param i32) (result i32)))
 (type (;1;) (func (param i32 i32) (result i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test_global (type 0) (param i32) (result i32)
    i32.const 0
    local.get 0
    i32.store offset=32
    i32.const 0)
  (func $test_else (type 1) (param i32 i32) (result i32)
    block  ;; label = @1
      local.get 0
      i32.const 3
      i32.gt_s
      br_if 0 (;@1;)
      local.get 0
      i32.const 2
      i32.shl
      local.tee 0
      i32.const 0
      i32.add
      local.get 1
      i32.store
      local.get 0
      i32.const -4
      i32.add
      i32.load
      return
    end
    local.get 0
    i32.const 3
    i32.shl
    i32.const 12
    i32.sub
    local.get 1
    local.get 0
    i32.add
    i32.store
    local.get 0
    call $test_global
    drop
    i32.const 0)
  (export "test_else" (func $test_else))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00")
  (data (;0;) (i32.const 32) "\00\00\00\00"))


(assert_failure (symb_exec "test_else" (i32.sconst l2) (i32.sconst h1)) "Trying to write high values in low memory")

(symb_exec "test_else" (i32.sconst 4) (i32.sconst h1)) 

(assert_failure (symb_exec "test_else" (i32.sconst 5) (i32.sconst h1)) "Trying to write high values in low memory")
