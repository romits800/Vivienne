;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 7))
   (public $memory (i32.const 8) (i32.const 35))
   )
(register "env" $env)

;; int test9 (int n) {
;;    for (int i = 0; i<100; i++)
;;        a[i] = n;
;;    return 0;
;;}

(module
  (type (;0;) (func (param i32) (result i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test9 (type 0) (param i32) (result i32)
    (local i32)
    i32.const -400
    local.set 1
    loop  ;; label = @1
      local.get 1
      i32.const 400
      i32.add
      local.get 0
      i32.store
      local.get 1
      i32.const 4
      i32.add
      local.tee 1
      br_if 0 (;@1;)
    end
    i32.const 0)
  (export "test9" (func $test9))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00"))

;;(symb_exec "test9" (i32.sconst h1))
(assert_failure (symb_exec "test9" (i32.sconst h1)) "Trying to write high values in low memory")
