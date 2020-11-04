;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 399))
   (public $memory (i32.const 400) (i32.const 407))
   )
(register "env" $env)

;; int test10 (int n, int j, int h) {
;;     for (int i = 0; i<100; i++)
;;         a[i] = n+i;
;;     if (j>=0 && j < 3) {
;;         if (a[j] + a[j+3]) {
;;             a[j+4] = h;
;;         }
;;     }
;;     return 0;
;; }

(module
  (type (;0;) (func (param i32 i32 i32) (result i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test10 (type 0) (param i32 i32 i32) (result i32)
    (local i32)
    i32.const -400
    local.set 3
    loop  ;; label = @1
      local.get 3
      i32.const 400
      i32.add
      local.get 0
      i32.store
      local.get 0
      i32.const 1
      i32.add
      local.set 0
      local.get 3
      i32.const 4
      i32.add
      local.tee 3
      br_if 0 (;@1;)
    end
    block  ;; label = @1
      local.get 1
      i32.const 3
      i32.ge_u
      br_if 0 (;@1;)
      local.get 1
      i32.const 2
      i32.shl
      local.tee 0
      i32.const 0
      i32.add
      i32.load
      i32.const 0
      local.get 0
      i32.const 12
      i32.add
      i32.load
      i32.sub
      i32.eq
      br_if 0 (;@1;)
      local.get 0
      i32.const 16
      i32.add
      local.get 2
      i32.store
    end
    i32.const 0)
  (export "test10" (func $test10))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00"))


(symb_exec "test10" (i32.sconst h1) (i32.sconst l2) (i32.sconst l3))
