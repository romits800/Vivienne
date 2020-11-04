;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 39))
   (public $memory (i32.const 40) (i32.const 43))
   )
(register "env" $env)

;; int test11 (int n, int j, int h) {
;;     for (int i = 0; i<10; i++)
;;         a[i] = n+i;
;;     if (j>=0 && j < 3) {
;;         /*Always true: n+j+n+j+3 = 2*(n+j+1)+1*/
;;         if (a[j] + a[j+3]) {
;;             a[j+4] = h;
;;         }
;;     }
;;     return 0;
;; }
;; 
;; int test115 (int n, int j, int h) {
;;     for (int i = 0; i<10; i++)
;;         a[i] = n+i;
;;     if (j>=0 && j < 3) {
;;         if (a[j] + a[j+2]) {
;;             a[j+4] = h;
;;         }
;;     }
;;     return 0;
;; }

(module
  (type (;0;) (func (param i32 i32 i32) (result i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test11 (type 0) (param i32 i32 i32) (result i32)
    i32.const 0
    local.get 0
    i32.store
    i32.const 0
    local.get 0
    i32.const 9
    i32.add
    i32.store offset=36
    i32.const 0
    local.get 0
    i32.const 8
    i32.add
    i32.store offset=32
    i32.const 0
    local.get 0
    i32.const 7
    i32.add
    i32.store offset=28
    i32.const 0
    local.get 0
    i32.const 6
    i32.add
    i32.store offset=24
    i32.const 0
    local.get 0
    i32.const 5
    i32.add
    i32.store offset=20
    i32.const 0
    local.get 0
    i32.const 4
    i32.add
    i32.store offset=16
    i32.const 0
    local.get 0
    i32.const 3
    i32.add
    i32.store offset=12
    i32.const 0
    local.get 0
    i32.const 2
    i32.add
    i32.store offset=8
    i32.const 0
    local.get 0
    i32.const 1
    i32.add
    i32.store offset=4
    block  ;; label = @1
      local.get 1
      i32.const 2
      i32.gt_u
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
      local.get 1
      i32.const 2
      i32.shl
      i32.const 16
      i32.add
      local.get 2
      i32.store
    end
    i32.const 0)
  (func $test115 (type 0) (param i32 i32 i32) (result i32)
    i32.const 0
    local.get 0
    i32.store
    i32.const 0
    local.get 0
    i32.const 9
    i32.add
    i32.store offset=36
    i32.const 0
    local.get 0
    i32.const 8
    i32.add
    i32.store offset=32
    i32.const 0
    local.get 0
    i32.const 7
    i32.add
    i32.store offset=28
    i32.const 0
    local.get 0
    i32.const 6
    i32.add
    i32.store offset=24
    i32.const 0
    local.get 0
    i32.const 5
    i32.add
    i32.store offset=20
    i32.const 0
    local.get 0
    i32.const 4
    i32.add
    i32.store offset=16
    i32.const 0
    local.get 0
    i32.const 3
    i32.add
    i32.store offset=12
    i32.const 0
    local.get 0
    i32.const 2
    i32.add
    i32.store offset=8
    i32.const 0
    local.get 0
    i32.const 1
    i32.add
    i32.store offset=4
    block  ;; label = @1
      local.get 1
      i32.const 2
      i32.gt_u
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
      i32.const 8
      i32.add
      i32.load
      i32.sub
      i32.eq
      br_if 0 (;@1;)
      local.get 1
      i32.const 2
      i32.shl
      i32.const 16
      i32.add
      local.get 2
      i32.store
    end
    i32.const 0)
  (export "test11" (func $test11))
  (export "test115" (func $test115))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00"))

(symb_exec "test11" (i32.sconst h1) (i32.sconst l2) (i32.sconst l3))
(assert_failure (symb_exec "test115" (i32.sconst h1) (i32.sconst l2) (i32.sconst l3)) "BrIf: Constant-time failure")
