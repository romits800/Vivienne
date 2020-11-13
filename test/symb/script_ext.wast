;; This is a comment

(module $env 
   (memory  $memory (export "__linear_memory") 1)
   (secret $memory (i32.const 0) (i32.const 11))
   (public $memory (i32.const 12) (i32.const 35))
   )
(register "env" $env)


;; void test3 (int i, int n) {
;;     if (i < 3 && i> 0)
;;         a[i] = n;
;;     return;
;; }

(module
  (type (;0;) (func (param i32 i32)))
  (import "env" "__linear_memory" (memory (;0;) 1))
  (func $test3 (type 0) (param i32 i32)
	block  ;; label = @1
	nop
	local.get 0
	i64.extend_i32_s
	i64.const -1
	i64.add
	i64.const 1
	i64.gt_u
	br_if 0 (;@1;)
	local.get 0
	i32.const 2
	i32.shl
	i32.const 0
	i32.add
	local.get 1
	i32.store
	end)
  (export "test3" (func $test3))
  (data (;0;) (i32.const 0) "\01\00\00\00\02\00\00\00\03\00\00\00\04\00\00\00\05\00\00\00\06\00\00\00\07\00\00\00\08\00\00\00"))


;;(assert_failure (symb_exec "test3" (i32.sconst h1) (i32.sconst h2)) "BrIf: Constant-time failure")

;; Maybe add some result
(symb_exec "test3" (i32.sconst l1) (i32.sconst h2))
