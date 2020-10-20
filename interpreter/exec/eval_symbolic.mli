open Svalues

exception TypeError of int * svalue * Types.svalue_type

val eval_unop : Ast.unop -> svalue -> svalue
val eval_binop : Ast.binop -> svalue -> svalue -> svalue
val eval_testop : Ast.testop -> svalue -> svalue
val eval_relop : Ast.relop -> svalue -> svalue -> svalue
val eval_cvtop : Ast.cvtop -> svalue -> svalue
val eval_load : Types.value_type -> svalue -> int -> svalue
val eval_store : Types.value_type -> svalue -> svalue -> int -> svalue
val create_new_lstore : int -> svalue
val create_new_hstore : int -> svalue
