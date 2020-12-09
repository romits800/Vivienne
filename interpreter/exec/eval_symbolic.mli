open Svalues

exception TypeError of int * svalue * Types.svalue_type

val eval_unop : Ast.unop -> svalue -> svalue
val eval_binop : Ast.binop -> svalue -> svalue -> svalue
val eval_testop : Ast.testop -> svalue -> svalue
val eval_relop : Ast.relop -> svalue -> svalue -> svalue
val eval_cvtop : Ast.cvtop -> svalue -> svalue
val eval_load : Types.value_type -> svalue -> int ->
                int -> Types.extension option -> svalue
val eval_store : Types.value_type -> svalue -> svalue -> int -> int -> svalue
val create_new_lstore : int -> int -> svalue
val create_new_value : int -> int -> int -> svalue
val create_new_hstore : int -> int -> svalue
val create_new_constant_store : int -> int -> int -> svalue
