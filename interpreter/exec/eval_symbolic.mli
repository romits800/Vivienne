open Svalues

exception TypeError of int * svalue * Stypes.svalue_type

val eval_unop : Ast.unop -> svalue -> svalue
val eval_binop : Ast.binop -> svalue -> svalue -> svalue
val eval_testop : Ast.testop -> svalue -> svalue
val eval_relop : Ast.relop -> svalue -> svalue -> svalue
val eval_cvtop : Ast.cvtop -> svalue -> svalue
