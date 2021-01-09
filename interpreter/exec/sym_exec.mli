(* open Values *)
open Svalues
open Instance
open Pc_type

val init : Ast.module_ -> extern list -> module_inst (* raises Link, Trap *)
val invoke : func_inst -> svalue list -> pc_ext list (* raises Trap *)
val symb_invoke : func_inst -> svalue list -> pc_ext list (* raises Trap *)
