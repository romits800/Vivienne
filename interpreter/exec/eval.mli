
(* open Values *)
open Svalues
open Instance
open Pc_type

exception Link of Source.region * string
exception Trap of Source.region * string
exception Crash of Source.region * string
exception Exhaustion of Source.region * string

val init : Ast.module_ -> extern list -> module_inst (* raises Link, Trap *)
val invoke : func_inst -> svalue list -> pc list (* raises Trap *)
val symb_invoke : func_inst -> svalue list -> (I32.t * I32.t) list -> pc list (* raises Trap *)
