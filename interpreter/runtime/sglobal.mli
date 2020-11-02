open Types
open Svalues

type sglobal
type t = sglobal

exception Type
exception NotMutable

val alloc : sglobal_type -> svalue -> sglobal  (* raises Type *)
val type_of : sglobal -> sglobal_type

val load : sglobal -> svalue
val store : sglobal -> svalue -> sglobal  (* raises Type, NotMutable *)
