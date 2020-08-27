open Types

type symbglobal
type t = symbglobal

exception NotMutable

val alloc : symbglobal_type -> Symbvalues.sstack-> symbglobal  (* raises Type *)
(* val type_of : symbglobal -> global_type *)

val load : symbglobal -> Symbvalues.sstack
val store : symbglobal -> Symbvalues.sstack -> unit  (* raises Type, NotMutable *)
