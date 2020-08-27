open Types
open Symbvalues


type symbglobal = {mutable content : sstack; mut : mutability}
type t = symbglobal

(* exception Type *)
exception NotMutable

let alloc (SymbType (t, mut)) sv =
  (* if type_of v <> t then raise Type; *)
  {content = sv; mut = mut}

(* let type_of glob =
 *   SymbType (type_of glob.content, glob.mut) *)

let load glob = glob.content
let store glob sv =
  if glob.mut <> Mutable then raise NotMutable;
  (* if Values.type_of v <> Values.type_of glob.content then raise Type; *)
  glob.content <- sv
