open Types
(* open Values                     (\*  *\) *)
open Svalues

type sglobal = {content : svalue; mut : mutability}
type t = sglobal

exception Type
exception NotMutable

let alloc (SglobalType (t, mut)) v =
  if type_of v <> t then raise Type;
  {content = v; mut = mut}

let type_of glob =
  SglobalType (type_of glob.content, glob.mut)

let load glob = glob.content
let store glob v =
  if glob.mut <> Mutable then raise NotMutable;
  if Svalues.type_of v <> Svalues.type_of glob.content then raise Type;
  (* if mutable: *)
  (* glob.content <- v *)
  {glob with content = v}
