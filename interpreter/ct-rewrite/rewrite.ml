open Source
open Ast

let transform_phrase (ph: 'a Source.phrase) (f: 'a -> 'b) : ('b Source.phrase) =
    let it' = f ph.it in
    let ph' = it' @@ no_region in
    ph'

let ensure_type (m: Ast.module_) (ftyp: Types.func_type): (Ast.module_ * var) =
    let m' = transform_phrase m (fun m_it -> {m_it with types = m_it.types @ [(ftyp @@ no_region)] }) in
    let type_index = (List.length m'.it.types) - 1 in
    let t_var = (Int32.of_int type_index) @@ no_region in
    (m, t_var)

(* Transforms an export by name *)
let transform_export (m: Ast.module_) (ex_name: Ast.name) (f: Ast.export' -> Ast.export') : Ast.module_ =
    transform_phrase m (fun m_it ->
        { m_it with exports = List.map (fun exp ->
            if exp.it.name = ex_name then
                transform_phrase exp f
            else
                exp
        ) m_it.exports })

let replace_in_list (l: 'a list) (where_: int -> 'a -> bool) (by: 'a -> 'a): 'a list =
    List.mapi (fun i el ->
        if where_ i el
        then by el
        else el
    ) l
(*
(* Transforms an export by name *)
let transform_func (m: Ast.module_) (v: Ast.var) (f: Ast.func' -> Ast.func') : Ast.module_ =
    transform_phrase m (fun m_it ->
        { m_it with funcs = replace_in_list m_it.funcs
            (fun i _ -> i = )
            (fun func -> transform_phrase exp f)
        })
*)
let export_desc (m: Ast.module_) (ex_name: Ast.name) : Ast.export_desc =
    let exp = List.find (fun exp -> exp.it.name = ex_name) m.it.exports in
    exp.it.edesc


(* produces a new module with the function rewritten *)
let rewrite (m: Ast.module_) (ex_name: Ast.name) (ftyp: Types.func_type) =
    (*let m, t_var = ensure_type m ftyp in
    let ex_desc = export_desc m ex_name in

    (* we'll crash if the named export is not function *)
  (*)  let FuncExport v = ex_desc.it in *)
    m*)
    m
