open Source
open Types
open Values
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
(*
let export_desc (m: Ast.module_) (ex_name: Ast.name) : Ast.export_desc =
    let exp = List.find (fun exp -> exp.it.name = ex_name) m.it.exports in
    exp.it.edesc


type nested_instr = N of (Ast.instr * (nested_instr list))

let rec group (is: Ast.instr list): nested_instr * (Ast.instr list) = 
    let h, is' = match is with
    | [] -> rais (Failure "ugh")
    | h::is' -> h,is'
    in
    match h.it with
    | Drop ->
        let tbd, tl = group is' in
        let pre, tl = group tl in
        N (h, [pre; tbd]), tl
    |
    | _ -> N (h, []), is'

*)

let secify_memory (m: Ast.memory) =
    let MemoryType (l, _) = m.it.mtype in
    {m with it = {mtype = MemoryType (l, Secret)}}

let secify_value_type (vt: Types.value_type) =
    match vt with
    | I32Type | S32Type -> S32Type
    | I64Type | S64Type -> S64Type
    | _ -> raise (Failure "Attempted to secify a float")

let secify_const (i: Ast.instr) =
    let v = match i.it with
        | Const v -> v
        | _ -> raise (Failure "You called secify_const on an instruction that wasn't const... I mean seriously? It's in the name")
    in
    let it' = match v.it with
        | I32 x | S32 x -> S32 x
        | I64 x | S64 x -> S64 x
        | F32 x -> F32 x
        | F64 x -> F64 x
    in
    Const {v with it = it'}

let secify (i: Ast.instr) =
    let it' = match i.it with
        | Const v -> secify_const i
        | Load memop -> Load {memop with ty = secify_value_type memop.ty}
        | Store memop -> Store {memop with ty = secify_value_type memop.ty}
        | _ -> raise (Failure "Unsupported secify (probably needs to be added")
    in
    {i with it = it'}

type expectation = Pub | Any

type context = {
    out: Ast.func';
    lstack: expectation list;
}

let instr_str (i: Ast.instr) =
    Sexpr.to_string 80 (Arrange.instr i)

let instr_reducer (i: Ast.instr) (ctx: context) =
    let expected, lstack' = match ctx.lstack with
        | [] -> Any, ctx.lstack
        | e::ls -> e, ls
    in
    let maybe_secify = if expected = Pub then (fun x -> x) else secify in
    let i', lstack'' = match i.it with
        | Unreachable
        | Nop
        | Block (_, _)
        | Loop (_, _)
        | If (_, _, _)
        | Br _
        | BrIf _
        | BrTable (_, _)
        | Return
        | Call _
        | CallIndirect _
        | Drop
        | Select
        | SecretSelect
        | GetLocal _
        | SetLocal _
        | TeeLocal _
        | GetGlobal _
        | SetGlobal _
        | CurrentMemory
        | GrowMemory
        | Test _
        | Compare _
        | Unary _
        | Binary _
        | Convert _ -> raise (Failure ("ugh: " ^ instr_str i))
        | Store memop -> (maybe_secify i), Any::Pub::lstack'
        | Load memop -> (maybe_secify i), Pub::lstack'
        | Const _ -> maybe_secify i, lstack'
    in
    let out' = {ctx.out with body = i'::ctx.out.body} in
    {out = out'; lstack = lstack''}

let empty_ctx (f: Ast.func) =
    {
        out = {f.it with body = []};
        lstack = [Any];  (* Currently we allow the function to return any type *)
    }

let rewrite_func (f: Ast.func): Ast.func =
    let ctx = List.fold_right instr_reducer f.it.body (empty_ctx f) in
    {f with it=ctx.out}

(* produces a new module with the function rewritten *)
let rewrite (m: Ast.module_) =
    let m_it = m.it in
    let m_it' = {m_it with 
        funcs = List.map rewrite_func m_it.funcs;
        memories = List.map secify_memory m_it.memories;
    } in
    {m with it=m_it'}
