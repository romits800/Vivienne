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

let secify_unop op =
    match op with
    | I32 IntOp.Clz -> S32 SecOp.Clz
    | I32 IntOp.Ctz -> S32 SecOp.Ctz
    | I32 IntOp.Popcnt -> S32 SecOp.Popcnt
    | I64 IntOp.Clz -> S64 SecOp.Clz
    | I64 IntOp.Ctz -> S64 SecOp.Ctz
    | I64 IntOp.Popcnt -> S64 SecOp.Popcnt
    | _ -> op

let secify_binop op =
    match op with
    | I32 IntOp.Add -> S32 SecOp.Add
    | I32 IntOp.Sub -> S32 SecOp.Sub
    | I32 IntOp.Mul -> S32 SecOp.Mul
    | I32 IntOp.And -> S32 SecOp.And
    | I32 IntOp.Or -> S32 SecOp.Or
    | I32 IntOp.Xor -> S32 SecOp.Xor
    | I32 IntOp.Shl -> S32 SecOp.Shl
    | I32 IntOp.ShrS -> S32 SecOp.ShrS
    | I32 IntOp.ShrU -> S32 SecOp.ShrU
    | I32 IntOp.Rotl -> S32 SecOp.Rotl
    | I32 IntOp.Rotr -> S32 SecOp.Rotr
    | I64 IntOp.Add -> S64 SecOp.Add
    | I64 IntOp.Sub -> S64 SecOp.Sub
    | I64 IntOp.Mul -> S64 SecOp.Mul
    | I64 IntOp.And -> S64 SecOp.And
    | I64 IntOp.Or -> S64 SecOp.Or
    | I64 IntOp.Xor -> S64 SecOp.Xor
    | I64 IntOp.Shl -> S64 SecOp.Shl
    | I64 IntOp.ShrS -> S64 SecOp.ShrS
    | I64 IntOp.ShrU -> S64 SecOp.ShrU
    | I64 IntOp.Rotl -> S64 SecOp.Rotl
    | I64 IntOp.Rotr -> S64 SecOp.Rotr
    | _ -> op

(*
let secify_op o =
    let op_map io =
        match io with
        |Clz | Ctz | Popcnt
        |Add | Sub | Mul | DivS | DivU | RemS | RemU
         And | Or | Xor | Shl | ShrS | ShrU | Rotl | Rotr
        | Eqz
        | Eq | Ne | LtS | LtU | GtS | GtU | LeS | LeU | GeS | GeU
    | ExtendSI32 | ExtendUI32 | WrapI64
             | TruncSF32 | TruncUF32 | TruncSF64 | TruncUF64
             | ReinterpretFloat | Declassify
    match o with
    | I32 IntOp.Add -> S32 SecOp.Sub
    | _ -> o
*)
let secify (i: Ast.instr) =
    let it' = match i.it with
        | Unary unop -> Unary (secify_unop unop)
        | Binary binop -> Binary (secify_binop binop)
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
    let i' = if expected = Pub then i else secify i in
    let lstack'' = match i.it with
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
        | Test _
        | Compare _
        | Convert _ -> raise (Failure ("ugh: " ^ instr_str i))
        | Unary unop -> expected::lstack'
        | GrowMemory -> Pub::lstack'
        | Binary binop -> expected::expected::lstack'
        | Store memop -> expected::Pub::lstack'
        | Load memop -> Pub::lstack'
        | Const _ -> lstack'
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
