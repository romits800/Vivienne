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

let secify_testop op =
    match op with
    | I32 IntOp.Eqz -> S32 SecOp.Eqz
    | I64 IntOp.Eqz -> S64 SecOp.Eqz
    | _ -> op

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

let secify_relop op =
  match op with
    | I32 IntOp.Eq -> S32 SecOp.Eq
    | I32 IntOp.Ne -> S32 SecOp.Ne
    | I32 IntOp.LtS -> S32 SecOp.LtS
    | I32 IntOp.LtU -> S32 SecOp.LtU
    | I32 IntOp.GtS -> S32 SecOp.GtS
    | I32 IntOp.GtU -> S32 SecOp.GtU
    | I32 IntOp.LeS -> S32 SecOp.LeS
    | I32 IntOp.LeU -> S32 SecOp.LeU
    | I32 IntOp.GeS -> S32 SecOp.GeS
    | I32 IntOp.GeU -> S32 SecOp.GeU
    | I64 IntOp.Eq -> S64 SecOp.Eq
    | I64 IntOp.Ne -> S64 SecOp.Ne
    | I64 IntOp.LtS -> S64 SecOp.LtS
    | I64 IntOp.LtU -> S64 SecOp.LtU
    | I64 IntOp.GtS -> S64 SecOp.GtS
    | I64 IntOp.GtU -> S64 SecOp.GtU
    | I64 IntOp.LeS -> S64 SecOp.LeS
    | I64 IntOp.LeU -> S64 SecOp.LeU
    | I64 IntOp.GeS -> S64 SecOp.GeS
    | I64 IntOp.GeU -> S64 SecOp.GeU
    | _ -> op

let secify_cvtop op =
    match op with
        | S64 SecOp.Classify
        | S32 SecOp.Classify -> []
        | I64 IntOp.ExtendSI32 -> [S64 SecOp.ExtendSS32]
        | I64 IntOp.ExtendUI32 -> [S64 SecOp.ExtendUS32]
        | I32 IntOp.WrapI64 -> [S32 SecOp.WrapS64]
        | I32 x -> [I32 x; S32 SecOp.Classify]
        | I64 x -> [I64 x; S64 SecOp.Classify]
        | _ -> [op]



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
        | Select
        | SecretSelect -> [SecretSelect]

        | BrIf _
        | Br _
        | BrTable _
        | CallIndirect _
        | CurrentMemory
        | Return
        | Unreachable
        | Nop -> [i.it]

        | Convert cvtop -> List.map (fun x -> Convert x) (secify_cvtop cvtop)
        | Compare relop -> [Compare (secify_relop relop)]
        | Test testop -> [Test (secify_testop testop)]
        | Unary unop -> [Unary (secify_unop unop)]
        | Binary binop -> [Binary (secify_binop binop)]
        | Const v -> [secify_const i]
        | Load memop -> [Load {memop with ty = secify_value_type memop.ty}]
        | Store memop -> [Store {memop with ty = secify_value_type memop.ty}]
        | _ -> raise (Failure "Unsupported secify (probably needs to be added")
    in
    List.map (fun x -> x @@ Source.no_region) it'

type expectation = Pub | Any
let exp_str exp = match exp with
    | Pub -> "Pub"
    | Any -> "Any"

type context = {
    out: Ast.func';
    lstack: expectation list;
}

let instr_str (i: Ast.instr) =
    Sexpr.to_string 80 (Arrange.instr i)

let instr_reducer (i: Ast.instr) (ctx: context) =
    (* Printf.printf "%s -- %s\n" (instr_str i) (String.concat "::" (List.map exp_str ctx.lstack)); *)
    let expected, lstack' = match ctx.lstack with
        | [] -> Any, ctx.lstack
        | e::ls -> e, ls
    in
    let is' = if expected = Pub then [i] else secify i in
    (* Printf.printf " -- %s" (String.concat "::" (List.map instr_str is')); *)
    let lstack'' = match i.it with
        | Block (_, _)
        | Loop (_, _)
        | If (_, _, _)
        | Call _
        | GetLocal _
        | SetLocal _
        | TeeLocal _
        | GetGlobal _
        | SetGlobal _ -> raise (Failure ("ugh: " ^ instr_str i))

        | Convert cvtop -> (match cvtop with
            | S32 SecOp.Classify
            | S64 SecOp.Classify -> lstack'
            | I64 IntOp.ExtendSI32
            | I64 IntOp.ExtendUI32
            | I32 IntOp.WrapI64 -> expected::lstack'
            | _ -> Pub::lstack'
        )
        | Compare _ -> expected::expected::lstack'

        (* TODO: These should read their context *)
        | BrIf _ -> Pub::[]
        | Br _ -> []
        | BrTable (_, _) -> Pub::[]

        | CurrentMemory -> lstack'
        | CallIndirect _ -> Pub::lstack'
        | SecretSelect
        | Select -> expected::expected::expected::lstack'
        | Return -> Any::[] (*maybe revisit*)
        | Drop -> Any::expected::lstack'
        | Unreachable -> []
        | Nop -> lstack'
        | Test testop -> expected::lstack'
        | Unary unop -> expected::lstack'
        | GrowMemory -> Pub::lstack'
        | Binary binop -> expected::expected::lstack'
        | Store memop -> expected::Pub::lstack'
        | Load memop -> Pub::lstack'
        | Const _ -> lstack'
    in
    let out' = {ctx.out with body = is' @ ctx.out.body} in
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
