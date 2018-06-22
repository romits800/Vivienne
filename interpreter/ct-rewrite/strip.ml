open Ast
open Source
open Types
open Values

module Int32Set = Set.Make(Int32)

let weakened_types = ref (Int32Set.empty)

let register_weakened_type ti = 
(*let _ = Printf.printf "weakened type %ld" ti in*)
  (weakened_types := (Int32Set.add ti (!weakened_types)))

let weakened_funcs = ref (Int32Set.empty)

let register_weakened_func fi =
(*let _ = Printf.printf "weakened func %ld" fi in*)
  (weakened_funcs := (Int32Set.add fi (!weakened_funcs)))

let register_weakened_func_if_weakened_type ti fi =
(*let _ = Printf.printf "testing func type %ld" ti in*)
  if (Int32Set.mem ti (!weakened_types))
  then register_weakened_func fi
  else ()

let leaked_tables = ref (Int32Set.empty)

let register_leaked_table ti =
(*let _ = Printf.printf "leaked table %ld" fi in*)
  (leaked_tables := (Int32Set.add ti (!leaked_tables)))

let warn_if_weakened_func_in_leaked_table ti fi reg =
  if (Int32Set.mem ti (!leaked_tables) && Int32Set.mem fi (!weakened_funcs))
  then Printf.printf "WARNING: leaking a trusted function via exported table at %s\n" (string_of_region reg)
  else ()

let strip_value_type t =
  let t' = (match t with | S32Type -> I32Type | S64Type -> I64Type | x -> x) in
  t'

let strip_value_types ts = List.map strip_value_type ts

let strip_memop mop =
  let {ty; align; offset; sz} = mop in
  { ty = strip_value_type ty; align = align; offset = offset; sz = sz}

let strip_value v =
  match v with
  | S32(v) -> I32(v)
  | S64(v) -> I64(v)
  | x -> x

let strip_literal l = (strip_value l.it) @@l.at

let unsec_testop op =
  match op with
  | SecOp.Eqz -> IntOp.Eqz

let strip_testop op =
  match op with
  | S32(v) -> I32(unsec_testop v)
  | S64(v) -> I64(unsec_testop v)
  | x -> x

let unsec_relop op =
  match op with
  | SecOp.Eq -> IntOp.Eq
  | SecOp.Ne -> IntOp.Ne
  | SecOp.LtS -> IntOp.LtS
  | SecOp.LtU -> IntOp.LtU
  | SecOp.GtS -> IntOp.GtS
  | SecOp.GtU -> IntOp.GtU
  | SecOp.LeS -> IntOp.LeS
  | SecOp.LeU -> IntOp.LeU
  | SecOp.GeS -> IntOp.GeS
  | SecOp.GeU -> IntOp.GeU

let strip_relop op =
  match op with
  | S32(v) -> I32(unsec_relop v)
  | S64(v) -> I64(unsec_relop v)
  | x -> x

let unsec_unop op =
  match op with
  | SecOp.Clz -> IntOp.Clz
  | SecOp.Ctz -> IntOp.Ctz
  | SecOp.Popcnt -> IntOp.Popcnt

let strip_unop op =
  match op with
  | S32(v) -> I32(unsec_unop v)
  | S64(v) -> I64(unsec_unop v)
  | x -> x

let unsec_binop op =
  match op with
  | SecOp.Add -> IntOp.Add
  | SecOp.Sub -> IntOp.Sub
  | SecOp.Mul -> IntOp.Mul
  | SecOp.And -> IntOp.And
  | SecOp.Or  -> IntOp.Or
  | SecOp.Xor -> IntOp.Xor
  | SecOp.Shl -> IntOp.Shl
  | SecOp.ShrS -> IntOp.ShrS
  | SecOp.ShrU -> IntOp.ShrU
  | SecOp.Rotl -> IntOp.Rotl
  | SecOp.Rotr -> IntOp.Rotr

let strip_binop op =
  match op with
  | S32(v) -> I32(unsec_binop v)
  | S64(v) -> I64(unsec_binop v)
  | x -> x

let unsec_cvtop op =
  match op with
  | SecOp.WrapS64 -> IntOp.WrapI64
  | SecOp.ExtendUS32 -> IntOp.ExtendUI32
  | SecOp.ExtendSS32 -> IntOp.ExtendSI32
  | _ -> raise (Failure "Somehow unsec of classify")

let strip_cvtop op =
  match op with
  | I32(IntOp.Declassify) -> None
  | I64(IntOp.Declassify) -> None
  | S32(SecOp.Classify) -> None
  | S64(SecOp.Classify) -> None
  | S32(v) -> Some(I32(unsec_cvtop v))
  | S64(v) -> Some(I64(unsec_cvtop v))
  | x -> Some(x)

let rec strip_instr i =
  let i' =
  (match i.it with
  | Block(ts,is) -> Block(strip_value_types ts, strip_instrs is)
  | Loop(ts,is) -> Loop(strip_value_types ts, strip_instrs is)
  | If(ts,is,is') -> If(strip_value_types ts, strip_instrs is, strip_instrs is')
  | Load(lop) -> Load(strip_memop lop)
  | Store(sop) -> Store(strip_memop sop)
  | Const(l) -> Const(strip_literal l)
  | Test(top) -> Test(strip_testop top)
  | Compare(relop) -> Compare(strip_relop relop)
  | Unary(unop) -> Unary(strip_unop unop)
  | Binary(binop) -> Binary(strip_binop binop)
  | Convert(cvtop) -> Lib.Option.get (Lib.Option.map (fun x -> Convert(x)) (strip_cvtop cvtop)) Nop
  | CallIndirect(ti) ->
    let _ = Printf.printf "WARNING: call_indirect at %s\n" (string_of_region i.at) in CallIndirect(ti)
  | x -> x
  ) in i' @@ i.at

and strip_instrs is = List.map strip_instr is

let strip_const c = (strip_instrs c.it) @@ c.at

let strip_type n t =
  let t' =
    (match t.it with
     | FuncType(tr,ts,ts') -> 
				let _ = (match tr with | Trusted -> register_weakened_type (Int32.of_int n) | _ -> ()) in
				FuncType(Untrusted, strip_value_types ts, strip_value_types ts'))
in
  t' @@ t.at

let strip_types ts = List.mapi strip_type ts

let strip_global_type gt =
  let gt' = (match gt with | GlobalType(t,m) -> GlobalType(strip_value_type t, m)) in
  gt'

let strip_global g =
  let { gtype; value } = g.it in
  { gtype = strip_global_type gtype; value = strip_const value } @@ g.at

let strip_globals gs = List.map strip_global gs

let strip_tables ts = ts

let strip_memory_type mt =
  let mt' = (match mt with | MemoryType(l,sec) -> MemoryType(l,Public)) in
  mt'

let strip_memory m =
  let { mtype } = m.it in
  { mtype = strip_memory_type mtype } @@ m.at
  

let strip_memories ms = List.map strip_memory ms

let strip_func n f =
  let { ftype; locals; body } = f.it in
  let _ = register_weakened_func_if_weakened_type ftype.it (Int32.of_int n) in
  { ftype = ftype; locals = strip_value_types locals; body = strip_instrs body } @@ f.at

let strip_funcs fs = List.mapi strip_func fs

let strip_start s = s

let strip_segment s =
  let { index; offset; init} = s.it in
  { index = index ; offset = strip_const offset; init = init } @@ s.at

let elem_warnings reg ti fis =
  let _ = List.map (fun fi -> warn_if_weakened_func_in_leaked_table ti.it fi.it reg) fis in
  fis

let strip_elem_segment s =
  let { index; offset; init} = s.it in
  { index = index ; offset = strip_const offset; init = elem_warnings s.at index init} @@ s.at

let strip_elems es = List.map strip_elem_segment es

let strip_data ds = List.map strip_segment ds

let strip_import_desc idesc =
  let idesc' =
    (match idesc.it with
     | MemoryImport(m) -> MemoryImport(strip_memory_type m)
     | GlobalImport(g) -> GlobalImport(strip_global_type g)
     | x -> x) in
  idesc' @@ idesc.at

let strip_import i =
  let { module_name; item_name; idesc } = i.it in
  { module_name = module_name; item_name = item_name; idesc = strip_import_desc idesc } @@ i.at

let strip_imports is = List.map strip_import is

let strip_export_desc e =
  let e' =
    (match e.it with
     | FuncExport(fi) ->
       let _ = (if (Int32Set.mem fi.it (!weakened_funcs))
                then Printf.printf "WARNING: exporting a trusted function at %s\n" (string_of_region e.at)
                else ()) in FuncExport(fi)
     | TableExport(ti) ->
       let _ = register_leaked_table ti.it in TableExport(ti)
     | x -> x) in
  e' @@ e.at

let strip_export e =
  let { name; edesc } = e.it in
  { name = name; edesc = strip_export_desc edesc } @@ e.at

let strip_exports es = List.map strip_export es

let strip_module m = 
  let {
  types;
  globals;
  tables;
  memories;
  funcs;
  start;
  elems;
  data;
  imports;
  exports;
} = m.it in
let weak_types = strip_types types in
let weak_funcs = strip_funcs funcs in
let weak_exports = strip_exports exports in
let weak_elems = strip_elems elems in
{
types = weak_types;
globals = strip_globals globals;
tables = strip_tables tables;
memories = strip_memories memories;
funcs = weak_funcs;
start = strip_start start;
elems = weak_elems;
data = strip_data data;
imports = strip_imports imports;
exports = weak_exports
} @@ m.at
