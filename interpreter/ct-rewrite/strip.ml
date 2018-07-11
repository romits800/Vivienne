open Ast
open Source
open Types
open Valid
open Values

module Int32Set = Set.Make(Int32) (* 1357 *)

let unsafe_types = ref (Int32Set.empty)

let secret_select_poly = ref false

let secret_select_poly_32 n =
  { ftype = n @@ no_region; locals = [];
    body = [
    Const ((I32Value.to_value Int32.zero) @@ no_region) @@ no_region;
    GetLocal(2l @@ no_region) @@ no_region;
    Test(I32 IntOp.Eqz) @@ no_region;
    Binary(I32 IntOp.Sub) @@ no_region;
    GetLocal(0l @@ no_region) @@ no_region;
    GetLocal(1l @@ no_region) @@ no_region;
    Binary(I32 IntOp.Xor) @@ no_region;
    Binary(I32 IntOp.And) @@ no_region;
    GetLocal(0l @@ no_region) @@ no_region;
    Binary(I32 IntOp.Xor) @@ no_region
]
  } @@ no_region

let secret_select_poly_64 n =
  { ftype = n @@ no_region; locals = [];
    body = [
    Const ((I64Value.to_value Int64.zero) @@ no_region) @@ no_region;
    GetLocal(2l @@ no_region) @@ no_region;
    Test(I32 IntOp.Eqz) @@ no_region;
    Convert(I64 IntOp.ExtendUI32) @@ no_region;
    Binary(I64 IntOp.Sub) @@ no_region;
    GetLocal(0l @@ no_region) @@ no_region;
    GetLocal(1l @@ no_region) @@ no_region;
    Binary(I64 IntOp.Xor) @@ no_region;
    Binary(I64 IntOp.And) @@ no_region;
    GetLocal(0l @@ no_region) @@ no_region;
    Binary(I64 IntOp.Xor) @@ no_region
]
  } @@ no_region

let secret_select_32_ind = ref Int32.zero

let secret_select_64_ind = ref Int32.zero

let register_unsafe_type ti = 
(*let _ = Printf.printf "unsafe type %ld" ti in*)
  (unsafe_types := (Int32Set.add ti (!unsafe_types)))

let unsafe_funcs = ref (Int32Set.empty)

let warn_if_unsafe_func is_import fi reg =
  if (Int32Set.mem fi !unsafe_funcs && !Flags.paranoid)
  then Printf.printf ("(paranoid) WARNING: %s a trusted function at %s\n") (if is_import then "importing" else "exporting") (string_of_region reg)
  else ()

let register_unsafe_func fi =
(*let _ = Printf.printf "unsafe func %ld" fi in*)
  (unsafe_funcs := (Int32Set.add fi (!unsafe_funcs)))

let register_unsafe_func_if_unsafe_type ti fi =
(*let _ = Printf.printf "testing func type %ld" ti in*)
  if (Int32Set.mem ti (!unsafe_types))
  then register_unsafe_func fi
  else ()

let weakened_memories = ref (Int32Set.empty)

let register_weakened_memory mi =
(*let _ = Printf.printf "weakened memory %ld" fi in*)
  (weakened_memories := (Int32Set.add mi (!weakened_memories)))

let warn_if_weakened_memory is_import mi reg =
  if (Int32Set.mem mi !weakened_memories && !Flags.paranoid)
  then Printf.printf ("(paranoid) WARNING: %s a secret memory at %s\n") (if is_import then "importing" else "exporting") (string_of_region reg)
  else ()

let leaked_tables = ref (Int32Set.empty)

let register_leaked_table ti =
(*let _ = Printf.printf "leaked table %ld" fi in*)
  (leaked_tables := (Int32Set.add ti (!leaked_tables)))

let weakened_globals = ref (Int32Set.empty)

let register_weakened_global gi =
(*let _ = Printf.printf "weakened global %ld" fi in*)
  (weakened_globals := (Int32Set.add gi (!weakened_globals)))

let register_global_if_weakened_and_mutable b m gi =
  if b then (match m with | Mutable -> register_weakened_global gi | _ -> () ) else ()

let warn_if_weakened_global is_import gi reg =
  if (Int32Set.mem gi !weakened_globals && !Flags.paranoid)
  then Printf.printf ("(paranoid) WARNING: %s a secret mutable global at %s\n") (if is_import then "importing" else "exporting") (string_of_region reg)
  else ()

let warn_if_unsafe_func_in_leaked_table ti fi reg =
  if (Int32Set.mem ti (!leaked_tables) && Int32Set.mem fi (!unsafe_funcs) && !Flags.paranoid)
  then Printf.printf "(paranoid) WARNING: leaking a trusted function via externalized table at %s\n" (string_of_region reg)
  else ()

let strip_value_type t =
  let (b,t') = (match t with | S32Type -> (true,I32Type) | S64Type -> (true,I64Type) | x -> (false,x)) in
  (b,t')

let strip_value_types ts = List.map (fun t -> snd (strip_value_type t)) ts

let strip_memop mop =
  let {ty; align; offset; sz} = mop in
  { ty = snd (strip_value_type ty); align = align; offset = offset; sz = sz}

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
        let _ = (match tr with | Trusted -> register_unsafe_type (Int32.of_int n) | _ -> ()) in
        FuncType(Trusted, strip_value_types ts, strip_value_types ts'))
in
  t' @@ t.at

let strip_types ts = List.mapi strip_type ts

let strip_global_type n gt =
  let gt' = (match gt with
             | GlobalType(t,m) -> let (b,t') = strip_value_type t in 
                                  let _ = register_global_if_weakened_and_mutable b m (Int32.of_int n) in
                                  GlobalType(t', m)) in
  gt'

let strip_global n g =
  let { gtype; value } = g.it in
  { gtype = strip_global_type n gtype; value = strip_const value } @@ g.at

let strip_globals gs off = List.mapi (fun n g -> strip_global (n+off) g) gs

let strip_tables ts = ts

let strip_memory_type n mt =
  let mt' = (match mt with
             | MemoryType(l,Secret) ->
               let _ = register_weakened_memory (Int32.of_int n) in
               MemoryType(l,Public)
             | MemoryType(l,Public) -> MemoryType(l,Public)) in
  mt'

let strip_memory n m =
  let { mtype } = m.it in
  { mtype = strip_memory_type n mtype } @@ m.at
  

let strip_memories ms off = List.mapi (fun n m -> strip_memory (n+off) m) ms

let rec my_check_instr (c : context) (e : instr) (s : infer_stack_type) =
  match e.it with
  | Block (ts, es) ->
    let stripped_es = my_check_block {c with labels = ts :: c.labels} es ts e.at in
    ([] --> ts, Block (strip_value_types ts, stripped_es) @@ e.at)

  | Loop (ts, es) ->
    let stripped_es = my_check_block {c with labels = [] :: c.labels} es ts e.at in
    ([] --> ts, Loop (strip_value_types ts, stripped_es) @@ e.at)

  | If (ts, es1, es2) ->
    let stripped_es1 = my_check_block {c with labels = ts :: c.labels} es1 ts e.at in
    let stripped_es2 = my_check_block {c with labels = ts :: c.labels} es2 ts e.at in
    ([I32Type] --> ts, If (strip_value_types ts, stripped_es1, stripped_es2) @@ e.at)

  | SecretSelect ->
    let t = peek 1 s in
    let out_t = [t; t; Some S32Type] -~> [t] in
    let _ = (secret_select_poly := true) in
    (match t with
     |  Some S32Type -> (out_t, Call(!secret_select_32_ind @@ e.at) @@ e.at)
     |  Some S64Type -> (out_t, Call(!secret_select_64_ind @@ e.at) @@ e.at)
     |  _ -> let _ = Printf.printf "WARNING: polymorphic secret_select in dead code at %s\n" (string_of_region e.at) in
             (out_t, Call(!secret_select_32_ind @@ e.at) @@ e.at))

  | _ ->  try (check_instr c e s, strip_instr e) with _ -> raise (Failure "Can't strip this ill-typed function.")

and my_check_seq (c : context) (es : instr list) =
  match es with
  | [] ->
    (stack [],[])

  | _ ->
    let es', e = Lib.List.split_last es in
    let (s,stripped_es') = my_check_seq c es' in
    let ({ins; outs},stripped_e) = my_check_instr c e s in
    (push outs (pop ins s e.at), stripped_es' @ [stripped_e])

and my_check_block (c : context) (es : instr list) (ts : stack_type) at =
  let (_,stripped_es) = my_check_seq c es in
  (* let s' = pop (stack ts) s at in *)
  stripped_es

let my_strip_func (c : context) n (f : func) =
  let {ftype; locals; body} = f.it in
  let _ = register_unsafe_func_if_unsafe_type ftype.it (Int32.of_int n) in
  let FuncType (tr, ins, out) = type_ c ftype in
  let c' = {c with trust = tr; locals = ins @ locals; results = out; labels = [out]} in
  let stripped_body = my_check_block c' body out f.at in
  { ftype = ftype; locals = strip_value_types locals; body = stripped_body } @@ f.at

let my_strip_funcs c fs off = List.mapi (fun n f -> my_strip_func c (n+off) f) fs

let strip_func n f =
  let { ftype; locals; body } = f.it in
  let _ = register_unsafe_func_if_unsafe_type ftype.it (Int32.of_int n) in
  { ftype = ftype; locals = strip_value_types locals; body = strip_instrs body } @@ f.at

let strip_funcs fs off = List.mapi (fun n f -> strip_func (n+off) f) fs

let strip_start s = s

let strip_segment s =
  let { index; offset; init} = s.it in
  { index = index ; offset = strip_const offset; init = init } @@ s.at

let elem_warnings reg ti fis =
  let _ = List.map (fun fi -> warn_if_unsafe_func_in_leaked_table ti.it fi.it reg) fis in
  fis

let strip_elem_segment s =
  let { index; offset; init} = s.it in
  { index = index ; offset = strip_const offset; init = elem_warnings s.at index init} @@ s.at

let strip_elems es = List.map strip_elem_segment es

let strip_data ds = List.map strip_segment ds

let strip_import_desc (fn,tn,mn,gn) idesc =
  let (fn',tn',mn',gn',idesc') =
    (match idesc.it with
     | MemoryImport(m) ->
       let m' = (strip_memory_type mn m) in
       let _ = warn_if_weakened_memory true (Int32.of_int mn) idesc.at in
       (fn,tn,mn+1,gn,MemoryImport(m'))
     | GlobalImport(g) ->
       let g' = (strip_global_type gn g) in
       let _ = warn_if_weakened_global true (Int32.of_int gn) idesc.at in
       (fn,tn,mn,gn+1,GlobalImport(g'))
     | FuncImport(ft) ->  
       let _ = (if (Int32Set.mem ft.it (!unsafe_types))
                  then register_unsafe_func (Int32.of_int fn)
                   else Printf.printf "WARNING: importing an untrusted function at %s\n" (string_of_region idesc.at))
       in (fn+1,tn,mn,gn,FuncImport(ft))
     | TableImport(tt) ->
       let _ = register_leaked_table (Int32.of_int tn) in (fn,tn+1,mn,gn,TableImport(tt))) in
  (fn',tn',mn',gn',idesc' @@ idesc.at)

let strip_import (fn,tn,mn,gn,ims) i =
  let { module_name; item_name; idesc } = i.it in
  let (fn',tn',mn',gn',idesc') = strip_import_desc (fn,tn,mn,gn) idesc in
  (fn',tn',mn',gn',ims @ [{ module_name = module_name; item_name = item_name; idesc = idesc' } @@ i.at])

let strip_imports is =
  let (fn,tn,mn,gn,ims) = List.fold_left strip_import (0,0,0,0,[]) is in (fn,tn,mn,gn,ims)

let strip_export_desc e =
  let e' =
    (match e.it with
     | FuncExport(fi) -> let _ = warn_if_unsafe_func false fi.it e.at in FuncExport(fi)
     | TableExport(ti) -> let _ = register_leaked_table ti.it in TableExport(ti)
     | MemoryExport(mi) -> let _ = warn_if_weakened_memory false mi.it e.at in MemoryExport(mi)
     | GlobalExport(gi) -> let _ = warn_if_weakened_global false gi.it e.at in GlobalExport(gi)) in
  e' @@ e.at

let strip_export e =
  let { name; edesc } = e.it in
  { name = name; edesc = strip_export_desc edesc } @@ e.at

let strip_exports es = List.map strip_export es

let num_funcs ims = List.fold_left (fun n im -> match im.it.idesc.it with | FuncImport(_) -> n+1 | _ -> n) 0 ims

let context_of_module (m : module_) = 
  let
    { types; imports; tables; memories; globals; funcs; start; elems; data;
      exports } = m.it
  in
  let c0 =
    List.fold_right check_import imports
      {empty_context with types = List.map (fun ty -> ty.it) types}
  in
  let c1 =
    { c0 with
      funcs = c0.funcs @ List.map (fun f -> type_ c0 f.it.ftype) funcs;
      tables = c0.tables @ List.map (fun tab -> tab.it.ttype) tables;
      memories = c0.memories @ List.map (fun mem -> mem.it.mtype) memories;
    }
  in
  { c1 with globals = c1.globals @ List.map (fun g -> g.it.gtype) globals }

let update_types_if_secret_poly types =
  if (!secret_select_poly)
  then types @ [FuncType(Trusted,[I32Type;I32Type;I32Type],[I32Type]) @@ no_region; FuncType(Trusted,[I64Type;I64Type;I32Type],[I64Type]) @@ no_region]
  else types

let update_funcs_if_secret_poly n funcs =
  if (!secret_select_poly)
  then funcs @ [secret_select_poly_32 n; secret_select_poly_64 (Int32.succ n)]
  else funcs

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
let c = context_of_module m in
let weak_types = strip_types types in
let (fn, tn, mn, gn, weak_imports) = strip_imports imports in
let _ = (secret_select_32_ind := Int32.of_int (fn + List.length funcs)) in
let _ = (secret_select_64_ind := Int32.succ (!secret_select_32_ind)) in
let weak_funcs = my_strip_funcs c funcs fn in
let weak_memories = strip_memories memories mn in
let weak_globals = strip_globals globals gn in
let weak_exports = strip_exports exports in
let weak_elems = strip_elems elems in
let weak_funcs = update_funcs_if_secret_poly (Int32.of_int (List.length weak_types)) weak_funcs in
let weak_types = update_types_if_secret_poly weak_types in

{
types = weak_types;
globals = weak_globals;
tables = strip_tables tables;
memories = weak_memories;
funcs = weak_funcs;
start = strip_start start;
elems = weak_elems;
data = strip_data data;
imports = weak_imports;
exports = weak_exports
} @@ m.at
