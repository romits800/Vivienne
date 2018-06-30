open Checker
open Types
open Values
open Source

let ocaml_int_to_nat n = Checker.Arith.nat_of_integer (Big_int.big_int_of_int n)

let ocaml_int32_to_nat n = Checker.Arith.nat_of_integer (Big_int.big_int_of_string (I32.to_string_u n))

let var_to_nat n = ocaml_int32_to_nat (n.Source.it)

let string_of_nat n = Big_int.string_of_big_int (Checker.Arith.integer_of_nat n)

let ocaml_lookup category list x =
  try Lib.List32.nth list x.it with Failure _ ->
    failwith "ill-formed"
(*
let ocaml_func_type_of inst ftype = (ocaml_lookup "type" (!inst).module_.it.Ast.types ftype).it

let default_value = function
  | I32Type -> ConstInt32 I32Wrapper.zero
  | I64Type -> ConstInt64 I64Wrapper.zero
  | F32Type -> ConstFloat32 F32Wrapper.zero
  | F64Type -> ConstFloat64 F64Wrapper.zero
*)

let convert_t = function
  | I32Type -> Wasm_Ast.T_i32(Wasm_Ast.Public)
  | S32Type -> Wasm_Ast.T_i32(Wasm_Ast.Secret)
  | F32Type -> Wasm_Ast.T_f32
  | I64Type -> Wasm_Ast.T_i64(Wasm_Ast.Public)
  | S64Type -> Wasm_Ast.T_i64(Wasm_Ast.Secret)
  | F64Type -> Wasm_Ast.T_f64

let convert_tg = function
  | GlobalType (t, Immutable) -> Wasm_Ast.Tg_ext (Wasm_Ast.T_immut, (convert_t t), ())
  | GlobalType (t, Mutable) -> Wasm_Ast.Tg_ext (Wasm_Ast.T_mut, (convert_t t), ())


let convert_value = function
  | I32 c -> Wasm_Ast.ConstInt32 (Wasm_Ast.Public,c)
  | I64 c -> Wasm_Ast.ConstInt64 (Wasm_Ast.Public,c)
  | S32 c -> Wasm_Ast.ConstInt32 (Wasm_Ast.Secret,c)
  | S64 c -> Wasm_Ast.ConstInt64 (Wasm_Ast.Secret,c)
  | F32 c -> Wasm_Ast.ConstFloat32 c
  | F64 c -> Wasm_Ast.ConstFloat64 c
(*
let unconvert_value = function
  | ConstInt32 c -> I32 c
  | ConstInt64 c -> I64 c
  | ConstFloat32 c -> F32 c
  | ConstFloat64 c -> F64 c
*)
let convert_int_testop = function
  | Ast.IntOp.Eqz -> Wasm_Ast.Eqz

let convert_sint_testop = function
  | Ast.SecOp.Eqz -> Wasm_Ast.Eqz

let convert_testop = function
  | I32 op -> Wasm_Ast.Testop (Wasm_Ast.T_i32(Wasm_Ast.Public), convert_int_testop op)
  | I64 op -> Wasm_Ast.Testop (Wasm_Ast.T_i64(Wasm_Ast.Public), convert_int_testop op)
  | S32 op -> Wasm_Ast.Testop (Wasm_Ast.T_i32(Wasm_Ast.Secret), convert_sint_testop op)
  | S64 op -> Wasm_Ast.Testop (Wasm_Ast.T_i64(Wasm_Ast.Secret), convert_sint_testop op)
  | _  -> failwith "ill-formed"

let convert_int_compareop = function
  | Ast.IntOp.Eq -> Wasm_Ast.Eq
  | Ast.IntOp.Ne -> Wasm_Ast.Ne
  | Ast.IntOp.LtS -> Wasm_Ast.Lt Wasm_Ast.S
  | Ast.IntOp.LtU -> Wasm_Ast.Lt Wasm_Ast.U
  | Ast.IntOp.GtS -> Wasm_Ast.Gt Wasm_Ast.S
  | Ast.IntOp.GtU -> Wasm_Ast.Gt Wasm_Ast.U
  | Ast.IntOp.LeS -> Wasm_Ast.Le Wasm_Ast.S
  | Ast.IntOp.LeU -> Wasm_Ast.Le Wasm_Ast.U
  | Ast.IntOp.GeS -> Wasm_Ast.Ge Wasm_Ast.S
  | Ast.IntOp.GeU -> Wasm_Ast.Ge Wasm_Ast.U

let convert_sint_compareop = function
  | Ast.SecOp.Eq -> Wasm_Ast.Eq
  | Ast.SecOp.Ne -> Wasm_Ast.Ne
  | Ast.SecOp.LtS -> Wasm_Ast.Lt Wasm_Ast.S
  | Ast.SecOp.LtU -> Wasm_Ast.Lt Wasm_Ast.U
  | Ast.SecOp.GtS -> Wasm_Ast.Gt Wasm_Ast.S
  | Ast.SecOp.GtU -> Wasm_Ast.Gt Wasm_Ast.U
  | Ast.SecOp.LeS -> Wasm_Ast.Le Wasm_Ast.S
  | Ast.SecOp.LeU -> Wasm_Ast.Le Wasm_Ast.U
  | Ast.SecOp.GeS -> Wasm_Ast.Ge Wasm_Ast.S
  | Ast.SecOp.GeU -> Wasm_Ast.Ge Wasm_Ast.U

let convert_float_compareop = function
  | Ast.FloatOp.Eq -> Wasm_Ast.Eqf
  | Ast.FloatOp.Ne -> Wasm_Ast.Nef
  | Ast.FloatOp.Lt -> Wasm_Ast.Ltf
  | Ast.FloatOp.Gt -> Wasm_Ast.Gtf
  | Ast.FloatOp.Le -> Wasm_Ast.Lef
  | Ast.FloatOp.Ge -> Wasm_Ast.Gef

let convert_compareop = function
  | I32 op -> Wasm_Ast.Relop_i (Wasm_Ast.T_i32(Wasm_Ast.Public), convert_int_compareop op)
  | I64 op -> Wasm_Ast.Relop_i (Wasm_Ast.T_i64(Wasm_Ast.Public), convert_int_compareop op)
  | S32 op -> Wasm_Ast.Relop_i (Wasm_Ast.T_i32(Wasm_Ast.Secret), convert_sint_compareop op)
  | S64 op -> Wasm_Ast.Relop_i (Wasm_Ast.T_i64(Wasm_Ast.Secret), convert_sint_compareop op)
  | F32 op -> Wasm_Ast.Relop_f (Wasm_Ast.T_f32, convert_float_compareop op)
  | F64 op -> Wasm_Ast.Relop_f (Wasm_Ast.T_f64, convert_float_compareop op)

let convert_int_unop = function
  | Ast.IntOp.Clz -> Wasm_Ast.Clz
  | Ast.IntOp.Ctz -> Wasm_Ast.Ctz
  | Ast.IntOp.Popcnt -> Wasm_Ast.Popcnt

let convert_sint_unop = function
  | Ast.SecOp.Clz -> Wasm_Ast.Clz
  | Ast.SecOp.Ctz -> Wasm_Ast.Ctz
  | Ast.SecOp.Popcnt -> Wasm_Ast.Popcnt

let convert_float_unop = function
  | Ast.FloatOp.Neg -> Wasm_Ast.Neg
  | Ast.FloatOp.Abs -> Wasm_Ast.Abs
  | Ast.FloatOp.Ceil -> Wasm_Ast.Ceil
  | Ast.FloatOp.Floor -> Wasm_Ast.Floor
  | Ast.FloatOp.Trunc -> Wasm_Ast.Trunc
  | Ast.FloatOp.Nearest -> Wasm_Ast.Nearest
  | Ast.FloatOp.Sqrt -> Wasm_Ast.Sqrt

let convert_unop = function
  | I32 op -> Wasm_Ast.Unop_i (Wasm_Ast.T_i32(Wasm_Ast.Public), convert_int_unop op)
  | I64 op -> Wasm_Ast.Unop_i (Wasm_Ast.T_i64(Wasm_Ast.Public), convert_int_unop op)
  | S32 op -> Wasm_Ast.Unop_i (Wasm_Ast.T_i32(Wasm_Ast.Secret), convert_sint_unop op)
  | S64 op -> Wasm_Ast.Unop_i (Wasm_Ast.T_i64(Wasm_Ast.Secret), convert_sint_unop op)
  | F32 op -> Wasm_Ast.Unop_f (Wasm_Ast.T_f32, convert_float_unop op)
  | F64 op  -> Wasm_Ast.Unop_f (Wasm_Ast.T_f64, convert_float_unop op)

let convert_int_binop = function
  | Ast.IntOp.Add -> Wasm_Ast.Add
  | Ast.IntOp.Sub -> Wasm_Ast.Sub
  | Ast.IntOp.Mul -> Wasm_Ast.Mul
  | Ast.IntOp.DivS -> Wasm_Ast.Div Wasm_Ast.S
  | Ast.IntOp.DivU -> Wasm_Ast.Div Wasm_Ast.U
  | Ast.IntOp.RemS -> Wasm_Ast.Rem Wasm_Ast.S
  | Ast.IntOp.RemU -> Wasm_Ast.Rem Wasm_Ast.U
  | Ast.IntOp.And -> Wasm_Ast.And
  | Ast.IntOp.Or -> Wasm_Ast.Or
  | Ast.IntOp.Xor -> Wasm_Ast.Xor
  | Ast.IntOp.Shl -> Wasm_Ast.Shl
  | Ast.IntOp.ShrS -> Wasm_Ast.Shr Wasm_Ast.S
  | Ast.IntOp.ShrU -> Wasm_Ast.Shr Wasm_Ast.U
  | Ast.IntOp.Rotl -> Wasm_Ast.Rotl
  | Ast.IntOp.Rotr -> Wasm_Ast.Rotr

let convert_sint_binop = function
  | Ast.SecOp.Add -> Wasm_Ast.Add
  | Ast.SecOp.Sub -> Wasm_Ast.Sub
  | Ast.SecOp.Mul -> Wasm_Ast.Mul
  | Ast.SecOp.And -> Wasm_Ast.And
  | Ast.SecOp.Or -> Wasm_Ast.Or
  | Ast.SecOp.Xor -> Wasm_Ast.Xor
  | Ast.SecOp.Shl -> Wasm_Ast.Shl
  | Ast.SecOp.ShrS -> Wasm_Ast.Shr Wasm_Ast.S
  | Ast.SecOp.ShrU -> Wasm_Ast.Shr Wasm_Ast.U
  | Ast.SecOp.Rotl -> Wasm_Ast.Rotl
  | Ast.SecOp.Rotr -> Wasm_Ast.Rotr

let convert_float_binop = function
  | Ast.FloatOp.Add -> Wasm_Ast.Addf
  | Ast.FloatOp.Sub -> Wasm_Ast.Subf
  | Ast.FloatOp.Mul -> Wasm_Ast.Mulf
  | Ast.FloatOp.Div -> Wasm_Ast.Divf
  | Ast.FloatOp.Min -> Wasm_Ast.Min
  | Ast.FloatOp.Max -> Wasm_Ast.Max
  | Ast.FloatOp.CopySign -> Wasm_Ast.Copysign

let convert_binop = function
  | I32 op -> Wasm_Ast.Binop_i (Wasm_Ast.T_i32(Wasm_Ast.Public), convert_int_binop op)
  | I64 op -> Wasm_Ast.Binop_i (Wasm_Ast.T_i64(Wasm_Ast.Public), convert_int_binop op)
  | S32 op -> Wasm_Ast.Binop_i (Wasm_Ast.T_i32(Wasm_Ast.Secret), convert_sint_binop op)
  | S64 op -> Wasm_Ast.Binop_i (Wasm_Ast.T_i64(Wasm_Ast.Secret), convert_sint_binop op)
  | F32 op -> Wasm_Ast.Binop_f (Wasm_Ast.T_f32, convert_float_binop op)
  | F64 op  -> Wasm_Ast.Binop_f (Wasm_Ast.T_f64, convert_float_binop op)

let t_reinterpret = function
  | Wasm_Ast.T_i32 _ -> Wasm_Ast.T_f32
  | Wasm_Ast.T_i64 _ -> Wasm_Ast.T_f64
  | Wasm_Ast.T_f32 -> Wasm_Ast.T_i32(Wasm_Ast.Public)
  | Wasm_Ast.T_f64 -> Wasm_Ast.T_i64(Wasm_Ast.Public)

let convert_int_convertop t1 = function
  | Ast.IntOp.ExtendSI32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i32(Wasm_Ast.Public),Some Wasm_Ast.S)
  | Ast.IntOp.ExtendUI32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i32(Wasm_Ast.Public), Some Wasm_Ast.U)
  | Ast.IntOp.WrapI64 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i64(Wasm_Ast.Public), None)
  | Ast.IntOp.TruncSF32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_f32, Some Wasm_Ast.S)
  | Ast.IntOp.TruncUF32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_f32, Some Wasm_Ast.U)
  | Ast.IntOp.TruncSF64 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_f64, Some Wasm_Ast.S)
  | Ast.IntOp.TruncUF64 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_f64, Some Wasm_Ast.U)
  | Ast.IntOp.ReinterpretFloat -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Reinterpret, t_reinterpret t1, None)
  | Ast.IntOp.Declassify -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Declassify, Wasm_Base_Defs.classify_t t1, None)

let convert_sint_convertop t1 = function
  | Ast.SecOp.ExtendSS32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i32(Wasm_Ast.Secret),Some Wasm_Ast.S)
  | Ast.SecOp.ExtendUS32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i32(Wasm_Ast.Secret), Some Wasm_Ast.U)
  | Ast.SecOp.WrapS64 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i64(Wasm_Ast.Secret), None)
  | Ast.SecOp.Classify -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Classify, Wasm_Base_Defs.declassify_t t1, None)

let convert_float_convertop t1 = function
  | Ast.FloatOp.ConvertSI32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i32(Wasm_Ast.Public), Some Wasm_Ast.S)
  | Ast.FloatOp.ConvertUI32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i32(Wasm_Ast.Public), Some Wasm_Ast.U)
  | Ast.FloatOp.ConvertSI64 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i64(Wasm_Ast.Public), Some Wasm_Ast.S)
  | Ast.FloatOp.ConvertUI64 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_i64(Wasm_Ast.Public), Some Wasm_Ast.U)
  | Ast.FloatOp.PromoteF32 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_f32, None)
  | Ast.FloatOp.DemoteF64 -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, Wasm_Ast.T_f64, None)
  | Ast.FloatOp.ReinterpretInt -> Wasm_Ast.Cvtop (t1, Wasm_Ast.Reinterpret, t_reinterpret t1, None)

let convert_convertop = function
  | I32 op -> convert_int_convertop (Wasm_Ast.T_i32(Wasm_Ast.Public)) op
  | I64 op -> convert_int_convertop (Wasm_Ast.T_i64(Wasm_Ast.Public)) op
  | S32 op -> convert_sint_convertop (Wasm_Ast.T_i32(Wasm_Ast.Secret)) op
  | S64 op -> convert_sint_convertop (Wasm_Ast.T_i64(Wasm_Ast.Secret)) op
  | F32 op -> convert_float_convertop Wasm_Ast.T_f32 op
  | F64 op  -> convert_float_convertop Wasm_Ast.T_f64 op
(*
let convert_glob g = Wasm_Ast.Global_ext (Wasm_Ast.T_mut, convert_value (!g), ())
*)
let convert_vltype vl_type = List.map convert_t vl_type

let convert_sec = function
  | Secret -> Wasm_Ast.Secret
  | Public -> Wasm_Ast.Public

let convert_trust = function
  | Trusted -> Wasm_Ast.Trusted
  | Untrusted -> Wasm_Ast.Untrusted

let convert_ftype = function
  | FuncType (trust, stype1, stype2) -> (convert_trust trust, Wasm_Ast.Tf (convert_vltype stype1, convert_vltype stype2))
(*
let rec list_to_ne_list ns n =
  match ns with
  | [] -> Base (var_to_nat n)
  | n'::ns' -> Conz (var_to_nat n', list_to_ne_list ns' n)
*)
let convert_tp = function
  | Memory.Mem8 -> Wasm_Ast.Tp_i8
  | Memory.Mem16 -> Wasm_Ast.Tp_i16
  | Memory.Mem32 -> Wasm_Ast.Tp_i32

let convert_sx = function
  | Memory.SX -> Wasm_Ast.S
  | Memory.ZX -> Wasm_Ast.U

let convert_load_tp_sx = function
  | None -> None
  | Some (mtp, msx) -> Some (convert_tp mtp, convert_sx msx)

let convert_store_tp = function
  | None -> None
  | Some mtp -> Some (convert_tp mtp)

let rec convert_instr instr =
  match instr.it with
  | Ast.Unreachable -> Wasm_Ast.Unreachable
  | Ast.Nop -> Wasm_Ast.Nop
  | Ast.Block (st, binstrs) -> Wasm_Ast.Block (Wasm_Ast.Tf ([],convert_vltype st), convert_instrs binstrs)
  | Ast.Loop (st, binstrs) -> Wasm_Ast.Loop (Wasm_Ast.Tf ([],convert_vltype st), convert_instrs binstrs)
  | Ast.If (st, binstrs1, binstrs2) -> Wasm_Ast.If (Wasm_Ast.Tf ([],convert_vltype st), convert_instrs binstrs1, convert_instrs binstrs2)
  | Ast.Br n -> Wasm_Ast.Br (var_to_nat n)
   | Ast.BrIf n -> Wasm_Ast.Br_if (var_to_nat n)
  | Ast.BrTable (ns, n) -> Wasm_Ast.Br_table (List.map var_to_nat ns, var_to_nat n)
  | Ast.Return -> Wasm_Ast.Return
  | Ast.Call n -> Wasm_Ast.Call (var_to_nat n)
  | Ast.CallIndirect n -> Wasm_Ast.Call_indirect (var_to_nat n)
  | Ast.Drop -> Wasm_Ast.Drop
  | Ast.Select -> Wasm_Ast.Select (Wasm_Ast.Public)
  | Ast.SecretSelect -> Wasm_Ast.Select (Wasm_Ast.Secret)
  | Ast.GetLocal n -> Wasm_Ast.Get_local (var_to_nat n)
  | Ast.SetLocal n -> Wasm_Ast.Set_local (var_to_nat n)
  | Ast.TeeLocal n -> Wasm_Ast.Tee_local (var_to_nat n)
  | Ast.GetGlobal n -> Wasm_Ast.Get_global (var_to_nat n)
  | Ast.SetGlobal n -> Wasm_Ast.Set_global (var_to_nat n)
  | Ast.Load lop -> let {Ast.ty; Ast.align; Ast.offset; Ast.sz} = lop in
                    Wasm_Ast.Load ((convert_t ty), convert_load_tp_sx sz, (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))
  | Ast.Store sop -> let {Ast.ty; Ast.align; Ast.offset; Ast.sz} = sop in
                     Wasm_Ast.Store ((convert_t ty), convert_store_tp sz, (ocaml_int_to_nat align), (ocaml_int32_to_nat offset))
  | Ast.CurrentMemory -> Wasm_Ast.Current_memory
  | Ast.GrowMemory -> Wasm_Ast.Grow_memory
  | Ast.Const v -> Wasm_Ast.EConst (convert_value v.it)
  | Ast.Test top -> convert_testop top
  | Ast.Compare cop -> convert_compareop cop
  | Ast.Unary uop -> convert_unop uop
  | Ast.Binary bop -> convert_binop bop
  | Ast.Convert cop -> convert_convertop cop
and convert_instrs instrs = List.map convert_instr instrs
(*
let rec get_table' t n =
  if (n = 0l)
  then []
  else
    match Table.load t (Int32.sub (Table.size t) n) with
    | Func f -> Some f :: get_table' t (Int32.sub n 1l)
    | _ -> None :: get_table' t (Int32.sub n 1l)

let get_table t = get_table' t (Table.size t)

let memrq s ss = List.exists (fun s' -> !s == !s') ss

let index_some ss s =
  match Lib.List.index_where (fun s' -> !s == !s') ss with
  | None -> failwith "error in gather procedure"
  | Some n -> n

let rec collect_instances_cl (ss : (instance ref) list) (cl :closure) : ((instance ref) list) =
  match cl with
  | AstFunc (s, func) -> collect_instances_instance ss s
  | HostFunc (_, _) -> ss
and collect_instances_funcs (ss : (instance ref) list) (funcs : closure list) : ((instance ref) list) =
  List.fold_left collect_instances_cl ss funcs
and collect_instances_table (ss : (instance ref) list) (table: Table.t) : ((instance ref) list) =
  List.fold_left (fun ss t -> Lib.Option.get (Lib.Option.map (collect_instances_cl ss) t) ss) ss (get_table table)
and collect_instances_tables (ss : (instance ref) list) (tables: Table.t list) : ((instance ref) list) =
  List.fold_left collect_instances_table ss tables
and collect_instances_instance (ss : (instance ref) list) (s : instance ref) : ((instance ref) list) =
  if (memrq s ss) then ss else
  let ss' = ss @ [s] in
  let { module_; funcs; tables; memories; globals; exports} = !s in
  let ss'' = collect_instances_funcs ss' funcs in
  let ss''' = collect_instances_tables ss'' tables in
  ss'''

let collect_globals_instance (gs : global list) (s : (instance ref)) : (global list) =
  List.fold_left (fun gs g -> if memrq g gs then gs else gs @ [g]) gs ((!s).globals)

let collect_globals (ss : (instance ref) list) : (global list) =
 List.fold_left collect_globals_instance [] ss

let convert_func (ss : (instance ref) list) (s : instance ref) (f : Ast.func) =
  let { Ast.ftype; Ast.locals; Ast.body; } = f.it in
  let n = index_some ss s in
  (n, convert_ftype (ocaml_func_type_of s ftype), convert_vltype locals, convert_instrs body)

let convert_cl (ss : (instance ref) list) = function
  | AstFunc (s, func) -> let (inst, ftype, vltype, instrs) = (convert_func ss s func) in
                            Func_native (ocaml_int_to_nat inst, ftype, vltype, instrs)
  | HostFunc (f_type, f) -> Func_host (convert_ftype f_type, f)

let convert_cls (ss : (instance ref) list) cls = List.map (convert_cl ss) cls

let convert_table (ss : (instance ref) list) t = List.map (Lib.Option.map (convert_cl ss)) t

(*
let convert_instance (ss : (instance ref) list) (s : instance ref) : (I32Wrapper.t, I64Wrapper.t, F32Wrapper.t, F64Wrapper.t, ImplWrapper.memory, ImplWrapper.host_function_t, unit) s_ext =
  let { module_; funcs; tables; memories; globals; exports} = !s in
  let types = List.map (fun (t : (Types.func_type Source.phrase)) -> convert_ftype (t.it)) (module_.it.Ast.types) in
  let (instance_list, cls) = convert_cls [s] funcs in
  let globs = List.map convert_glob globals in
  let (instance_list', tables) = get_tables instance_list tables in
  let tab = Some (Checker.Arith.zero_nat) in
  let mem = Some (Checker.Arith.zero_nat) in
  let insts = [Inst_ext (types, cls, globs, tab, mem, ())] in
  S_ext (insts, tables, memories, ()) *)

let convert_instance (ss : (instance ref) list) (insts, fs, ts, ms, gs) (s : instance ref) =
  let { module_; funcs; tables; memories; globals; exports} = !s in
  let types = List.map (fun (t : (Types.func_type Source.phrase)) -> convert_ftype (t.it)) (module_.it.Ast.types) in
  let fs' = convert_cls ss funcs in
  let t' = (match tables with
            | table::tables' -> [convert_table ss (get_table table)]
            | [] -> []) in
  let m' = (match memories with
            | memory::memories' -> [memory]
            | [] -> []) in
  let f_inds = List.mapi (fun i f -> ocaml_int_to_nat (i + (List.length fs))) fs' in
  let t_ind = ocaml_int_to_nat (List.length ts) in
  let m_ind = ocaml_int_to_nat (List.length ms) in
  let g_inds = List.map (fun g -> ocaml_int_to_nat (index_some gs g)) globals in
  let inst' = Inst_ext (types, f_inds, Some t_ind, Some m_ind, g_inds, ()) in
  (insts@[inst'], fs@fs', ts@t', ms@m', gs)

let create_store (s : (instance ref)) : (instance ref) list * global list * (I32Wrapper.t, I64Wrapper.t, F32Wrapper.t, F64Wrapper.t, ImplWrapperTypes.memory, ImplWrapperTypes.host_function_t, unit) s_ext =
  let ss = collect_instances_instance [] s in
  let gs = collect_globals ss in
  let (insts, funcs, tables, memories, gs') = List.fold_left (convert_instance ss) ([], [], [], [], gs) ss in
  let globals = List.map convert_glob gs' in
  (ss, gs, S_ext (insts, funcs, tables, memories, globals, ()))

let convert_values_to_es vs = (List.map (fun v -> Basic (EConst (convert_value v))) vs)

let convert_b_es_to_es b_es = (List.map (fun b_e -> Basic b_e) b_es)

let empty_config (ss : (instance ref) list) (vs : value list) (cl : closure) =
  ([], (convert_values_to_es vs) @ [Callcl (convert_cl ss cl)])
*)
