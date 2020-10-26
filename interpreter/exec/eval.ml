(* open Values *)
open Svalues
open Types
open Instance
open Ast
open Source
open Pc_type

(* Errors *)

module Link = Error.Make ()
module Trap = Error.Make ()
module Crash = Error.Make ()
module Exhaustion = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)
exception Exhaustion = Exhaustion.Error

(* let memory_error at = function
 *   | Memory.Bounds -> "out of bounds memory access"
 *   | Memory.SizeOverflow -> "memory size overflow"
 *   | Memory.SizeLimit -> "memory size limit reached"
 *   | Memory.Type -> Crash.error at "type mismatch at memory access"
 *   | exn -> raise exn *)

(*TODO(Romy): implement *)
(* let smemory_error at = function *)
  (* | Memory.Bounds -> "out of bounds memory access"
   * | Memory.SizeOverflow -> "memory size overflow"
   * | Memory.SizeLimit -> "memory size limit reached"
   * | Memory.Type -> Crash.error at "type mismatch at memory access" *)
  (* | exn -> raise exn *)

let numeric_error at = function
  | Numeric_error.IntegerOverflow -> "integer overflow"
  | Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Numeric_error.InvalidConversionToInteger -> "invalid conversion to integer"
  | Eval_numeric.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ Types.string_of_value_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ Types.string_of_value_type (Values.type_of v))
  | exn -> raise exn


(* administrative Expressions & Configurations *)

type 'a stack = 'a list

(* TODO(Romy): Fix module_inst *)
type frame =
{
  inst : module_inst;
  locals : svalue list;
}

type code = svalue stack * admin_instr list

and admin_instr = admin_instr' phrase
and admin_instr' =
  | Plain of instr'
  | Invoke of func_inst
  | Trapping of string
  | Returning of svalue stack
  | Breaking of int32 * svalue stack
  | Label of int32 * instr list * code
  | Frame of int32 * frame * code

           
type obs_type =
  | CT_UNSAT of pc * svalue * (Smemory.t list * int) * obs_type
  | CT_V_UNSAT of pc * svalue * (Smemory.t list * int) * obs_type
  (* | CT_SAT of pc * obs_type *)
  | OBSTRUE
  
type config =
{
  frame : frame;
  code : code;
  budget : int;  (* to model stack overflow *)
  pc : pc;  (* to model path condition *)
  msecrets : secret_type list;
  loops : config list;
  abstract_loops: admin_instr' list;
  observations: obs_type
}
and
secret_type = int * int


(* type configs =
 *   {
 *     cs : config list;
 *     loops : config list;
 *   } *)

            
let frame inst locals = {inst; locals}
let config inst vs es =
  {frame = frame inst []; code = vs, es; budget = 300;
   pc = PCTrue; msecrets = inst.secrets; loops = []; abstract_loops = [];
   observations = OBSTRUE }

let plain e = Plain e.it @@ e.at

let lookup category list x =
  try Lib.List32.nth list x.it with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
let func (inst : module_inst) x = lookup "function" inst.funcs x
let table (inst : module_inst) x = lookup "table" inst.tables x
let memory (inst : module_inst) x = lookup "memory" inst.memories x
let smemory (inst : module_inst) x = lookup "smemory" inst.smemories x
let smemlen (inst : module_inst) =  inst.smemlen
let global (inst : module_inst) x = lookup "global" inst.globals x
let local (frame : frame) x = lookup "local" frame.locals x

let update_smemory (inst : module_inst) (mem : Instance.smemory_inst)
      (x : int32 Source.phrase)  = 
  try
    {inst with smemories = Lib.List32.replace x.it mem inst.smemories}
  with Failure _ ->
    Crash.error x.at ("undefined smemory " ^ Int32.to_string x.it)

let insert_smemory (inst : module_inst) (mem : Instance.smemory_inst)  = 
  try
    {inst with smemories = Lib.List32.insert mem inst.smemories;
               smemlen = inst.smemlen + 1 }
  with Failure _ ->
    failwith "insert memory"

let update_local (frame : frame) (x : int32 Source.phrase) (sv: svalue) = 
  try
    {frame with locals = Lib.List32.replace x.it sv frame.locals}
  with Failure _ ->
    Crash.error x.at ("udefined local " ^ Int32.to_string x.it)

(* let elem inst x i at =
 *   match Table.load (table inst x) i with
 *   | Table.Uninitialized ->
 *     Trap.error at ("uninitialized element " ^ Int32.to_string i)
 *   | f -> f
 *   | exception Table.Bounds ->
 *     Trap.error at ("undefined element " ^ Int32.to_string i) *)

(* let func_elem inst x i at =
 *   match elem inst x i at with
 *   | FuncElem f -> f
 *   | _ -> Crash.error at ("type mismatch for element " ^ Int32.to_string i) *)

let func_type_of = function
  | Func.AstFunc (t, inst, f) -> t
  | Func.HostFunc (t, _) -> t

let block_type inst bt =
  match bt with
  | VarBlockType x -> type_ inst x
  | ValBlockType None -> FuncType ([], [])
  | ValBlockType (Some t) -> FuncType ([], [t])

let take n (vs : 'a stack) at =
  try Lib.List32.take n vs with Failure _ -> Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Lib.List32.drop n vs with Failure _ -> Crash.error at "stack underflow"

(* let svalue_to_string (sv : svalue): string =
 *   match sv with
 *   | SI32 sv -> Si32.to_string_s sv
 *   | SI64 sv -> Si64.to_string_s sv
 *   | SF32 sv -> F32.to_string sv
 *   | SF64 sv -> F64.to_string sv *)

  
let split_condition (sv : svalue) (pc : pc): pc * pc =
  let pc' = 
    match sv with
    | SI32 vi32 ->
       let zero = Si32.zero in
       PCAnd( SI32 (Si32.ne vi32 zero), pc)
    | SI64 vi64 ->
       let zero = Si32.zero in
       PCAnd( SI64 (Si64.ne vi64 zero), pc)
    | SF32 vf32 -> PCAnd( SF32 ( F32.neg vf32), pc)
    | SF64 vf64 -> PCAnd( SF64 ( F64.neg vf64), pc)
  in
  let pc'' =
    match sv with
    | SI32 vi32 ->
       let zero = Si32.zero in
       PCAnd( SI32 ( Si32.eq vi32 zero ), pc)
    | SI64 vi64 ->
       let zero = Si64.zero in
       PCAnd( SI64 ( Si64.eq vi64 zero), pc)
    | SF32 vf32 -> PCAnd( SF32 ( F32.neg vf32), pc)
    | SF64 vf64 -> PCAnd( SF64 ( F64.neg vf64), pc)
  in
  (pc'', pc')

let split_msec (sv : svalue) (msec : (int * int) list ) (pc : pc) : pc * pc =  
  (* let pc' = PCAnd (sv, pc) in
   * let pc'' = *)
  let rec within_hrange sv msec =
    match msec with
    | [] -> Si32.ne Si32.zero Si32.zero
    | (lo, hi)::[] ->
       let hrange = Si32.le_u sv (Si32.of_int_s hi) in
       let lrange = Si32.ge_u sv (Si32.of_int_s lo) in
       Si32.and_ hrange lrange
       (* PCAnd(sv, pc) *)
    | (lo, hi)::msecs ->
       let hrange = Si32.le_u sv (Si32.of_int_s hi) in
       let lrange = Si32.ge_u sv (Si32.of_int_s lo) in
       let hl = Si32.and_ hrange lrange in
       Si32.or_ hl (within_hrange sv msecs)
 
  in
    match sv with
    | SI32 vi32 ->
       let hrange = within_hrange vi32 msec in
       let lrange = Si32.not_ hrange in
       (PCAnd (SI32 hrange, pc), PCAnd (SI32 lrange, pc))
    | _ -> failwith "Address should be 32bit integer"


(* in *)
  (* (pc', pc'') *)

let select_condition v0 v1 v2 = (* (v0: svalue  v1: svalue): svalue = *)
  match v0, v1, v2 with
  (* v0 :: v2 :: v1 :: vs' -> *)
  | SI32 vi32, SI32 vi32_1, SI32 vi32_2 -> SI32 ( Si32.ite vi32 vi32_1 vi32_2 )
  | SI64 vi64, SI64 vi64_1, SI64 vi64_2 -> SI64 ( Si64.ite vi64 vi64_1 vi64_2 )
  | SF32 vf32, SF32 vf32_1, SF32 vf32_2 -> SF32 vf32
  | SF64 vf64, SF64 vf64_1, SF64 vf64_2 -> SF64 vf64
  | _ -> failwith "Type problem select"


let merge lold lnew pcnew mem =
  print_endline "merge eval";
  Pc_type.print_pc pcnew |> print_endline;
  svalue_to_string lold |> print_endline;
  svalue_to_string lnew |> print_endline;

  match lold,lnew with
  | SI32 l1, SI32 l2 ->
     let ishigh = Si32.is_high l1 || Si32.is_high l2 in
     let newv = if ishigh then Si32.of_high () else Si32.of_low() in
     let ge = Si32.ge_s l1 l2 in
     if (Z3_solver.is_unsat pcnew (SI32 ge) mem) then
       Some (SI32 newv, Si32.merge Smt_type.TLT l1 l2)
     else (
       let gt = Si32.gt_s l1 l2 in
       if (Z3_solver.is_unsat pcnew (SI32 gt) mem) then
         Some (SI32 newv, Si32.merge Smt_type.TLE l1 l2)
       else (
         let le = Si32.le_s l1 l2 in
         if (Z3_solver.is_unsat pcnew (SI32 le) mem) then
           Some (SI32 newv, Si32.merge Smt_type.TGT l1 l2)
         else (
           let lt = Si32.lt_s l1 l2 in
           if (Z3_solver.is_unsat pcnew (SI32 lt) mem) then
             Some (SI32 newv, Si32.merge Smt_type.TGE l1 l2)
           else Some (SI32 newv, Si32.merge Smt_type.TNONE l1 l2)
         )
       )
     )
  | SI64 l1, SI64 l2 ->
     let ishigh = Si64.is_high l1 || Si64.is_high l2 in
     let newv = if ishigh then Si64.of_high () else Si64.of_low() in
     let ge = Si64.ge_s l1 l2 in
     if (Z3_solver.is_unsat pcnew (SI64 ge) mem) then
       Some (SI64 newv, Si64.merge Smt_type.TLT l1 l2)
     else (
       let gt = Si64.gt_s l1 l2 in
       if (Z3_solver.is_unsat pcnew (SI64 gt) mem) then
         Some (SI64 newv, Si64.merge Smt_type.TLE l1 l2)
       else (
         let le = Si64.le_s l1 l2 in
         if (Z3_solver.is_unsat pcnew (SI64 le) mem) then
           Some (SI64 newv, Si64.merge Smt_type.TGT l1 l2)
         else (
           let lt = Si64.lt_s l1 l2 in
           if (Z3_solver.is_unsat pcnew (SI64 lt) mem) then
             Some (SI64 newv, Si64.merge Smt_type.TGE l1 l2)
           else Some (SI64 newv, Si64.merge Smt_type.TNONE l1 l2)
         )
       )
     )
  | _ -> None

let gen_constraints v range =
  match v with
  | SI32 v ->
     (match range with
     | None -> []
     | Some (Smt_type.Term t, Smt_type.PLUS_INF)  -> [SI32 (Si32.ge_s v t)]
     | Some (Smt_type.MINUS_INF, Smt_type.Term t) -> [SI32 (Si32.le_s v t)]
     | Some (Smt_type.Integer i, Smt_type.Term t) ->
        [SI32 (Si32.le_s v t); SI32 (Si32.ge_s v (Si32.of_int_s i))]
     | Some (Smt_type.Term t, Smt_type.Integer i) ->
        [SI32 (Si32.ge_s v t); SI32 (Si32.le_s v (Si32.of_int_s i))]
     | _ -> [])
  | SI64 v ->
     (match range with
     | None -> []
     | Some (Smt_type.Term t, Smt_type.PLUS_INF)  -> [SI64 (Si64.ge_s v t)]
     | Some (Smt_type.MINUS_INF, Smt_type.Term t) -> [SI64 (Si64.le_s v t)]
     | Some (Smt_type.Integer i, Smt_type.Term t) ->
        [SI64 (Si64.le_s v t); SI64 (Si64.ge_s v (Si64.of_int_s i))]
     | Some (Smt_type.Term t, Smt_type.Integer i) ->
        [SI64 (Si64.ge_s v t); SI64 (Si64.le_s v (Si64.of_int_s i))]
     | _ -> [])

  | _ -> []

let is_loop_equal l1 l2 =
  match l1, l2 with
    | Plain(Loop (bv, es')), Plain(Loop (bvi, esi')) when bv == bvi && es' == esi' -> true
    | _ -> false

       
let rec check_loops c cs =
  let check_loops_i c ci =
    let rec check_locals l1s l2s ind ci =
      match l1s,l2s with
      | l1::l1s',l2::l2s' ->
         (* svalue_to_string l1 |> print_endline; *)
         (* svalue_to_string l2 |> print_endline; *)
         (* New mem *)
         let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in
         (* print_endline "merge"; *)
         let newvrange = merge l1 l2 c.pc mem in
         (match newvrange with
         | Some (newv,range) ->
            (* print_endline (merge_to_string comp); *)
            let ci' = { ci with frame = update_local ci.frame ind newv } in
            let ci' =
              match range with
              | None -> ci'
              | Some (Smt_type.Term t, Smt_type.PLUS_INF) ->
                 let mv = Z3_solver.optimize Z3_solver.max ci.pc mem l2 in
                 (match mv with
                  | None ->
                     let cs = gen_constraints newv range in
                     let pc' = List.fold_left (fun pci c -> PCAnd (c, pci)) ci'.pc cs in
                     { ci' with pc = pc' }
                     (* Some (newv, cs) *)
                  | Some v ->
                     let nrange = Some (Smt_type.Term t, Smt_type.Integer v) in
                     let cs = gen_constraints newv nrange in
                     let pc' = List.fold_left (fun pci c -> PCAnd (c, pci)) ci'.pc cs in
                     { ci' with pc = pc' }
                 (* Some (newv, cs) *)
                 )
              | Some (Smt_type.MINUS_INF, Smt_type.Term t) ->
                 let mv = Z3_solver.optimize Z3_solver.min ci'.pc mem l2 in
                 (match mv with
                  | None ->
                     let cs = gen_constraints newv range in
                     let pc' = List.fold_left (fun pci c -> PCAnd (c, pci)) ci'.pc cs in
                     { ci' with pc = pc' }
                     (* Some (newv, cs) *)
                  | Some v ->
                     let nrange = Some (Smt_type.Term t, Smt_type.Integer v) in
                     let cs = gen_constraints newv nrange in
                     let pc' = List.fold_left (fun pci c -> PCAnd (c, pci)) ci'.pc cs in
                     { ci' with pc = pc' }
                     (* Some (newv, cs) *)
                 )
              | _ -> ci'
            in
            let nind = Int32.of_int ((Int32.to_int ind.it) + 1) in
            check_locals l1s' l2s' (nind @@ ind.at) ci'
         | None ->
            let nind = Int32.of_int ((Int32.to_int ind.it) + 1) in
            check_locals l1s' l2s' (nind @@ ind.at) ci
         (* check_locals (None::acc) l1s' l2s' ind ci) *)
         )
      | l::_, [] 
        | [], l::_ -> ci (*List.rev acc*)
      | [], [] -> ci (* List.rev acc *)
    in
    let {frame; code = vs, es; pc; _} = c in
    let {frame = framei; code = vsi,esi; pc = pci; _} = ci in
    let e, ei = (List.hd es, List.hd esi) in 
    if is_loop_equal e.it ei.it then 
    (* match e.it, ei.it with
     * | Plain ( Loop (bv, es')), Plain ( Loop (bvi, esi')) when bv == bvi && es' == esi' -> *)
      let loc1 = frame.locals in
      let loc2 = framei.locals in
      Some (check_locals loc1 loc2 (0l @@ e.at) ci)
    else None
    (* | _ -> None *)
  in
  match c, cs with
  | _, c1::cs' ->
     let cl = check_loops_i c c1 in
     (match cl with
      (* Terminates after the first matching loop *)
     | Some (cls) -> Some (cls)
     | None -> check_loops c cs')
  | _, [] -> None

(* Evaluation *)

(*
 * Conventions:
 *   e  : instr
 *   v  : svalue
 *   es : instr list
 *   vs : svalue stack
 *   c : config
 *)
(*TODO(Romy): Implement debug flag etc*)

let rec step (c : config) : config list =
  let {frame; code = vs, es; pc; _} = c in
  let e = List.hd es in
  (* let vs', es' = *)
  let res =
    match e.it, vs with
    | Plain e', vs ->
       (match e', vs with
        | Unreachable, vs ->
           let vs', es' = vs, [Trapping "unreachable executed" @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]
        | Nop, vs ->
           (* print_endline "nop"; *)
           let vs', es' = vs, [] in
           [{c with code = vs', es' @ List.tl es}]
        | Block (bt, es'), vs ->
           (* print_endline "block"; *)
           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let n2 = Lib.List32.length ts2 in
           let args, vs' = take n1 vs e.at, drop n1 vs e.at in
           let vs', es' = vs', [Label (n2, [], (args, List.map plain es')) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]
        | Loop (bt, es'), vs ->
           (* print_endline "loop"; *)
           (if (List.fold_left (fun b ei -> (is_loop_equal e.it ei) || b)
                  false c.abstract_loops) then
              (print_endline "Skipping loop";
              let vs', es' = vs, [] in
              [{c with code = vs', es' @ List.tl es}])
            else 
              (match (check_loops c c.loops) with
               | Some newc -> 
                  let FuncType (ts1, ts2) = block_type frame.inst bt in
                  let n1 = Lib.List32.length ts1 in
                  let args, vs' = take n1 vs e.at, drop n1 vs e.at in
                  let vs', es' = vs', [Label (n1, [e' @@ e.at], (args, List.map plain es')) @@ e.at] in
                  [{newc with code = vs', es' @ List.tl es;
                              abstract_loops = e.it::c.abstract_loops;
                              loops = c.loops}]
                  
               | None -> 
                  let FuncType (ts1, ts2) = block_type frame.inst bt in
                  let n1 = Lib.List32.length ts1 in
                  let args, vs' = take n1 vs e.at, drop n1 vs e.at in
                  let vs', es' = vs', [Label (n1, [e' @@ e.at], (args, List.map plain es')) @@ e.at] in
                  [{c with code = vs', es' @ List.tl es; loops = c::c.loops}]
              )
           )
        | If (bt, es1, es2), v :: vs' ->
           (* print_endline "if"; *)
           let pc', pc'' = split_condition v pc in
           let vs'', es'' = vs', [Plain (Block (bt, es1)) @@ e.at] in (* True *)
           let vs', es' = vs', [Plain (Block (bt, es2)) @@ e.at] in (* False *)
           (* Check sat of if *)

           let mem = (frame.inst.smemories, smemlen frame.inst) in 

           let c = {c with observations = CT_UNSAT(pc, v, mem, c.observations)} in
           
           let res = if Z3_solver.is_sat pc' mem then
                       [{c with code = vs', es' @ List.tl es; pc = pc'}]
                     else [] in
           let res = if Z3_solver.is_sat pc'' mem then
                       {c with code = vs'', es'' @ List.tl es; pc = pc''}::res
                     else res in
           
           (* Must be unsat *)
           if Z3_solver.is_ct_unsat pc v mem then res
           else failwith "If: Constant-time failure"

        | Br x, vs ->
           (* print_endline "br"; *)
           let vs', es' = [], [Breaking (x.it, vs) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]
           
        | BrIf x, v :: vs' ->
           (* print_endline "br_if"; *)
           let pc', pc'' = split_condition v pc in
           let vs'', es'' = vs', [Plain (Br x) @@ e.at] in
           let vs', es' = vs', [] in
           
           let mem = (frame.inst.smemories, smemlen frame.inst) in

           (* proof obligation *)
           let c = {c with observations = CT_UNSAT(pc, v, mem, c.observations)} in
           
           let res = if Z3_solver.is_sat pc' mem then
                       [{c with code = vs', es' @ List.tl es; pc = pc'}]
                     else [] in
           let res = if Z3_solver.is_sat pc'' mem then
                       {c with code = vs'', es'' @ List.tl es; pc = pc''}::res
                     else res in
           
           (* Must be unsat *)

           if Z3_solver.is_ct_unsat pc v mem then res
           else failwith "BrIf: Constant-time failure"
           
        (* | BrTable (xs, x), I32 i :: vs' when I32.ge_u i (Lib.List32.length xs) ->
         *   vs', [Plain (Br x) @@ e.at]
         * 
         * | BrTable (xs, x), I32 i :: vs' ->
         *   vs', [Plain (Br (Lib.List32.nth xs i)) @@ e.at] *)

        | Return, vs ->
           (* print_endline "return"; *)
           let vs', es' = [], [Returning vs @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]

        | Call x, vs ->
           (* print_endline "call"; *)
           let vs', es' = vs, [Invoke (func frame.inst x) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]

        (* | CallIndirect x, I32 i :: vs ->
         *   let func = func_elem frame.inst (0l @@ e.at) i e.at in
         *   if type_ frame.inst x <> Func.type_of func then
         *     vs, [Trapping "indirect call type mismatch" @@ e.at]
         *   else
         *     vs, [Invoke func @@ e.at] *)

        | Drop, v :: vs' ->
           (* print_endline "drop"; *)
           let vs', es' = vs', [] in
           [{c with code = vs', es' @ List.tl es}]
           
        | Select, v0 :: v2 :: v1 :: vs' ->
           (* print_endline "select"; *)
           let vselect = select_condition v0 v1 v2 in
           (* let pc' = PCAnd(cond, pc) in *)
           let vs', es' = vselect :: vs', [] in
           [{c with code = vs', es' @ List.tl es }]
           
        | LocalGet x, vs ->
           (* print_endline "localget"; *)
           let vs', es' = (local frame x) :: vs, [] in
           [{c with code = vs', es' @ List.tl es}]

        | LocalSet x, v :: vs' ->
           (* print_endline "localset"; *)
           let frame' = update_local c.frame x v in
           let vs', es' = vs', [] in
           [{c with code = vs', es' @ List.tl es; frame = frame'}]

        | LocalTee x, v :: vs' ->
           (* print_endline "localtee"; *)
           let frame' = update_local c.frame x v in
           (* local frame x := v; *)
           let vs', es' = v :: vs', [] in
           [{c with code = vs', es' @ List.tl es; frame = frame'}]

        (* | GlobalGet x, vs ->
         *   Global.load (global frame.inst x) :: vs, [] *)

        (* | GlobalSet x, v :: vs' ->
         *   (try Global.store (global frame.inst x) v; vs', []
         *   with Global.NotMutable -> Crash.error e.at "write to immutable global"
         *      | Global.Type -> Crash.error e.at "type mismatch at global write") *)

        | Load {offset; ty; sz; _}, si :: vs' ->
           let imem = smemory frame.inst (0l @@ e.at) in

           (* let mem = Smemory.init_secrets mem c.msecrets in *)
           
           let frame = {frame with
                         inst = update_smemory frame.inst imem (0l @@ e.at)} in
           
           let addr =
             (match si with
              | SI32 v -> v
              | _ -> failwith "Error: Address should be 32-bit integer"
             ) in (* I64_convert.extend_i32_u i in *)
           let offset = Int32.to_int offset in        
           let mem = (frame.inst.smemories, smemlen frame.inst) in

           let c = {c with observations = CT_V_UNSAT(pc, si, mem, c.observations)} in

           if (Z3_solver.is_v_ct_unsat pc si mem) then
             (
               let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in
               (* let final_addr = Eval_symbolic.address ty addr offset in (\*  *\) *)
               let msec = Smemory.get_secrets imem in
               let pc', pc'' = split_msec final_addr msec pc in
               (* The loaded value consists of the (symbolic) index and the memory
                   index *)
               let nv = Eval_symbolic.eval_load ty final_addr (smemlen frame.inst) in
               let vs', es' =  nv :: vs', [] in 
               let res = if Z3_solver.is_sat pc' mem then(
                           [{c with code = vs', es' @ List.tl es;
                                    frame = frame;
                                    pc = pc'}])
                         else []
               in
               let res = if Z3_solver.is_sat pc'' mem then
                           (* low values *)
                           {c with code = vs', es' @ List.tl es;
                                   frame = frame;
                                   pc = pc''}:: res
                         else res in
               res)
           else failwith "The index does not satisfy CT."
       (* ) *)
           
        | Store {offset; ty; sz; _}, sv :: si :: vs' ->
           print_endline "store";
           (* Pc_type.print_pc pc |> print_endline; *)
           let mem = smemory frame.inst (0l @@ e.at) in
           (* TODO(Romy): find a better way to do this *)
           (* let mem = Smemory.init_secrets mem c.msecrets in *)
           let frame = {frame with
                         inst = update_smemory frame.inst mem (0l @@ e.at)} in
           let addr =
             (match si with
              | SI32 v -> v
              | _ -> failwith "Error: Address should be 32-bit integer"
             ) in (* I64_convert.extend_i32_u i in *)
           let offset = Int32.to_int offset in
           (* check if we satisfy CT  for the index *)

           let mems = (frame.inst.smemories, smemlen frame.inst) in
           
           let c = {c with observations = CT_V_UNSAT(pc, si, mems, c.observations)} in
           
           if (Z3_solver.is_v_ct_unsat pc si mems) then
             let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in
             let msec = Smemory.get_secrets mem in
             (* print_endline "c.msecrets";
              * List.length msec |> string_of_int |> print_endline; *)
             let pc', pc'' = split_msec final_addr msec pc in
             let nv = Eval_symbolic.eval_store ty final_addr sv (smemlen frame.inst) in
             let mem' = Smemory.store_sind_value mem nv in
             let vs', es' = vs', [] in
             (* Update memory with a store *)
             let nframe = {frame with inst = insert_smemory frame.inst mem'} in
             (* Path1: we store the value in secret memory *)
             (* print_endline "before is_sat1"; *)
             let res = if Z3_solver.is_sat pc' mems then (
                         (* print_endline "in is_sat1"; *)
                         [{c with code = vs', es' @ List.tl es;
                                  frame = nframe; 
                                  pc = pc'}])
                       else []
             in
             (* Path2: we store the value in non secret memory *)
             let res = if Z3_solver.is_sat pc'' mems then
                         (let c = {c with observations =
                                            CT_V_UNSAT(pc'', sv, mems, c.observations)} in
                          if Z3_solver.is_v_ct_unsat pc'' sv mems then
                            {c with code = vs', es' @ List.tl es;
                                    frame = nframe;
                                    pc = pc''}:: res
                          else failwith "Trying to write high values in low memory")
                       else res in
             res
           else failwith "The index does not satisfy CT."

        (* | MemorySize, vs ->
         *   let mem = memory frame.inst (0l @@ e.at) in
         *   I32 (Memory.size mem) :: vs, []
         * 
         * | MemoryGrow, I32 delta :: vs' ->
         *   let mem = memory frame.inst (0l @@ e.at) in
         *   let old_size = Memory.size mem in
         *   let result =
         *     try Memory.grow mem delta; old_size
         *     with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
         *   in I32 result :: vs', [] *)

        (*TODO(Romy): Implement Const*)
        | Const v, vs ->
           (* print_endline "const"; *)
           let va = 
             match v.it with
             | Values.I32 i ->
                let ii = Int32.to_int i in
                SI32 (Si32.bv_of_int ii 32)
             | Values.I64 i ->
                let ii = Int64.to_int i in
                SI64 (Si64.bv_of_int ii 64)
             | Values.F32 i -> SF32 i
             | Values.F64 i -> SF64 i
           in
           let vs', es' = va :: vs, [] in
           [{c with code = vs', es' @ List.tl es}]
           
        (* | Const v, vs ->
         *    v.it :: vs, [] *)

        | Test testop, v :: vs' ->
           (* print_endline "testop"; *)
           let vs', es' =
             (try (Eval_symbolic.eval_testop testop v) :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es}]
           
        | Compare relop, v2 :: v1 :: vs' ->
           (* print_endline "relop"; *)
           let vs', es' =
             (try (Eval_symbolic.eval_relop relop v1 v2) :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es}]
        | Unary unop, v :: vs' ->
           (* print_endline "unop"; *)
           let vs', es' = 
             (try Eval_symbolic.eval_unop unop v :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es}]
        | Binary binop, v2 :: v1 :: vs' ->
           (* print_endline "binop"; *)
           let vs', es' = 
             (try
                let nv = Eval_symbolic.eval_binop binop v1 v2 in
                (* "Printing binop" |> print_endline; *)
                (* Pc_type.svalue_to_string nv |> print_endline; *)
                nv :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es}]
        (* | Convert cvtop, v :: vs' ->
         *   (try Eval_numeric.eval_cvtop cvtop v :: vs', []
         *   with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) *)

        | _ ->
           let s1 = Svalues.string_of_values (List.rev vs) in
           let s2 = Types.string_of_svalue_types (List.map Svalues.type_of (List.rev vs)) in
           Crash.error e.at
             ("missing or ill-typed operand on stack (" ^ s1 ^ " : " ^ s2 ^ ")")
       )

    | Trapping msg, vs ->
       assert false

    | Returning vs', vs ->
       Crash.error e.at "undefined frame"

    | Breaking (k, vs'), vs ->
       Crash.error e.at "undefined label"

    | Label (n, es0, (vs', [])), vs ->
       (* print_endline "lab"; *)
       let vs', es' = vs' @ vs, [] in
       [{c with code = vs', es' @ List.tl es}]
    | Label (n, es0, (vs', {it = Trapping msg; at} :: es')), vs ->
       (* print_endline "lab2"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Returning vs0; at} :: es')), vs ->
       (* print_endline "lab3"; *)
       let vs', es' = vs, [Returning vs0 @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (0l, vs0); at} :: es')), vs ->
       (* print_endline "lab4"; *)
       let vs', es' = take n vs0 e.at @ vs, List.map plain es0 in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (k, vs0); at} :: es')), vs ->
       (* print_endline "lab5"; *)
       let vs', es' = vs, [Breaking (Int32.sub k 1l, vs0) @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, code'), vs ->
       (* print_endline "lab6"; *)
       let c' = step {c with code = code'} in
       List.map (fun ci -> {ci with code = vs, [Label (n, es0, ci.code) @@ e.at]
                                               @ List.tl es}) c'

    | Frame (n, frame', (vs', [])), vs ->
       (* print_endline "frame1"; *)
       let vs', es' = vs' @ vs, [] in
       [{c with code = vs', es' @ List.tl es}]

    | Frame (n, frame', (vs', {it = Trapping msg; at} :: es')), vs ->
       (* print_endline "frame2"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Frame (n, frame', (vs', {it = Returning vs0; at} :: es')), vs ->
       (* print_endline "frame3"; *)
       let vs', es' = take n vs0 e.at @ vs, [] in
       [{c with code = vs', es' @ List.tl es}]

    | Frame (n, frame', code'), vs ->
       (* print_endline "frame4"; *)
       let c' = step {c with frame = frame'; code = code'; budget = c.budget - 1} in
       List.map (fun ci -> {ci with code = vs, [Frame (n, ci.frame, ci.code) @@ e.at] @ List.tl es}) c'

    | Invoke func, vs when c.budget = 0 ->
       Exhaustion.error e.at "call stack exhausted"

    | Invoke func, vs ->
       (* print_endline "inv2"; *)
       let FuncType (ins, out) = func_type_of func in
       let n1, n2 = Lib.List32.length ins, Lib.List32.length out in
       let args, vs' = take n1 vs e.at, drop n1 vs e.at in
       (match func with
        | Func.AstFunc (t, inst', f) ->
           let rest = List.map value_to_svalue_type f.it.locals in
           let locals' = List.rev args @ List.map Svalues.default_value rest in
           let frame' = {inst = !inst'; locals = locals'} in
           let instr' = [Label (n2, [], ([], List.map plain f.it.body)) @@ f.at] in 
           let vs', es' = vs', [Frame (n2, frame', ([], instr')) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]

        (* | Func.HostFunc (t, f) ->
         *   (try List.rev (f (List.rev args)) @ vs', []
         *   with Crash (_, msg) -> Crash.error e.at msg) *)
        | _ -> Crash.error e.at "Func.Hostfunc not implemented yet."
       )
  in
  (* print_endline "end of step";
   * List.length res |> string_of_int |> print_endline;
   * List.iter (fun c -> Pc_type.print_pc c.pc |> print_endline;) res; *)
  res

(* Eval BFS *)
let filter_step (c: config) : config list option =
  match c.code with
  | vs, [] -> None
  | vs, {it = Trapping msg; at } :: _ ->
     Trap.error at msg
  | vs, es ->
     let st = step c in
     Some st

let filter_done (c: config) : pc option = 
  match c.code with
  | vs, [] ->
     (* "Printing pc" |> print_endline;
      * print_pc c.pc |> print_endline; *)
     Some c.pc
  | vs, {it = Trapping msg; at } :: _ ->
     Trap.error at msg
  | vs, es -> None


(* let filter_map (a' -> b' option) -> a' list -> b' list *)
let filter_map f cs =
  let rec filter_map_i f cs acc =
        match cs with
        | c::cs' ->
           (match f c with
            | Some v -> filter_map_i f cs' (v::acc)
            | None -> filter_map_i f cs' acc
           )
        | [] -> acc
  in
  filter_map_i f cs [] |> List.rev
     
let rec eval_bfs (cs : config list) : pc list =
  (* print_endline "BFS"; *)
  let spaths = filter_map filter_done cs in
  let css = filter_map filter_step cs in
  spaths @ (List.fold_left (@) [] css |> eval_bfs)


             
     
(* Eval DFS *)
let eval_dfs (cs : config list) : pc list =
  let rec eval_dfs_i (cs : config list) (acc : pc list) =
    (* print_endline "eval_dfs_i"; *)
    match cs with
    | c::cs' ->
       (match c.code with
        | vs, [] -> eval_dfs_i cs' (c.pc::acc)
        | vs, {it = Trapping msg; at} :: _ -> Trap.error at msg
        | vs, es -> (
           let ncs = step c in
           eval_dfs_i (ncs @ cs') acc
        )
       )
      
    | [] -> List.rev acc
  in
  eval_dfs_i cs []
   
(* let rec eval (c : config) : svalue stack =
 *   match c.code with
 *   | vs, [] ->
 *     vs
 * 
 *   | vs, {it = Trapping msg; at} :: _ ->
 *     Trap.error at msg
 * 
 *   | vs, es ->
 *      let st = step c in
 *      eval (List.hd st) *)

let eval (c : config) : pc list =
  if !Flags.bfs then
    eval_bfs [c]
  else 
    eval_dfs [c] (* {cs = [c]; loops = []} *)

(* Functions & Constants *)

let invoke (func : func_inst) (vs : svalue list) : pc list =
  let at = match func with Func.AstFunc (_,_, f) -> f.at | _ -> no_region in
  (* let FuncType (ins, out) = Func.type_of func in
   * if List.map Svalues.type_of vs <> ins then
   *   Crash.error at "wrong number or types of arguments"; *)
  let c = config empty_module_inst (List.rev vs) [Invoke func @@ at] in
  try List.rev (eval c) with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"

(* Todo(Romy): fix the check *)
let symb_invoke (func : func_inst) (vs : svalue list): pc list =
  let at = match func with Func.AstFunc (_,_, f) -> f.at | _ -> no_region in
  (* let FuncType (ins, out) = Func.type_of func in
   * if List.map Svalues.type_of vs <> ins then
   *   Crash.error at "wrong number or types of arguments"; *)
  let c = config empty_module_inst (List.rev vs) [Invoke func @@ at] in
  try List.rev (eval c) with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"

                             
(*TODO(Romy): Check this one *)
let eval_const (inst : module_inst) (const : const) : svalue =
  (* let c = config inst [] (List.map plain const.it) in *) 
  match const.it with
  | [v] ->
     (match v.it with
      | Const v -> value_to_svalue v.it
      | _ -> Crash.error const.at "Evaluation on constants not implemented, yet."
     )
  | _ -> Crash.error const.at "wrong number of results on stack"

(* let c = config inst [] (List.map plain const.it) in *)
  (* match eval c with
   * | [v] -> v
   * | vs -> Crash.error const.at "wrong number of results on stack" *)


let i32 (v : svalue) at =
  match v with
  | SI32 i -> Int32.of_int (Si32.to_int_s i)
  | _ -> Crash.error at "type error: i32 value expected"


(* Modules *)

let create_func (inst : module_inst) (f : func) : func_inst =
  Func.alloc (type_ inst f.it.ftype) (ref inst) f

let create_table (inst : module_inst) (tab : table) : table_inst =
  let {ttype} = tab.it in
  Table.alloc ttype

let create_memory (inst : module_inst) (mem : memory) : memory_inst =
  let {mtype} = mem.it in
  Memory.alloc mtype

let create_smemory (inst : module_inst) (mem : smemory) : smemory_inst =
  let {smtype} = mem.it in
  Smemory.alloc smtype


(* let create_global (inst : module_inst) (glob : global) : global_inst =
 *   let {gtype; value} = glob.it in
 *   let v = eval_const inst value in
 *   Global.alloc gtype v *)

let create_export (inst : module_inst) (ex : export) : export_inst =
  let {name; edesc} = ex.it in
  let ext =
    match edesc.it with
    | FuncExport x -> ExternFunc (func inst x)
    | TableExport x -> ExternTable (table inst x)
    | MemoryExport x -> ExternMemory (memory inst x)
    | SmemoryExport x -> ExternSmemory (smemory inst x)
    | GlobalExport x -> ExternGlobal (global inst x)
  in name, ext


let init_func (inst : module_inst) (func : func_inst) =
  match func with
  | Func.AstFunc (_, inst_ref, _) -> inst_ref := inst
  | _ -> assert false

let init_table (inst : module_inst) (seg : table_segment) =
  let {index; offset = const; init} = seg.it in
  let tab = table inst index in
  let offset = i32 (eval_const inst const) const.at in
  let end_ = Int32.(add offset (of_int (List.length init))) in
  let bound = Table.size tab in
  if I32.lt_u bound end_ || I32.lt_u end_ offset then
    Link.error seg.at "elements segment does not fit table";
  fun () ->
    Table.blit tab offset (List.map (fun x -> FuncElem (func inst x)) init)

let init_memory (inst : module_inst) (seg : memory_segment) =
  let {index; offset = const; init} = seg.it in
  let mem = memory inst index in
  let offset' = i32 (eval_const inst const) const.at in
  let offset = I64_convert.extend_i32_u offset' in
  let end_ = Int64.(add offset (of_int (String.length init))) in
  let bound = Memory.bound mem in
  if I64.lt_u bound end_ || I64.lt_u end_ offset then
    Link.error seg.at "data segment does not fit memory";
  fun () -> Memory.store_bytes mem offset init

let init_smemory (secret : bool) (inst : module_inst) (sec : security) = 
  let {index; range = (const_lo,const_hi)} = sec.it in
  let smem = smemory inst index in
  let lo = i32 (eval_const inst const_lo) const_lo.at in
  let hi = i32 (eval_const inst const_hi) const_hi.at in
  let lo,hi = Int32.to_int lo, Int32.to_int hi in
  let hi_list = List.init ((hi-lo+1)/4) (fun x-> 4*x + lo) in
  let stores =
    match secret with
    | true -> List.map Eval_symbolic.create_new_hstore hi_list
    | false -> List.map Eval_symbolic.create_new_lstore hi_list
  in

  (* let inst' =
   *   match secret with
   *   | true -> { inst with secrets = (lo,hi)::inst.secrets }
   *   | false -> { inst with public = (lo,hi)::inst.public }
   * in *)
  let smem =
    match secret with
    | true -> Smemory.add_secret smem (lo,hi)
    | false -> Smemory.add_public smem (lo,hi)
  in

  let mem = List.fold_left Smemory.store_sind_value smem stores in  
  update_smemory inst mem  (0l @@ sec.at)
  
  (* let offset' = i32 (eval_const inst const) const.at in *)
  (* let offset = I64_convert.extend_i32_u offset' in *)
  (* let end_ = Int64.(add offset (of_int (String.length init))) in *)
  (* let bound = Memory.bound mem in *)
  
  (* if I64.lt_u bound end_ || I64.lt_u end_ offset then
   *   Link.error seg.at "data segment does not fit memory"; *)
  


let add_import (m : module_) (ext : extern) (im : import) (inst : module_inst)
  : module_inst =
  if not (match_extern_type (extern_type_of ext) (import_type m im)) then
    Link.error im.at "incompatible import type";
  match ext with
  | ExternFunc func -> {inst with funcs = func :: inst.funcs}
  | ExternTable tab -> {inst with tables = tab :: inst.tables}
  | ExternMemory mem -> {inst with memories = mem :: inst.memories}
  | ExternSmemory smem -> {inst with smemories = smem :: inst.smemories;
                                     smemlen = 1 + inst.smemlen }
  | ExternGlobal glob -> {inst with globals = glob :: inst.globals}

let init (m : module_) (exts : extern list) : module_inst =
  let
    { imports; tables; memories; smemories; globals; funcs; types;
      exports; elems; data; start; secrets; public
    } = m.it
  in

  if List.length exts <> List.length imports then
    Link.error m.at "wrong number of imports provided for initialisation";
  let inst0 =
    { (List.fold_right2 (add_import m) exts imports empty_module_inst) with
      types = List.map (fun type_ -> type_.it) types }
  in


  let fs = List.map (create_func inst0) funcs in
  let inst1 =
    { inst0 with
      funcs = inst0.funcs @ fs;
      tables = inst0.tables @ List.map (create_table inst0) tables;
      memories = inst0.memories @ List.map (create_memory inst0) memories;
      smemories = inst0.smemories @ List.map (create_smemory inst0) smemories;
      smemlen = List.length  (inst0.smemories) + List.length(smemories);
      globals = inst0.globals;
      (* msecrets = inst0.msecrets @ List.map (create_secrets inst0) secrets; *)
                  (* @ List.map (create_global inst0) globals; *)
    }
  in
  let inst1 = List.fold_left (init_smemory true) inst1 secrets in
  let inst1 = List.fold_left (init_smemory false) inst1 public in
  let inst = {inst1 with exports = List.map (create_export inst1) exports} in
  List.iter (init_func inst) fs;
  
  let init_elems = List.map (init_table inst) elems in
  let init_datas = List.map (init_memory inst) data in

  List.iter (fun f -> f ()) init_elems;
  List.iter (fun f -> f ()) init_datas;
  Lib.Option.app (fun x -> ignore (invoke (func inst x) [])) start;
  inst
