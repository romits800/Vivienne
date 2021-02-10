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
module ConstantTime = Error.Make ()
module NonInterference = Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error (* failure that cannot happen in valid code *)
exception Exhaustion = Exhaustion.Error
(* exception ConstantTime = ConstantTime.Error
 * exception NonIntereference = NonInterference.Error *)

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
  | Eval_symbolic.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ Types.string_of_svalue_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ Types.string_of_svalue_type (Svalues.type_of v))
  | exn -> raise exn


(* administrative Expressions & Configurations *)

type 'a stack = 'a list

(* TODO(Romy): Fix module_inst *)
type frame =
{
  inst : module_inst;
  locals : svalue list;
}


type modifier = Increase of svalue | Decrease of svalue | Nothing
                                                       
type loopvar_t = LocalVar of int32 Source.phrase * bool * modifier (* local x * is_sat *)
               | GlobalVar of int32 Source.phrase * bool * modifier
               | StoreVar of svalue * Types.value_type * Types.pack_size option * bool * modifier


module IndVarMap = Map.Make(struct
                       type t = svalue
                       let compare = compare
                     end)


type triple = svalue * svalue * svalue * svalue (*real init value, symb init value, mul, add*)

                           
type iv_type = triple IndVarMap.t

type ct_check_t = bool
              
type code = svalue stack * admin_instr list          
and admin_instr = admin_instr' phrase
and admin_instr' =
  | Plain of instr'
  | Invoke of func_inst
  | Trapping of string
  | Returning of svalue stack
  | Breaking of int32 * svalue stack
  | Label of int32 * admin_instr list * code * pc_ext * iv_type option * ct_check_t 
  | Frame of int32 * frame * code * pc_ext * iv_type option 
  | Assert of loopvar_t list * instr'
  | Havoc of loopvar_t list
  | FirstPass of int32 * admin_instr list * code
  | SecondPass of int32 * admin_instr list * code 
           
type obs_type =
  | CT_UNSAT of pc_ext * svalue * (Smemory.t list * int) * obs_type
  | CT_V_UNSAT of pc_ext * svalue * (Smemory.t list * int) * obs_type
  (* | CT_SAT of pc * obs_type *)
  | OBSTRUE

type config =
{
  frame : frame;
  code : code;
  budget : int;  (* to model stack overflow *)
  pc : pc_ext;  (* to model path condition *)
  progc : int;
  msecrets : secret_type list;
  loops : config list;
  (* abstract_loops: admin_instr' list; *)
  abstract_loops: config list;
  observations: obs_type;
  counter : int;
  induction_vars : iv_type option;
  ct_check : ct_check_t;
}
and
secret_type = int * int



let modifier_to_string = function
  | Decrease vold -> "Decrease " ^ (svalue_to_string vold)
  | Increase vold -> "Increase " ^ (svalue_to_string vold)
  | Nothing -> "Nothing"
                     
let print_loopvar = function
  | LocalVar (i, tf, mo) ->
     "Local " ^ (string_of_bool tf) ^ " " ^ (Int32.to_int i.it |> string_of_int) |> print_endline
  | GlobalVar (i, tf, mo) ->
     "Global " ^ (string_of_bool tf) ^ " " ^ (Int32.to_int i.it |> string_of_int) |> print_endline
  | StoreVar (sv, ty, sz, tf, mo) ->
     "Store " ^ (string_of_bool tf) ^ " " ^ (svalue_to_string sv) |> print_endline
     
  
    
let frame inst locals = {inst; locals}
let config inst vs es =
  {frame = frame inst []; code = vs, es; budget = 300;
   pc = empty_pc(); msecrets = inst.secrets; loops = []; abstract_loops = [];
   observations = OBSTRUE;  counter = 0; induction_vars = None; progc = 0;
   ct_check = true}

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
(* let global (inst : module_inst) x = lookup "global" inst.globals x *)
let sglobal (inst : module_inst) x = lookup "sglobal" inst.sglobals x
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

let update_sglobal (inst : module_inst) (glob : Instance.sglobal_inst)
      (x : int32 Source.phrase)  = 
  try
    {inst with sglobals = Lib.List32.replace x.it glob inst.sglobals}
  with Failure _ ->
    Crash.error x.at ("undefined smemory " ^ Int32.to_string x.it)

let elem inst x i at =
  match Table.load (table inst x) i with
  | Table.Uninitialized ->
    Trap.error at ("uninitialized element " ^ Int32.to_string i)
  | f -> f
  | exception Table.Bounds ->
    Trap.error at ("undefined element " ^ Int32.to_string i)

let func_elem inst x i at =
  match elem inst x i at with
  | FuncElem f -> f
  | _ -> Crash.error at ("type mismatch for element " ^ Int32.to_string i)

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
  (pc'', pc') (* false, true *)

let split_msec (sv : svalue)
      (msec : (int * int) list )
      (mpub : (int * int) list ) (pc : pc) : pc * pc =  
  (* let pc' = PCAnd (sv, pc) in
   * let pc'' = *)
  (* print_endline "split_msec"; *)
  let rec within_range sv msec =
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
       Si32.or_ hl (within_range sv msecs)
  in
  match sv with
  | SI32 vi32 ->
     let lrange = within_range vi32 mpub in (* Si32.not_ hrange in *)
     let hrange = Si32.not_ lrange in (* within_hrange vi32 msec in *)
     (PCAnd (SI32 hrange, pc), PCAnd (SI32 lrange, pc))
  | _ -> failwith "Address should be 32bit integer"


let select_condition v0 v1 v2 = (* (v0: svalue  v1: svalue): svalue = *)
  match v0, v1, v2 with
  (* v0 :: v2 :: v1 :: vs' -> *)
  | SI32 vi32, SI32 vi32_1, SI32 vi32_2 ->
     let one = Si32.one in
     let cond = Si32.eq vi32 one in
     SI32 ( Si32.ite cond vi32_1 vi32_2 )
  | SI32 vi32, SI64 vi64_1, SI64 vi64_2 ->
     let one = Si32.one in
     let cond = Si32.eq vi32 one in
     SI64 ( Si64.ite cond vi64_1 vi64_2 )
  (* | SF32 vf32, SF32 vf32_1, SF32 vf32_2 -> SF32 vf32
   * | SF64 vf64, SF64 vf64_1, SF64 vf64_2 -> SF64 vf64 *)
  | _ -> failwith "Type problem select"

let match_policy b1 b2 =
  match b1,b2 with
  | true, true | false, false -> true
  | _ -> false

(* Assert invariant *)
let rec assert_invar (lv: loopvar_t list) (c : config) : bool =
  match lv with
  | LocalVar (x, (true as is_low), mo) :: lvs ->
     (* print_endline "localvar"; *)
     let v = local c.frame x in
     let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in
     let is_low_new = Z3_solver.is_v_ct_unsat c.pc v mem in
     if match_policy is_low is_low_new then assert_invar lvs c
     else (
       (* print_endline (Int32.to_string x.it); *)
       false)

  | GlobalVar (x, (true as is_low), mo) :: lvs ->
     (* print_endline "globalvar"; *)
     let v = Sglobal.load (sglobal c.frame.inst x) in
     let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in
     let is_low_new = Z3_solver.is_v_ct_unsat c.pc v mem in
     if match_policy is_low is_low_new then assert_invar lvs c
     else false

  | StoreVar (addr, ty, sz, (true as is_low), mo) :: lvs ->
     (* print_endline "storevar"; *)
     let nv =
       (match sz with
        | None ->
           Eval_symbolic.eval_load ty addr (smemlen c.frame.inst)
             (Types.size ty) None
        | Some (sz) ->
           assert (packed_size sz <= Types.size ty);
           let n = packed_size sz in
           Eval_symbolic.eval_load ty addr (smemlen c.frame.inst) n None 
       )
     in
     (* let mem = smemory c.frame.inst (0l @@ Source.no_region) in *)

     let memtuple = (c.frame.inst.smemories, smemlen c.frame.inst) in
     let is_low_new = Z3_solver.is_v_ct_unsat c.pc nv memtuple in

     if match_policy is_low is_low_new then assert_invar lvs c
     else false
  (* if it is high, we don't mind if it got low *)
  | _ :: lvs -> assert_invar lvs c
  | [] -> true

(* let disable_ct = ref false *)       
  
(* Find variants that get updated in a loop *)


       


        
