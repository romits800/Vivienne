open Types
open Svalues
(* open Values *)


(* Runtime type errors *)

exception TypeError of int * svalue * svalue_type

let of_arg f n v =
  try f v with SValue t -> raise (TypeError (n, v, t))


(* Int operators *)

module IntOp (IXX : Sym_int.S) (Value : ValueType with type t = IXX.t) =
struct
  open Ast.IntOp

  let to_value = Value.to_value
  let of_value = of_arg Value.of_value

  let unop op =
    let f = match op with
      | Clz -> IXX.clz
      | Ctz -> IXX.ctz
      | Popcnt -> IXX.popcnt
      | ExtendS sz -> failwith "Eval_symbolic: Not implemented"
      (* IXX.extend_s (8 * packed_size sz) *)
    in fun v -> to_value (f (of_value 1 v))

  let binop op =
    let f = match op with
      | Add -> IXX.add
      | Sub -> IXX.sub
      | Mul -> IXX.mul
      | DivS -> IXX.div_s
      | DivU -> IXX.div_u
      | RemS -> IXX.rem_s
      | RemU -> IXX.rem_u
      | And -> IXX.band
      | Or -> IXX.bor
      | Xor -> IXX.xor
      | Shl -> IXX.shl
      | ShrU -> IXX.shr_u
      | ShrS -> IXX.shr_s
      | Rotl -> IXX.rotl
      | Rotr -> IXX.rotr
    in fun v1 v2 -> to_value (f (of_value 1 v1) (of_value 2 v2))

  let cond op t1 t2 =
    let one = IXX.one in
    let zero = IXX.zero in
    let v = op t1 t2 in
    IXX.ite v one zero

  let testop op =
    let f = match op with
      | Eqz ->
         let zero = IXX.zero in
         cond IXX.eq zero
    in fun v -> to_value (f (of_value 1 v))

    
  let relop op =
    let f = match op with
      | Eq -> cond (IXX.eq)
      | Ne -> cond (IXX.ne)
      | LtS -> cond (IXX.lt_s)
      | LtU -> cond (IXX.lt_u)
      | LeS -> cond (IXX.le_s)
      | LeU -> cond (IXX.le_u)
      | GtS -> cond (IXX.gt_s)
      | GtU -> cond (IXX.gt_u)
      | GeS -> cond (IXX.ge_s)
      | GeU -> cond (IXX.ge_u)
    in fun v1 v2 -> to_value (f (of_value 1 v1) (of_value 2 v2))

end

module SI32Op = IntOp (Si32) (Svalues.SI32Value)
module SI64Op = IntOp (Si64) (Svalues.SI64Value)


(* Float operators *)

module FloatOp (FXX : Float.S) (Value : ValueType with type t = FXX.t) =
struct
  open Ast.FloatOp

  let to_value = Value.to_value
  let of_value = of_arg Value.of_value

  let unop op =
    let f = match op with
      | Neg -> FXX.neg
      | Abs -> FXX.abs
      | Sqrt  -> FXX.sqrt
      | Ceil -> FXX.ceil
      | Floor -> FXX.floor
      | Trunc -> FXX.trunc
      | Nearest -> FXX.nearest
    in fun v -> to_value (f (of_value 1 v))

  let binop op =
    let f = match op with
      | Add -> FXX.add
      | Sub -> FXX.sub
      | Mul -> FXX.mul
      | Div -> FXX.div
      | Min -> FXX.min
      | Max -> FXX.max
      | CopySign -> FXX.copysign
    in fun v1 v2 -> to_value (f (of_value 1 v1) (of_value 2 v2))

  let testop op = assert false

  let relop op =
    let f = match op with
      | Eq -> FXX.eq
      | Ne -> FXX.ne
      | Lt -> FXX.lt
      | Le -> FXX.le
      | Gt -> FXX.gt
      | Ge -> FXX.ge
    in fun v1 v2 -> to_value ( if (f (of_value 1 v1) (of_value 2 v2)) then FXX.of_float 1. else FXX.of_float 0.)
end

module SF32Op = FloatOp (F32) (Svalues.SF32Value)
module SF64Op = FloatOp (F64) (Svalues.SF64Value)


(* Conversion operators *)

module I32CvtOp =
struct
  (* open Ast.IntOp *)

  let cvtop op v =
    raise (TypeError (1, v, SI32Type))
    (* match op with
     * | WrapI64 -> I32 (I32_convert.wrap_i64 (I64Op.of_value 1 v))
     * | TruncSF32 -> I32 (I32_convert.trunc_f32_s (F32Op.of_value 1 v))
     * | TruncUF32 -> I32 (I32_convert.trunc_f32_u (F32Op.of_value 1 v))
     * | TruncSF64 -> I32 (I32_convert.trunc_f64_s (F64Op.of_value 1 v))
     * | TruncUF64 -> I32 (I32_convert.trunc_f64_u (F64Op.of_value 1 v))
     * | TruncSatSF32 -> I32 (I32_convert.trunc_sat_f32_s (F32Op.of_value 1 v))
     * | TruncSatUF32 -> I32 (I32_convert.trunc_sat_f32_u (F32Op.of_value 1 v))
     * | TruncSatSF64 -> I32 (I32_convert.trunc_sat_f64_s (F64Op.of_value 1 v))
     * | TruncSatUF64 -> I32 (I32_convert.trunc_sat_f64_u (F64Op.of_value 1 v))
     * | ReinterpretFloat -> I32 (I32_convert.reinterpret_f32 (F32Op.of_value 1 v))
     * | ExtendSI32 -> raise (TypeError (1, v, I32Type))
     * | ExtendUI32 -> raise (TypeError (1, v, I32Type)) *)
end

module I64CvtOp =
struct
  (* open Ast.IntOp *)

  let cvtop op v =
    raise (TypeError (1, v, SI64Type))
    (* match op with
     * | ExtendSI32 -> I64 (I64_convert.extend_i32_s (I32Op.of_value 1 v))
     * | ExtendUI32 -> I64 (I64_convert.extend_i32_u (I32Op.of_value 1 v))
     * | TruncSF32 -> I64 (I64_convert.trunc_f32_s (F32Op.of_value 1 v))
     * | TruncUF32 -> I64 (I64_convert.trunc_f32_u (F32Op.of_value 1 v))
     * | TruncSF64 -> I64 (I64_convert.trunc_f64_s (F64Op.of_value 1 v))
     * | TruncUF64 -> I64 (I64_convert.trunc_f64_u (F64Op.of_value 1 v))
     * | TruncSatSF32 -> I64 (I64_convert.trunc_sat_f32_s (F32Op.of_value 1 v))
     * | TruncSatUF32 -> I64 (I64_convert.trunc_sat_f32_u (F32Op.of_value 1 v))
     * | TruncSatSF64 -> I64 (I64_convert.trunc_sat_f64_s (F64Op.of_value 1 v))
     * | TruncSatUF64 -> I64 (I64_convert.trunc_sat_f64_u (F64Op.of_value 1 v))
     * | ReinterpretFloat -> I64 (I64_convert.reinterpret_f64 (F64Op.of_value 1 v))
     * | WrapI64 -> raise (TypeError (1, v, I64Type)) *)
end

module F32CvtOp =
struct
  (* open Ast.FloatOp *)

  let cvtop op v =
    raise (TypeError (1, v, SF32Type))
    (* match op with
     * | DemoteF64 -> F32 (F32_convert.demote_f64 (F64Op.of_value 1 v))
     * | ConvertSI32 -> F32 (F32_convert.convert_i32_s (I32Op.of_value 1 v))
     * | ConvertUI32 -> F32 (F32_convert.convert_i32_u (I32Op.of_value 1 v))
     * | ConvertSI64 -> F32 (F32_convert.convert_i64_s (I64Op.of_value 1 v))
     * | ConvertUI64 -> F32 (F32_convert.convert_i64_u (I64Op.of_value 1 v))
     * | ReinterpretInt -> F32 (F32_convert.reinterpret_i32 (I32Op.of_value 1 v))
     * | PromoteF32 -> raise (TypeError (1, v, F32Type)) *)
end

module F64CvtOp =
struct
  (* open Ast.FloatOp *)

  let cvtop op v =
    raise (TypeError (1, v, SF64Type))
    (* match op with *)
    (* | PromoteF32 -> F64 (F64_convert.promote_f32 (F32Op.of_value 1 v))
     * | ConvertSI32 -> F64 (F64_convert.convert_i32_s (I32Op.of_value 1 v))
     * | ConvertUI32 -> F64 (F64_convert.convert_i32_u (I32Op.of_value 1 v))
     * | ConvertSI64 -> F64 (F64_convert.convert_i64_s (I64Op.of_value 1 v))
     * | ConvertUI64 -> F64 (F64_convert.convert_i64_u (I64Op.of_value 1 v))
     * | ReinterpretInt -> F64 (F64_convert.reinterpret_i64 (I64Op.of_value 1 v))
     * | DemoteF64 -> raise (TypeError (1, v, F64Type)) *)
end


(* Dispatch *)

let op i32 i64 f32 f64 = function
  | Values.I32 x -> i32 x
  | Values.I64 x -> i64 x
  | Values.F32 x -> f32 x
  | Values.F64 x -> f64 x

let eval_unop = op SI32Op.unop SI64Op.unop SF32Op.unop SF64Op.unop
let eval_binop = op SI32Op.binop SI64Op.binop SF32Op.binop SF64Op.binop
let eval_testop = op SI32Op.testop SI64Op.testop SF32Op.testop SF64Op.testop
let eval_relop = op SI32Op.relop SI64Op.relop SF32Op.relop SF64Op.relop
let eval_cvtop = op I32CvtOp.cvtop I64CvtOp.cvtop F32CvtOp.cvtop F64CvtOp.cvtop




let eval_load ty ad i =
  match ty,ad with 
  | I32Type, SI32 a -> SI32 (Si32.load a i)
  | I64Type, SI32 a -> SI64 (Si64.load a i)
  | _ -> failwith "Floats not implemented."


let eval_store ty ad sv i =
  match ty,ad,sv with 
  | I32Type, SI32 a, SI32 v -> SI32 (Si32.store a v i)
  | I64Type, SI32 a, SI64 v -> SI64 (Si64.store a v i)
  | _ -> failwith "Floats not implemented."


let create_new_hstore a =
  let value = Si32.of_high() in
  let index = Si32.bv_of_int a 32 in
  let st = SI32 (Si32.store index value 0) in
  st

let create_new_lstore a =
  let value = Si32.of_low() in
  let index = Si32.bv_of_int a 32 in
  let st = SI32 (Si32.store index value 0) in
  st

    (* match ty,ad,sv with 
   * | I32Type, SI32 a, SI32 v -> SI32 (Si32.store a v i)
   * | I64Type, SI32 a, SI64 v -> SI64 (Si64.store a v i)
   * | _ -> failwith "Floats not implemented." *)


(* let calc_address ty sv i =
 *   match ty with 
 *   | I32Type -> SI32 (Si32.load sv i)
 *   | I64Type -> SI64 (Si64.load sv i)
 *   | _ -> failwith "Floats not implemented." *)
