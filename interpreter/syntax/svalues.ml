open Types


(* Values and operators *)

type ('i32, 'i64, 'f32, 'f64) op =
  SI32 of 'i32 | SI64 of 'i64 | SF32 of 'f32 | SF64 of 'f64

type svalue = (Si32.t, Si64.t, F32.t, F64.t) op

            (* type svalue_d = Hi of (svalue *) 

(* Typing *)

let type_of = function
  | SI32 _ -> SI32Type
  | SI64 _ -> SI64Type
  | SF32 _ -> SF32Type
  | SF64 _ -> SF64Type

let default_value = function
  | SI32Type -> SI32 Si32.zero
  | SI64Type -> SI64 Si64.zero
  | SF32Type -> SF32 F32.zero
  | SF64Type -> SF64 F64.zero

let value_to_svalue_type = function
  | Types.I32Type -> SI32Type
  | Types.I64Type -> SI64Type
  | Types.F32Type -> SF32Type
  | Types.F64Type -> SF64Type

              
(* Conversion *)

let svalue32_of_bool v =
  match v with
  | SI32 _ -> v  
  | SI64 v -> SI32 (Si64.wrap 32 v)
  | _ -> failwith "not expected float in condition"

let string_of_value = function
  | SI32 i -> Si32.to_string_s i
  | SI64 i -> Si64.to_string_s i
  | SF32 z -> F32.to_string z
  | SF64 z -> F64.to_string z

let string_of_values = function
  | [v] -> string_of_value v
  | vs -> "[" ^ String.concat " " (List.map string_of_value vs) ^ "]"


(* Injection & projection *)

exception SValue of svalue_type

module type ValueType =
sig
  type t
  val to_value : t -> svalue
  val of_value : svalue -> t (* raise Value *)
end

module SI32Value =
struct
  type t = Si32.t
  let to_value i = SI32 i
  let of_value = function SI32 i -> i | _ -> raise (SValue SI32Type)
end

module SI64Value =
struct
  type t = Si64.t
  let to_value i = SI64 i
  let of_value = function SI64 i -> i | _ -> raise (SValue SI64Type)
end

module SF32Value =
struct
  type t = F32.t
  let to_value i = SF32 i
  let of_value = function SF32 z -> z | _ -> raise (SValue SF32Type)
end

module SF64Value =
struct
  type t = F64.t
  let to_value i = SF64 i
  let of_value = function SF64 z -> z | _ -> raise (SValue SF64Type)
end


let value_to_svalue = function
  | Values.I32 i32 -> SI32 (Si32.bv_of_int (Int32.to_int i32) 32)
  | Values.I64 i64 -> SI64 (Si64.bv_of_int (Int64.to_int i64) 64)
  | Values.F32 f32 -> SF32 f32
  | Values.F64 f64 -> SF64 f64
