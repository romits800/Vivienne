open Types


(* Values and operators *)

type ('i32, 'i64, 's32, 's64, 'f32, 'f64) op =
  I32 of 'i32 | I64 of 'i64 | S32 of 's32 | S64 of 's64 | F32 of 'f32 | F64 of 'f64

type value = (I32.t, I64.t, S32.t, S64.t, F32.t, F64.t) op


(* Typing *)

let type_of = function
  | I32 _ -> I32Type
  | I64 _ -> I64Type
  | S32 _ -> S32Type
  | S64 _ -> S64Type
  | F32 _ -> F32Type
  | F64 _ -> F64Type

let default_value = function
  | I32Type -> I32 I32.zero
  | I64Type -> I64 I64.zero
  | S32Type -> S32 S32.zero
  | S64Type -> S64 S64.zero
  | F32Type -> F32 F32.zero
  | F64Type -> F64 F64.zero


(* Conversion *)

let value_of_bool b = I32 (if b then 1l else 0l)
let value_of_sec_bool b = S32 (if b then 1l else 0l)

let string_of_value = function
  | I32 i -> I32.to_string_s i
  | I64 i -> I64.to_string_s i
  | S32 i -> S32.to_string_s i
  | S64 i -> S64.to_string_s i
  | F32 z -> F32.to_string z
  | F64 z -> F64.to_string z

let string_of_values = function
  | [v] -> string_of_value v
  | vs -> "[" ^ String.concat " " (List.map string_of_value vs) ^ "]"


(* Injection & projection *)

exception Value of value_type

module type ValueType =
sig
  type t
  val to_value : t -> value
  val of_value : value -> t (* raise Value *)
end

module I32Value =
struct
  type t = I32.t
  let to_value i = I32 i
  let of_value = function I32 i -> i | _ -> raise (Value I32Type)
end

module I64Value =
struct
  type t = I64.t
  let to_value i = I64 i
  let of_value = function I64 i -> i | _ -> raise (Value I64Type)
end

module S32Value =
struct
  type t = S32.t
  let to_value i = S32 i
  let of_value = function S32 i -> i | _ -> raise (Value S32Type)
end

module S64Value =
struct
  type t = S64.t
  let to_value i = S64 i
  let of_value = function S64 i -> i | _ -> raise (Value S64Type)
end


module F32Value =
struct
  type t = F32.t
  let to_value i = F32 i
  let of_value = function F32 z -> z | _ -> raise (Value F32Type)
end

module F64Value =
struct
  type t = F64.t
  let to_value i = F64 i
  let of_value = function F64 z -> z | _ -> raise (Value F64Type)
end
