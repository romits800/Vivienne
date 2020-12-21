(* Types *)

type value_type = I32Type | I64Type | F32Type | F64Type
type elem_type = FuncRefType
type stack_type = value_type list
type func_type = FuncType of stack_type * stack_type

type 'a limits = {min : 'a; max : 'a option}
type mutability = Immutable | Mutable
type table_type = TableType of Int32.t limits * elem_type
type memory_type = MemoryType of Int32.t limits
(* type memory_type = MemoryType of Int32.t limits *)
(* Symbolic types *)

type svalue_type = SI32Type | SI64Type | SF32Type | SF64Type
type smemory_type = SmemoryType of Int32.t limits

type sglobal_type = SglobalType of svalue_type * mutability
type global_type = GlobalType of value_type * mutability
type extern_type =
  | ExternFuncType of func_type
  | ExternTableType of table_type
  | ExternMemoryType of memory_type
  | ExternSmemoryType of smemory_type
  | ExternGlobalType of global_type
  | ExternSglobalType of sglobal_type

type pack_size = Pack8 | Pack16 | Pack32
type extension = SX | ZX



(* Symbolic types *)

type sec_type =   High of string | Low of string
                | Nat of string | Int of string | Float of string 

                        
let value_to_svalue_type = function
  | I32Type -> SI32Type
  | I64Type -> SI64Type
  | F32Type -> SF32Type
  | F64Type -> SF64Type
(* Attributes *)

let global_to_sglobal_type = function
  | GlobalType (v,mut) -> SglobalType (value_to_svalue_type v, mut)

let ssize = function
  | SI32Type | SF32Type -> 4
  | SI64Type | SF64Type -> 8

(* String conversion *)

let string_of_svalue_type = function
  | SI32Type -> "si32"
  | SI64Type -> "si64"
  | SF32Type -> "sf32"
  | SF64Type -> "sf64"

let string_of_svalue_types = function
  | [t] -> string_of_svalue_type t
  | ts -> "[" ^ String.concat " " (List.map string_of_svalue_type ts) ^ "]"


let string_of_sstack_type ts =
  "[" ^ String.concat " " (List.map string_of_svalue_type ts) ^ "]"


(* HERE *)
                    
(* Attributes *)

let size = function
  | I32Type | F32Type -> 4
  | I64Type | F64Type -> 8

let packed_size = function
  | Pack8 -> 1
  | Pack16 -> 2
  | Pack32 -> 4


(* Subtyping *)

let match_limits lim1 lim2 =
  I32.ge_u lim1.min lim2.min &&
  match lim1.max, lim2.max with
  | _, None -> true
  | None, Some _ -> false
  | Some i, Some j -> I32.le_u i j

let match_func_type ft1 ft2 =
  ft1 = ft2

let match_table_type (TableType (lim1, et1)) (TableType (lim2, et2)) =
  et1 = et2 && match_limits lim1 lim2

let match_memory_type (MemoryType lim1) (MemoryType lim2) =
  match_limits lim1 lim2

let match_smemory_type (SmemoryType lim1) (SmemoryType lim2) =
  match_limits lim1 lim2

let match_global_type gt1 gt2 =
  gt1 = gt2

let match_sglobal_type sgt1 sgt2 =
  sgt1 = sgt2

let match_extern_type et1 et2 =
  match et1, et2 with
  | ExternFuncType ft1, ExternFuncType ft2 -> match_func_type ft1 ft2
  | ExternTableType tt1, ExternTableType tt2 -> match_table_type tt1 tt2
  | ExternMemoryType mt1, ExternMemoryType mt2 -> match_memory_type mt1 mt2
  | ExternSmemoryType mt1, ExternSmemoryType mt2 -> match_smemory_type mt1 mt2
  | ExternGlobalType gt1, ExternGlobalType gt2 -> match_global_type gt1 gt2
  | ExternSglobalType gt1, ExternGlobalType gt2 ->
     let sg2 = global_to_sglobal_type gt2 in
     match_sglobal_type gt1 sg2
  | _, _ ->   print_endline "match_ext_type no match"; false


(* Filters *)

let funcs =
  Lib.List.map_filter (function ExternFuncType t -> Some t | _ -> None)
let tables =
  Lib.List.map_filter (function ExternTableType t -> Some t | _ -> None)
let memories =
  Lib.List.map_filter (function ExternMemoryType t -> Some t | _ -> None)
let smemories =
  Lib.List.map_filter (function ExternSmemoryType t -> Some t | _ -> None)
let globals =
  Lib.List.map_filter (function ExternGlobalType t -> Some t | _ -> None)


(* String conversion *)

let string_of_value_type = function
  | I32Type -> "i32"
  | I64Type -> "i64"
  | F32Type -> "f32"
  | F64Type -> "f64"

let string_of_value_types = function
  | [t] -> string_of_value_type t
  | ts -> "[" ^ String.concat " " (List.map string_of_value_type ts) ^ "]"

let string_of_elem_type = function
  | FuncRefType -> "funcref"

let string_of_limits {min; max} =
  I32.to_string_u min ^
  (match max with None -> "" | Some n -> " " ^ I32.to_string_u n)


let string_of_memory_type = function
  | MemoryType lim -> string_of_limits lim

let string_of_smemory_type = function
  | SmemoryType lim -> string_of_limits lim

let string_of_table_type = function
  | TableType (lim, t) -> string_of_limits lim ^ " " ^ string_of_elem_type t

let string_of_global_type = function
  | GlobalType (t, Immutable) -> string_of_value_type t
  | GlobalType (t, Mutable) -> "(mut " ^ string_of_value_type t ^ ")"

let string_of_sglobal_type = function
  | SglobalType (t, Immutable) -> string_of_svalue_type t
  | SglobalType (t, Mutable) -> "(mut " ^ string_of_svalue_type t ^ ")"

let string_of_stack_type ts =
  "[" ^ String.concat " " (List.map string_of_value_type ts) ^ "]"

let string_of_func_type (FuncType (ins, out)) =
  string_of_stack_type ins ^ " -> " ^ string_of_stack_type out

let string_of_extern_type = function
  | ExternFuncType ft -> "func " ^ string_of_func_type ft
  | ExternTableType tt -> "table " ^ string_of_table_type tt
  | ExternMemoryType mt -> "memory " ^ string_of_memory_type mt
  | ExternSmemoryType mt -> "smemory " ^ string_of_smemory_type mt
  | ExternGlobalType gt -> "global " ^ string_of_global_type gt
  | ExternSglobalType gt -> "sglobal " ^ string_of_sglobal_type gt

let memory_to_smemory_type = function
  | MemoryType lim -> SmemoryType lim 
