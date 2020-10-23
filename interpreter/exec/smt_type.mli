type identifier =
  High of int | Low of int 

type func =
  | Id of string

  | Eq  | And | Or 
  | Ite | Not

  | Implies
  | Add | Sub | Mul | Div
  | Lt | Gt | Lte | Gte

  | BvAdd | BvSub | BvMul
                  
  | BvURem | BvSRem | BvSMod | BvDiv
  | BvShl | BvLShr | BvAShr
                   
  | BvOr | BvAnd | BvNand | BvNor | BvXNor | BvXor
  | BvNeg | BvNot
  | BvUle | BvUlt
  | BvSle | BvSlt 
  | BvUge | BvUgt
  | BvSge | BvSgt

type sort = 
  | Sort of identifier
  | SortApp of identifier * sort list
  | BitVecSort of int

type term = 
  | String of string
  | Int of int
  | Float of float
  | BitVec of int * int (* bool + number of bits *)
  | Const of identifier
  | Multi of term list * identifier * int (* term list, high/low, number_of_elements *)
  | Load of  term * int (* index, memory *)
  | Store of  term * term * int (* index, value, memory *)
  | App of func * term list
  | Let of string * term * term

type mergetype = PLUS_INF | MINUS_INF | Integer of int | Term of term
                                                     
(* let curr_num = ref 0 *)
             
(* val int_sort : sort
 * val bool_sort : sort
 * val array_sort : sort -> sort -> sort *)
val zero: term
val one: term

val int_to_intterm : int -> term
val int_to_bvterm : int -> int -> term
val float_to_term : float -> term
val get_high : unit -> identifier
val get_low : unit -> identifier

val is_low : term -> bool
val is_high : term -> bool
val is_int : term -> bool

val high_to_term : unit -> term
val low_to_term : unit -> term

val term_to_int : term -> int
val bool_to_term : bool -> term

val list_to_term : term list -> term
(* val const : identifier -> term *)
val equals : term -> term -> term
val load : term -> int -> term
val store : term -> term -> int -> term 
val and_ : term -> term -> term
val or_ : term -> term -> term
val not_ : term -> term
val ite : term -> term -> term -> term
val implies : term -> term -> term
val add : term -> term -> term
val sub : term -> term -> term
val mul : term -> term -> term
val div : term -> term -> term
val lt : term -> term -> term
val gt : term -> term -> term
val lte : term -> term -> term
val gte : term -> term -> term

val bv : int -> int -> term
val bvadd : term -> term -> term
val bvsub : term -> term -> term
val bvmul : term -> term -> term
val bvurem : term -> term -> term
val bvsrem : term -> term -> term
val bvsmod : term -> term -> term
val bvdiv: term -> term -> term (* doesn't exist *)
val bvshl : term -> term -> term
val bvlshr : term -> term -> term
val bvashr : term -> term -> term
val bvor : term -> term -> term
val bvand : term -> term -> term
val bvxor : term -> term -> term
val bvnand : term -> term -> term
val bvnor : term -> term -> term
val bvxnor : term -> term -> term
val bvneg : term -> term
val bvnot : term -> term

(* Not implemented *)
val bvule : term -> term -> term
val bvult : term -> term -> term
val bvuge : term -> term -> term
val bvugt : term -> term -> term
val bvsle : term -> term -> term
val bvslt : term -> term -> term
val bvsge : term -> term -> term
val bvsgt : term -> term -> term

val merge : term -> term -> (mergetype * mergetype) option
val merge_to_string :  mergetype -> string
val term_to_string : term -> string
