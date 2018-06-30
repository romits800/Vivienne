module Bits_Integer : sig
  val and_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val or_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftl : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftr : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val test_bit : Big_int.big_int -> Big_int.big_int -> bool
end = struct

let and_pninteger bi1 bi2 =
  Big_int.and_big_int bi1
    (Big_int.xor_big_int
      (Big_int.pred_big_int
        (Big_int.shift_left_big_int Big_int.unit_big_int
           (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
      (Big_int.pred_big_int (Big_int.minus_big_int bi2)));;

let or_pninteger bi1 bi2 =
  Big_int.pred_big_int (Big_int.minus_big_int
    (Big_int.and_big_int
      (Big_int.xor_big_int
         (Big_int.pred_big_int
           (Big_int.shift_left_big_int Big_int.unit_big_int
              (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                   (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
         bi1)
      (Big_int.pred_big_int (Big_int.minus_big_int bi2))));;

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Big_int.shift_left_big_int x (Big_int.int_of_big_int n);;

let shiftr x n = Big_int.shift_right_big_int x (Big_int.int_of_big_int n);;

let test_bit x n = 
  Big_int.eq_big_int 
    (Big_int.extract_big_int x (Big_int.int_of_big_int n) 1) 
    Big_int.unit_big_int

end;; (*struct Bits_Integer*)

module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

end;; (*struct Orderings*)

module Arith : sig
  type nat = Nat of Big_int.big_int
  type num = One | Bit0 of num | Bit1 of num
  val one_nata : nat
  type 'a one = {one : 'a}
  val one : 'a one -> 'a
  val one_nat : nat one
  val integer_of_nat : nat -> Big_int.big_int
  val times_nata : nat -> nat -> nat
  type 'a times = {times : 'a -> 'a -> 'a}
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power = {one_power : 'a one; times_power : 'a times}
  val times_nat : nat times
  val power_nat : nat power
  val ord_integer : Big_int.big_int Orderings.ord
  val plus_nat : nat -> nat -> nat
  val suc : nat -> nat
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val zero_nat : nat
  val power : 'a power -> 'a -> nat -> 'a
  val less_nat : nat -> nat -> bool
  val nat_of_integer : Big_int.big_int -> nat
  val less_eq_nat : nat -> nat -> bool
end = struct

type nat = Nat of Big_int.big_int;;

type num = One | Bit0 of num | Bit1 of num;;

let one_nata : nat = Nat (Big_int.big_int_of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec integer_of_nat (Nat x) = x;;

let rec times_nata
  m n = Nat (Big_int.mult_big_int (integer_of_nat m) (integer_of_nat n));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_nat = ({times = times_nata} : nat times);;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

let ord_integer =
  ({Orderings.less_eq = Big_int.le_big_int; Orderings.less = Big_int.lt_big_int}
    : Big_int.big_int Orderings.ord);;

let rec plus_nat
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nata;;

let rec minus_nat
  m n = Nat (Orderings.max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

let rec equal_nat
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

let zero_nat : nat = Nat Big_int.zero_big_int;;

let rec power _A
  a n = (if equal_nat n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nata)));;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

let rec nat_of_integer
  k = Nat (Orderings.max ord_integer Big_int.zero_big_int k);;

let rec less_eq_nat
  m n = Big_int.le_big_int (integer_of_nat m) (integer_of_nat n);;

end;; (*struct Arith*)

module List : sig
  val nth : 'a list -> Arith.nat -> 'a
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val take : Arith.nat -> 'a list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val gen_length : Arith.nat -> 'a list -> Arith.nat
  val size_list : 'a list -> Arith.nat
  val equal_list : 'a HOL.equal -> 'a list -> 'a list -> bool
end = struct

let rec nth
  (x :: xs) n =
    (if Arith.equal_nat n Arith.zero_nat then x
      else nth xs (Arith.minus_nat n Arith.one_nata));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if Arith.equal_nat n Arith.zero_nat then []
          else x :: take (Arith.minus_nat n Arith.one_nata) xs);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec gen_length
  n x1 = match n, x1 with n, x :: xs -> gen_length (Arith.suc n) xs
    | n, [] -> n;;

let rec size_list x = gen_length Arith.zero_nat x;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> HOL.eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

end;; (*struct List*)

module Option : sig
  val is_none : 'a option -> bool
  val map_option : ('a -> 'b) -> 'a option -> 'b option
end = struct

let rec is_none = function Some x -> false
                  | None -> true;;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

end;; (*struct Option*)

module Wasm_Ast : sig
  type sec = Secret | Public
  val equal_sec : sec -> sec -> bool
  type t = T_i32 of sec | T_i64 of sec | T_f32 | T_f64
  val equal_ta : t -> t -> bool
  val equal_t : t HOL.equal
  type v = ConstInt32 of sec * I32.t | ConstInt64 of sec * I64.t |
    ConstFloat32 of F32.t | ConstFloat64 of F64.t
  type sx = S | U
  type tf = Tf of t list * t list
  type tp = Tp_i8 | Tp_i16 | Tp_i32
  type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx
  type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef
  type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl
    | Shr of sx | Rotl | Rotr
  type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign
  type unop_i = Clz | Ctz | Popcnt
  type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt
  type testop = Eqz
  type cvtop = Convert | Reinterpret | Classify | Declassify
  type b_e = Unreachable | Nop | Drop | Select of sec | Block of tf * b_e list |
    Loop of tf * b_e list | If of tf * b_e list * b_e list | Br of Arith.nat |
    Br_if of Arith.nat | Br_table of Arith.nat list * Arith.nat | Return |
    Call of Arith.nat | Call_indirect of Arith.nat | Get_local of Arith.nat |
    Set_local of Arith.nat | Tee_local of Arith.nat | Get_global of Arith.nat |
    Set_global of Arith.nat |
    Load of t * (tp * sx) option * Arith.nat * Arith.nat |
    Store of t * tp option * Arith.nat * Arith.nat | Current_memory |
    Grow_memory | EConst of v | Unop_i of t * unop_i | Unop_f of t * unop_f |
    Binop_i of t * binop_i | Binop_f of t * binop_f | Testop of t * testop |
    Relop_i of t * relop_i | Relop_f of t * relop_f |
    Cvtop of t * cvtop * t * sx option
  type mut = T_immut | T_mut
  type trust = Trusted | Untrusted
  type 'a tg_ext = Tg_ext of mut * t * 'a
  type 'a t_context_ext =
    T_context_ext of
      trust * (trust * tf) list * (trust * tf) list * unit tg_ext list *
        Arith.nat option * (Arith.nat * sec) option * t list * (t list) list *
        (t list) option * 'a
  val tg_t : 'a tg_ext -> t
  val tg_mut : 'a tg_ext -> mut
  val label : 'a t_context_ext -> (t list) list
  val local : 'a t_context_ext -> t list
  val table : 'a t_context_ext -> Arith.nat option
  val func_t : 'a t_context_ext -> (trust * tf) list
  val global : 'a t_context_ext -> unit tg_ext list
  val memory : 'a t_context_ext -> (Arith.nat * sec) option
  val return : 'a t_context_ext -> (t list) option
  val trust_t : 'a t_context_ext -> trust
  val types_t : 'a t_context_ext -> (trust * tf) list
  val label_update :
    ((t list) list -> (t list) list) -> 'a t_context_ext -> 'a t_context_ext
  val equal_mut : mut -> mut -> bool
  val equal_trust : trust -> trust -> bool
end = struct

type sec = Secret | Public;;

let rec equal_sec x0 x1 = match x0, x1 with Secret, Public -> false
                    | Public, Secret -> false
                    | Public, Public -> true
                    | Secret, Secret -> true;;

type t = T_i32 of sec | T_i64 of sec | T_f32 | T_f64;;

let rec equal_ta x0 x1 = match x0, x1 with T_f32, T_f64 -> false
                   | T_f64, T_f32 -> false
                   | T_i64 x2, T_f64 -> false
                   | T_f64, T_i64 x2 -> false
                   | T_i64 x2, T_f32 -> false
                   | T_f32, T_i64 x2 -> false
                   | T_i32 x1, T_f64 -> false
                   | T_f64, T_i32 x1 -> false
                   | T_i32 x1, T_f32 -> false
                   | T_f32, T_i32 x1 -> false
                   | T_i32 x1, T_i64 x2 -> false
                   | T_i64 x2, T_i32 x1 -> false
                   | T_i64 x2, T_i64 y2 -> equal_sec x2 y2
                   | T_i32 x1, T_i32 y1 -> equal_sec x1 y1
                   | T_f64, T_f64 -> true
                   | T_f32, T_f32 -> true;;

let equal_t = ({HOL.equal = equal_ta} : t HOL.equal);;

type v = ConstInt32 of sec * I32.t | ConstInt64 of sec * I64.t |
  ConstFloat32 of F32.t | ConstFloat64 of F64.t;;

type sx = S | U;;

type tf = Tf of t list * t list;;

type tp = Tp_i8 | Tp_i16 | Tp_i32;;

type relop_i = Eq | Ne | Lt of sx | Gt of sx | Le of sx | Ge of sx;;

type relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef;;

type binop_i = Add | Sub | Mul | Div of sx | Rem of sx | And | Or | Xor | Shl |
  Shr of sx | Rotl | Rotr;;

type binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign;;

type unop_i = Clz | Ctz | Popcnt;;

type unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt;;

type testop = Eqz;;

type cvtop = Convert | Reinterpret | Classify | Declassify;;

type b_e = Unreachable | Nop | Drop | Select of sec | Block of tf * b_e list |
  Loop of tf * b_e list | If of tf * b_e list * b_e list | Br of Arith.nat |
  Br_if of Arith.nat | Br_table of Arith.nat list * Arith.nat | Return |
  Call of Arith.nat | Call_indirect of Arith.nat | Get_local of Arith.nat |
  Set_local of Arith.nat | Tee_local of Arith.nat | Get_global of Arith.nat |
  Set_global of Arith.nat | Load of t * (tp * sx) option * Arith.nat * Arith.nat
  | Store of t * tp option * Arith.nat * Arith.nat | Current_memory |
  Grow_memory | EConst of v | Unop_i of t * unop_i | Unop_f of t * unop_f |
  Binop_i of t * binop_i | Binop_f of t * binop_f | Testop of t * testop |
  Relop_i of t * relop_i | Relop_f of t * relop_f |
  Cvtop of t * cvtop * t * sx option;;

type mut = T_immut | T_mut;;

type trust = Trusted | Untrusted;;

type 'a tg_ext = Tg_ext of mut * t * 'a;;

type 'a t_context_ext =
  T_context_ext of
    trust * (trust * tf) list * (trust * tf) list * unit tg_ext list *
      Arith.nat option * (Arith.nat * sec) option * t list * (t list) list *
      (t list) option * 'a;;

let rec tg_t (Tg_ext (tg_mut, tg_t, more)) = tg_t;;

let rec tg_mut (Tg_ext (tg_mut, tg_t, more)) = tg_mut;;

let rec label
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = label;;

let rec local
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = local;;

let rec table
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = table;;

let rec func_t
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = func_t;;

let rec global
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = global;;

let rec memory
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = memory;;

let rec return
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = return;;

let rec trust_t
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = trust_t;;

let rec types_t
  (T_context_ext
    (trust_t, types_t, func_t, global, table, memory, local, label, return,
      more))
    = types_t;;

let rec label_update
  labela
    (T_context_ext
      (trust_t, types_t, func_t, global, table, memory, local, label, return,
        more))
    = T_context_ext
        (trust_t, types_t, func_t, global, table, memory, local, labela label,
          return, more);;

let rec equal_mut x0 x1 = match x0, x1 with T_immut, T_mut -> false
                    | T_mut, T_immut -> false
                    | T_mut, T_mut -> true
                    | T_immut, T_immut -> true;;

let rec equal_trust x0 x1 = match x0, x1 with Trusted, Untrusted -> false
                      | Untrusted, Trusted -> false
                      | Untrusted, Untrusted -> true
                      | Trusted, Trusted -> true;;

end;; (*struct Wasm_Ast*)

module Product_Type : sig
  val fst : 'a * 'b -> 'a
  val equal_bool : bool -> bool -> bool
end = struct

let rec fst (x1, x2) = x1;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

end;; (*struct Product_Type*)

module Wasm_Base_Defs : sig
  val t_sec : Wasm_Ast.t -> Wasm_Ast.sec
  val is_mut : unit Wasm_Ast.tg_ext -> bool
  val typeof : Wasm_Ast.v -> Wasm_Ast.t
  val is_int_t : Wasm_Ast.t -> bool
  val t_length : Wasm_Ast.t -> Arith.nat
  val tp_length : Wasm_Ast.tp -> Arith.nat
  val classify_t : Wasm_Ast.t -> Wasm_Ast.t
  val is_float_t : Wasm_Ast.t -> bool
  val declassify_t : Wasm_Ast.t -> Wasm_Ast.t
  val option_projl : ('a * 'b) option -> 'a option
  val safe_binop_i : Wasm_Ast.binop_i -> bool
  val trust_compat : Wasm_Ast.trust -> Wasm_Ast.trust -> bool
  val load_store_t_bounds :
    Arith.nat -> Wasm_Ast.tp option -> Wasm_Ast.t -> bool
end = struct

let rec t_sec
  t = (match t with Wasm_Ast.T_i32 sec -> sec | Wasm_Ast.T_i64 sec -> sec
        | Wasm_Ast.T_f32 -> Wasm_Ast.Public
        | Wasm_Ast.T_f64 -> Wasm_Ast.Public);;

let rec is_mut tg = Wasm_Ast.equal_mut (Wasm_Ast.tg_mut tg) Wasm_Ast.T_mut;;

let rec typeof
  v = (match v with Wasm_Ast.ConstInt32 (sec, _) -> Wasm_Ast.T_i32 sec
        | Wasm_Ast.ConstInt64 (sec, _) -> Wasm_Ast.T_i64 sec
        | Wasm_Ast.ConstFloat32 _ -> Wasm_Ast.T_f32
        | Wasm_Ast.ConstFloat64 _ -> Wasm_Ast.T_f64);;

let rec is_int_t
  t = (match t with Wasm_Ast.T_i32 _ -> true | Wasm_Ast.T_i64 _ -> true
        | Wasm_Ast.T_f32 -> false | Wasm_Ast.T_f64 -> false);;

let rec t_length
  t = (match t
        with Wasm_Ast.T_i32 _ -> Arith.nat_of_integer (Big_int.big_int_of_int 4)
        | Wasm_Ast.T_i64 _ -> Arith.nat_of_integer (Big_int.big_int_of_int 8)
        | Wasm_Ast.T_f32 -> Arith.nat_of_integer (Big_int.big_int_of_int 4)
        | Wasm_Ast.T_f64 -> Arith.nat_of_integer (Big_int.big_int_of_int 8));;

let rec tp_length
  tp = (match tp with Wasm_Ast.Tp_i8 -> Arith.one_nata
         | Wasm_Ast.Tp_i16 -> Arith.nat_of_integer (Big_int.big_int_of_int 2)
         | Wasm_Ast.Tp_i32 -> Arith.nat_of_integer (Big_int.big_int_of_int 4));;

let rec classify_t
  t = (match t with Wasm_Ast.T_i32 _ -> Wasm_Ast.T_i32 Wasm_Ast.Secret
        | Wasm_Ast.T_i64 _ -> Wasm_Ast.T_i64 Wasm_Ast.Secret
        | Wasm_Ast.T_f32 -> Wasm_Ast.T_f32 | Wasm_Ast.T_f64 -> Wasm_Ast.T_f64);;

let rec is_float_t
  t = (match t with Wasm_Ast.T_i32 _ -> false | Wasm_Ast.T_i64 _ -> false
        | Wasm_Ast.T_f32 -> true | Wasm_Ast.T_f64 -> true);;

let rec declassify_t
  t = (match t with Wasm_Ast.T_i32 _ -> Wasm_Ast.T_i32 Wasm_Ast.Public
        | Wasm_Ast.T_i64 _ -> Wasm_Ast.T_i64 Wasm_Ast.Public
        | Wasm_Ast.T_f32 -> Wasm_Ast.T_f32 | Wasm_Ast.T_f64 -> Wasm_Ast.T_f64);;

let rec option_projl x = Option.map_option Product_Type.fst x;;

let rec safe_binop_i
  bop = (match bop with Wasm_Ast.Add -> true | Wasm_Ast.Sub -> true
          | Wasm_Ast.Mul -> true | Wasm_Ast.Div _ -> false
          | Wasm_Ast.Rem _ -> false | Wasm_Ast.And -> true | Wasm_Ast.Or -> true
          | Wasm_Ast.Xor -> true | Wasm_Ast.Shl -> true | Wasm_Ast.Shr _ -> true
          | Wasm_Ast.Rotl -> true | Wasm_Ast.Rotr -> true);;

let rec trust_compat
  tra tr =
    Wasm_Ast.equal_trust tra Wasm_Ast.Trusted ||
      Wasm_Ast.equal_trust tra Wasm_Ast.Untrusted &&
        Wasm_Ast.equal_trust tr Wasm_Ast.Untrusted;;

let rec load_store_t_bounds
  a tp t =
    (match tp
      with None ->
        Arith.less_eq_nat
          (Arith.power Arith.power_nat
            (Arith.nat_of_integer (Big_int.big_int_of_int 2)) a)
          (t_length t)
      | Some tpa ->
        Arith.less_eq_nat
          (Arith.power Arith.power_nat
            (Arith.nat_of_integer (Big_int.big_int_of_int 2)) a)
          (tp_length tpa) &&
          (Arith.less_nat (tp_length tpa) (t_length t) && is_int_t t));;

end;; (*struct Wasm_Base_Defs*)

module Wasm_Checker_Types : sig
  type ct = TAny | TSecret | TSome of Wasm_Ast.t
  type checker_type = TopType of ct list | Type of Wasm_Ast.t list | Bot
  val can_secret_ct : ct -> bool
  val ct_eq : ct -> ct -> bool
  val sec_ct : Wasm_Ast.sec -> ct
  val to_ct_list : Wasm_Ast.t list -> ct list
  val ct_prefix : ct list -> ct list -> bool
  val ct_suffix : ct list -> ct list -> bool
  val consume : checker_type -> ct list -> checker_type
  val produce : checker_type -> checker_type -> checker_type
  val ens_sec_ct : Wasm_Ast.sec -> ct -> ct
  val type_update : checker_type -> ct list -> checker_type -> checker_type
  val c_types_agree : checker_type -> Wasm_Ast.t list -> bool
  val select_return_top : Wasm_Ast.sec -> ct list -> ct -> ct -> checker_type
  val type_update_select : Wasm_Ast.sec -> checker_type -> checker_type
end = struct

type ct = TAny | TSecret | TSome of Wasm_Ast.t;;

type checker_type = TopType of ct list | Type of Wasm_Ast.t list | Bot;;

let rec can_secret_ct
  = function
    TSome t -> Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t) Wasm_Ast.Secret
    | TAny -> true
    | TSecret -> true;;

let rec ct_eq
  x0 ct = match x0, ct with TSome ta, TSome t -> Wasm_Ast.equal_ta ta t
    | TSecret, ct -> can_secret_ct ct
    | TAny, TSecret -> can_secret_ct TAny
    | TSome v, TSecret -> can_secret_ct (TSome v)
    | TAny, TAny -> true
    | TAny, TSome v -> true
    | TSome v, TAny -> true;;

let rec sec_ct = function Wasm_Ast.Public -> TAny
                 | Wasm_Ast.Secret -> TSecret;;

let rec to_ct_list ts = List.map (fun a -> TSome a) ts;;

let rec ct_prefix
  x0 xs = match x0, xs with x :: xs, y :: ys -> ct_eq x y && ct_prefix xs ys
    | x :: xs, [] -> false
    | [], xs -> true;;

let rec ct_suffix xs ys = ct_prefix (List.rev xs) (List.rev ys);;

let rec consume
  x0 cons = match x0, cons with
    Type ts, cons ->
      (if ct_suffix cons (to_ct_list ts)
        then Type (List.take
                    (Arith.minus_nat (List.size_list ts) (List.size_list cons))
                    ts)
        else Bot)
    | TopType cts, cons ->
        (if ct_suffix cons cts
          then TopType
                 (List.take
                   (Arith.minus_nat (List.size_list cts) (List.size_list cons))
                   cts)
          else (if ct_suffix cts cons then TopType [] else Bot))
    | Bot, uv -> Bot;;

let rec produce
  uu uv = match uu, uv with
    TopType tsa, Type ts -> TopType (tsa @ to_ct_list ts)
    | Type tsa, Type ts -> Type (tsa @ ts)
    | Type tsa, TopType ts -> TopType ts
    | TopType tsa, TopType ts -> TopType ts
    | Type v, Bot -> Bot
    | Bot, uv -> Bot
    | uu, Bot -> Bot;;

let rec ens_sec_ct uu ct = match uu, ct with Wasm_Ast.Secret, TAny -> TSecret
                     | Wasm_Ast.Public, ct -> ct
                     | uu, TSecret -> TSecret
                     | uu, TSome v -> TSome v;;

let rec type_update
  curr_type cons prods = produce (consume curr_type cons) prods;;

let rec c_types_agree
  x0 ts = match x0, ts with
    Type tsa, ts -> List.equal_list Wasm_Ast.equal_t tsa ts
    | TopType tsa, ts -> ct_suffix tsa (to_ct_list ts)
    | Bot, uu -> false;;

let rec select_return_top
  sec ts ct1 x3 = match sec, ts, ct1, x3 with
    sec, ts, ct1, TAny ->
      (if (if Wasm_Ast.equal_sec sec Wasm_Ast.Secret then can_secret_ct ct1
            else true)
        then TopType
               (List.take
                  (Arith.minus_nat (List.size_list ts)
                    (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
                  ts @
                 [ens_sec_ct sec ct1])
        else Bot)
    | sec, ts, TAny, TSecret ->
        (if (if Wasm_Ast.equal_sec sec Wasm_Ast.Secret
              then can_secret_ct TSecret else true)
          then TopType
                 (List.take
                    (Arith.minus_nat (List.size_list ts)
                      (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
                    ts @
                   [ens_sec_ct sec TSecret])
          else Bot)
    | sec, ts, TAny, TSome v ->
        (if (if Wasm_Ast.equal_sec sec Wasm_Ast.Secret
              then can_secret_ct (TSome v) else true)
          then TopType
                 (List.take
                    (Arith.minus_nat (List.size_list ts)
                      (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
                    ts @
                   [ens_sec_ct sec (TSome v)])
          else Bot)
    | sec, ts, TSecret, TSecret ->
        (if can_secret_ct TSecret
          then TopType
                 (List.take
                    (Arith.minus_nat (List.size_list ts)
                      (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
                    ts @
                   [ens_sec_ct sec TSecret])
          else Bot)
    | sec, ts, TSome v, TSecret ->
        (if can_secret_ct (TSome v)
          then TopType
                 (List.take
                    (Arith.minus_nat (List.size_list ts)
                      (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
                    ts @
                   [ens_sec_ct sec (TSome v)])
          else Bot)
    | sec, ts, TSecret, TSome v ->
        (if can_secret_ct (TSome v)
          then TopType
                 (List.take
                    (Arith.minus_nat (List.size_list ts)
                      (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
                    ts @
                   [TSome v])
          else Bot)
    | sec, ts, TSome t1, TSome t2 ->
        (if Wasm_Ast.equal_ta t1 t2 &&
              (if Wasm_Ast.equal_sec sec Wasm_Ast.Secret
                then Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t1)
                       Wasm_Ast.Secret
                else true)
          then TopType
                 (List.take
                    (Arith.minus_nat (List.size_list ts)
                      (Arith.nat_of_integer (Big_int.big_int_of_int 3)))
                    ts @
                   [TSome t1])
          else Bot);;

let rec type_update_select
  sec x1 = match sec, x1 with
    sec, Type ts ->
      (if Arith.less_eq_nat (Arith.nat_of_integer (Big_int.big_int_of_int 3))
            (List.size_list ts) &&
            (Wasm_Ast.equal_ta
               (List.nth ts
                 (Arith.minus_nat (List.size_list ts)
                   (Arith.nat_of_integer (Big_int.big_int_of_int 2))))
               (List.nth ts
                 (Arith.minus_nat (List.size_list ts)
                   (Arith.nat_of_integer (Big_int.big_int_of_int 3)))) &&
              (if Wasm_Ast.equal_sec sec Wasm_Ast.Secret
                then Wasm_Ast.equal_sec
                       (Wasm_Base_Defs.t_sec
                         (List.nth ts
                           (Arith.minus_nat (List.size_list ts)
                             (Arith.nat_of_integer
                               (Big_int.big_int_of_int 2)))))
                       Wasm_Ast.Secret
                else true))
        then consume (Type ts) [TAny; TSome (Wasm_Ast.T_i32 sec)] else Bot)
    | sec, TopType ts ->
        (if Arith.equal_nat (List.size_list ts) Arith.zero_nat
          then TopType [sec_ct sec]
          else (if Arith.equal_nat
                     (Arith.minus_nat (List.size_list ts) Arith.one_nata)
                     Arith.zero_nat
                 then type_update (TopType ts) [TSome (Wasm_Ast.T_i32 sec)]
                        (TopType [sec_ct sec])
                 else (if Arith.equal_nat
                            (Arith.minus_nat
                              (Arith.minus_nat (List.size_list ts)
                                Arith.one_nata)
                              Arith.one_nata)
                            Arith.zero_nat
                        then type_update (TopType ts)
                               [sec_ct sec; TSome (Wasm_Ast.T_i32 sec)]
                               (TopType
                                 [ens_sec_ct sec
                                    (List.nth ts
                                      (Arith.minus_nat (List.size_list ts)
(Arith.nat_of_integer (Big_int.big_int_of_int 2))))])
                        else type_update (TopType ts)
                               [sec_ct sec; sec_ct sec;
                                 TSome (Wasm_Ast.T_i32 sec)]
                               (select_return_top sec ts
                                 (List.nth ts
                                   (Arith.minus_nat (List.size_list ts)
                                     (Arith.nat_of_integer
                                       (Big_int.big_int_of_int 2))))
                                 (List.nth ts
                                   (Arith.minus_nat (List.size_list ts)
                                     (Arith.nat_of_integer
                                       (Big_int.big_int_of_int 3))))))))
    | uu, Bot -> Bot;;

end;; (*struct Wasm_Checker_Types*)

module Wasm_Checker : sig
  val convert_cond : Wasm_Ast.t -> Wasm_Ast.t -> Wasm_Ast.sx option -> bool
  val same_lab_h :
    Arith.nat list ->
      (Wasm_Ast.t list) list -> Wasm_Ast.t list -> (Wasm_Ast.t list) option
  val same_lab :
    Arith.nat list -> (Wasm_Ast.t list) list -> (Wasm_Ast.t list) option
  val check :
    unit Wasm_Ast.t_context_ext ->
      Wasm_Ast.b_e list ->
        Wasm_Checker_Types.checker_type -> Wasm_Checker_Types.checker_type
  val b_e_type_checker :
    unit Wasm_Ast.t_context_ext -> Wasm_Ast.b_e list -> Wasm_Ast.tf -> bool
  val check_single :
    unit Wasm_Ast.t_context_ext ->
      Wasm_Ast.b_e ->
        Wasm_Checker_Types.checker_type -> Wasm_Checker_Types.checker_type
end = struct

let rec convert_cond
  t1 t2 sx =
    not (Wasm_Ast.equal_ta t1 t2) &&
      (Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t1) (Wasm_Base_Defs.t_sec t2) &&
        Product_Type.equal_bool (Option.is_none sx)
          (Wasm_Base_Defs.is_float_t t1 && Wasm_Base_Defs.is_float_t t2 ||
            Wasm_Base_Defs.is_int_t t1 &&
              (Wasm_Base_Defs.is_int_t t2 &&
                Arith.less_nat (Wasm_Base_Defs.t_length t1)
                  (Wasm_Base_Defs.t_length t2))));;

let rec same_lab_h
  x0 uu ts = match x0, uu, ts with [], uu, ts -> Some ts
    | i :: is, lab_c, ts ->
        (if Arith.less_eq_nat (List.size_list lab_c) i then None
          else (if List.equal_list Wasm_Ast.equal_t (List.nth lab_c i) ts
                 then same_lab_h is lab_c (List.nth lab_c i) else None));;

let rec same_lab
  x0 lab_c = match x0, lab_c with [], lab_c -> None
    | i :: is, lab_c ->
        (if Arith.less_eq_nat (List.size_list lab_c) i then None
          else same_lab_h is lab_c (List.nth lab_c i));;

let rec check
  c es ts =
    (match es with [] -> ts
      | e :: esa ->
        (match ts
          with Wasm_Checker_Types.TopType _ -> check c esa (check_single c e ts)
          | Wasm_Checker_Types.Type _ -> check c esa (check_single c e ts)
          | Wasm_Checker_Types.Bot -> Wasm_Checker_Types.Bot))
and b_e_type_checker
  c es (Wasm_Ast.Tf (tn, tm)) =
    Wasm_Checker_Types.c_types_agree (check c es (Wasm_Checker_Types.Type tn))
      tm
and check_single
  c x1 ts = match c, x1, ts with
    c, Wasm_Ast.EConst v, ts ->
      Wasm_Checker_Types.type_update ts []
        (Wasm_Checker_Types.Type [Wasm_Base_Defs.typeof v])
    | c, Wasm_Ast.Unop_i (t, uu), ts ->
        (if Wasm_Base_Defs.is_int_t t
          then Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TSome t]
                 (Wasm_Checker_Types.Type [t])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Unop_f (t, uv), ts ->
        (if Wasm_Base_Defs.is_float_t t
          then Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TSome t]
                 (Wasm_Checker_Types.Type [t])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Binop_i (t, iop), ts ->
        (if Wasm_Base_Defs.is_int_t t &&
              (if Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t) Wasm_Ast.Secret
                then Wasm_Base_Defs.safe_binop_i iop else true)
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome t; Wasm_Checker_Types.TSome t]
                 (Wasm_Checker_Types.Type [t])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Binop_f (t, uw), ts ->
        (if Wasm_Base_Defs.is_float_t t
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome t; Wasm_Checker_Types.TSome t]
                 (Wasm_Checker_Types.Type [t])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Testop (t, ux), ts ->
        (if Wasm_Base_Defs.is_int_t t
          then Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TSome t]
                 (Wasm_Checker_Types.Type
                   [Wasm_Ast.T_i32 (Wasm_Base_Defs.t_sec t)])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Relop_i (t, uy), ts ->
        (if Wasm_Base_Defs.is_int_t t
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome t; Wasm_Checker_Types.TSome t]
                 (Wasm_Checker_Types.Type
                   [Wasm_Ast.T_i32 (Wasm_Base_Defs.t_sec t)])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Relop_f (t, uz), ts ->
        (if Wasm_Base_Defs.is_float_t t
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome t; Wasm_Checker_Types.TSome t]
                 (Wasm_Checker_Types.Type
                   [Wasm_Ast.T_i32 (Wasm_Base_Defs.t_sec t)])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Cvtop (t1, Wasm_Ast.Convert, t2, sx), ts ->
        (if convert_cond t1 t2 sx
          then Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TSome t2]
                 (Wasm_Checker_Types.Type [t1])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Cvtop (t1, Wasm_Ast.Reinterpret, t2, sx), ts ->
        (if not (Wasm_Ast.equal_ta t1 t2) &&
              (Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t1)
                 (Wasm_Base_Defs.t_sec t2) &&
                (Arith.equal_nat (Wasm_Base_Defs.t_length t1)
                   (Wasm_Base_Defs.t_length t2) &&
                  Option.is_none sx))
          then Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TSome t2]
                 (Wasm_Checker_Types.Type [t1])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Cvtop (t1, Wasm_Ast.Classify, t2, sx), ts ->
        (if Wasm_Base_Defs.is_int_t t2 &&
              (Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t2) Wasm_Ast.Public &&
                (Wasm_Ast.equal_ta (Wasm_Base_Defs.classify_t t2) t1 &&
                  Option.is_none sx))
          then Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TSome t2]
                 (Wasm_Checker_Types.Type [t1])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Cvtop (t1, Wasm_Ast.Declassify, t2, sx), ts ->
        (if Wasm_Ast.equal_trust (Wasm_Ast.trust_t c) Wasm_Ast.Trusted &&
              (Wasm_Base_Defs.is_int_t t2 &&
                (Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t2) Wasm_Ast.Secret &&
                  (Wasm_Ast.equal_ta (Wasm_Base_Defs.declassify_t t2) t1 &&
                    Option.is_none sx)))
          then Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TSome t2]
                 (Wasm_Checker_Types.Type [t1])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Unreachable, ts ->
        Wasm_Checker_Types.type_update ts [] (Wasm_Checker_Types.TopType [])
    | c, Wasm_Ast.Nop, ts -> ts
    | c, Wasm_Ast.Drop, ts ->
        Wasm_Checker_Types.type_update ts [Wasm_Checker_Types.TAny]
          (Wasm_Checker_Types.Type [])
    | c, Wasm_Ast.Select sec, ts -> Wasm_Checker_Types.type_update_select sec ts
    | c, Wasm_Ast.Block (Wasm_Ast.Tf (tn, tm), es), ts ->
        (if b_e_type_checker
              (Wasm_Ast.label_update (fun _ -> [tm] @ Wasm_Ast.label c) c) es
              (Wasm_Ast.Tf (tn, tm))
          then Wasm_Checker_Types.type_update ts
                 (Wasm_Checker_Types.to_ct_list tn) (Wasm_Checker_Types.Type tm)
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Loop (Wasm_Ast.Tf (tn, tm), es), ts ->
        (if b_e_type_checker
              (Wasm_Ast.label_update (fun _ -> [tn] @ Wasm_Ast.label c) c) es
              (Wasm_Ast.Tf (tn, tm))
          then Wasm_Checker_Types.type_update ts
                 (Wasm_Checker_Types.to_ct_list tn) (Wasm_Checker_Types.Type tm)
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.If (Wasm_Ast.Tf (tn, tm), es1, es2), ts ->
        (if b_e_type_checker
              (Wasm_Ast.label_update (fun _ -> [tm] @ Wasm_Ast.label c) c) es1
              (Wasm_Ast.Tf (tn, tm)) &&
              b_e_type_checker
                (Wasm_Ast.label_update (fun _ -> [tm] @ Wasm_Ast.label c) c) es2
                (Wasm_Ast.Tf (tn, tm))
          then Wasm_Checker_Types.type_update ts
                 (Wasm_Checker_Types.to_ct_list
                   (tn @ [Wasm_Ast.T_i32 Wasm_Ast.Public]))
                 (Wasm_Checker_Types.Type tm)
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Br i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.label c))
          then Wasm_Checker_Types.type_update ts
                 (Wasm_Checker_Types.to_ct_list (List.nth (Wasm_Ast.label c) i))
                 (Wasm_Checker_Types.TopType [])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Br_if i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.label c))
          then Wasm_Checker_Types.type_update ts
                 (Wasm_Checker_Types.to_ct_list
                   (List.nth (Wasm_Ast.label c) i @
                     [Wasm_Ast.T_i32 Wasm_Ast.Public]))
                 (Wasm_Checker_Types.Type (List.nth (Wasm_Ast.label c) i))
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Br_table (is, i), ts ->
        (match same_lab (is @ [i]) (Wasm_Ast.label c)
          with None -> Wasm_Checker_Types.Bot
          | Some tls ->
            Wasm_Checker_Types.type_update ts
              (Wasm_Checker_Types.to_ct_list
                (tls @ [Wasm_Ast.T_i32 Wasm_Ast.Public]))
              (Wasm_Checker_Types.TopType []))
    | c, Wasm_Ast.Return, ts ->
        (match Wasm_Ast.return c with None -> Wasm_Checker_Types.Bot
          | Some tls ->
            Wasm_Checker_Types.type_update ts
              (Wasm_Checker_Types.to_ct_list tls)
              (Wasm_Checker_Types.TopType []))
    | c, Wasm_Ast.Call i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.func_t c))
          then (let (tr, Wasm_Ast.Tf (tn, tm)) = List.nth (Wasm_Ast.func_t c) i
                  in
                 (if Wasm_Base_Defs.trust_compat (Wasm_Ast.trust_t c) tr
                   then Wasm_Checker_Types.type_update ts
                          (Wasm_Checker_Types.to_ct_list tn)
                          (Wasm_Checker_Types.Type tm)
                   else Wasm_Checker_Types.Bot))
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Call_indirect i, ts ->
        (if not (Option.is_none (Wasm_Ast.table c)) &&
              Arith.less_nat i (List.size_list (Wasm_Ast.types_t c))
          then (let (tr, Wasm_Ast.Tf (tn, tm)) = List.nth (Wasm_Ast.types_t c) i
                  in
                 (if Wasm_Base_Defs.trust_compat (Wasm_Ast.trust_t c) tr
                   then Wasm_Checker_Types.type_update ts
                          (Wasm_Checker_Types.to_ct_list
                            (tn @ [Wasm_Ast.T_i32 Wasm_Ast.Public]))
                          (Wasm_Checker_Types.Type tm)
                   else Wasm_Checker_Types.Bot))
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Get_local i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.local c))
          then Wasm_Checker_Types.type_update ts []
                 (Wasm_Checker_Types.Type [List.nth (Wasm_Ast.local c) i])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Set_local i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.local c))
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome (List.nth (Wasm_Ast.local c) i)]
                 (Wasm_Checker_Types.Type [])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Tee_local i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.local c))
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome (List.nth (Wasm_Ast.local c) i)]
                 (Wasm_Checker_Types.Type [List.nth (Wasm_Ast.local c) i])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Get_global i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.global c))
          then Wasm_Checker_Types.type_update ts []
                 (Wasm_Checker_Types.Type
                   [Wasm_Ast.tg_t (List.nth (Wasm_Ast.global c) i)])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Set_global i, ts ->
        (if Arith.less_nat i (List.size_list (Wasm_Ast.global c)) &&
              Wasm_Base_Defs.is_mut (List.nth (Wasm_Ast.global c) i)
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome
                    (Wasm_Ast.tg_t (List.nth (Wasm_Ast.global c) i))]
                 (Wasm_Checker_Types.Type [])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Load (t, tp_sx, a, off), ts ->
        (match Wasm_Ast.memory c with None -> Wasm_Checker_Types.Bot
          | Some (_, sec) ->
            (if Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t) sec &&
                  Wasm_Base_Defs.load_store_t_bounds a
                    (Wasm_Base_Defs.option_projl tp_sx) t
              then Wasm_Checker_Types.type_update ts
                     [Wasm_Checker_Types.TSome (Wasm_Ast.T_i32 Wasm_Ast.Public)]
                     (Wasm_Checker_Types.Type [t])
              else Wasm_Checker_Types.Bot))
    | c, Wasm_Ast.Store (t, tp, a, off), ts ->
        (match Wasm_Ast.memory c with None -> Wasm_Checker_Types.Bot
          | Some (_, sec) ->
            (if Wasm_Ast.equal_sec (Wasm_Base_Defs.t_sec t) sec &&
                  Wasm_Base_Defs.load_store_t_bounds a tp t
              then Wasm_Checker_Types.type_update ts
                     [Wasm_Checker_Types.TSome (Wasm_Ast.T_i32 Wasm_Ast.Public);
                       Wasm_Checker_Types.TSome t]
                     (Wasm_Checker_Types.Type [])
              else Wasm_Checker_Types.Bot))
    | c, Wasm_Ast.Current_memory, ts ->
        (if not (Option.is_none (Wasm_Ast.memory c))
          then Wasm_Checker_Types.type_update ts []
                 (Wasm_Checker_Types.Type [Wasm_Ast.T_i32 Wasm_Ast.Public])
          else Wasm_Checker_Types.Bot)
    | c, Wasm_Ast.Grow_memory, ts ->
        (if not (Option.is_none (Wasm_Ast.memory c))
          then Wasm_Checker_Types.type_update ts
                 [Wasm_Checker_Types.TSome (Wasm_Ast.T_i32 Wasm_Ast.Public)]
                 (Wasm_Checker_Types.Type [Wasm_Ast.T_i32 Wasm_Ast.Public])
          else Wasm_Checker_Types.Bot);;

end;; (*struct Wasm_Checker*)

module Wasm_Checker_Printing : sig
  val typing :
    unit Wasm_Ast.t_context_ext -> Wasm_Ast.b_e list -> Wasm_Ast.tf -> bool
end = struct

let rec typing x = Wasm_Checker.b_e_type_checker x;;

end;; (*struct Wasm_Checker_Printing*)
