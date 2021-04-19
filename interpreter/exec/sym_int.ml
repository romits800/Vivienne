 (*In part based on https://people.cs.umass.edu/~arjun/courses/cmpsci631-spring2016/ocamldoc/Smtlib.html*)

module type SmtType =
sig
  type term
  type mergetype
  type solv_type
  (* val declare_const : solver -> identifier -> sort -> unit
   *   
   * val assert_ : solver -> term -> unit
   * 
   * val check_sat : solver -> check_sat_result
   * 
   * val get_model : solver -> (identifier * term) list
   * 
   * val push : solver -> unit
   * 
   * val pop : solver -> unit *)

  (* val int_sort : sort
   * 
   * val bool_sort : sort
   * 
   * val array_sort : sort -> sort -> sort *)
  
  val size: int
  val zero: int -> term
  val one: int -> term
    
  val int_to_intterm : int -> term
  val int64_to_bvterm : int64 -> int -> term
  val float_to_term : float -> term
  val high_to_term : int -> term
  val low_to_term : int -> term

  val is_high : term -> bool
  val is_low : term -> bool
  val is_int : term -> bool
    
  val term_to_int : term -> int
  val bool_to_term : bool -> term

  (* val list_to_term : term list  -> term *)
  (* val const : string -> term *)
  val equals : term -> term -> term

  val load  : term -> int -> int -> int -> Types.extension option -> term
  val store : term -> term -> int -> int -> int -> term
    
  val and_ : term -> term -> term
  val or_  : term -> term -> term
  val not_ : term -> term
  val ite  : term -> term -> term -> term
  val implies : term -> term -> term
  val add  : term -> term -> term
  val sub  : term -> term -> term
  val mul  : term -> term -> term
  val div  : term -> term -> term
  val lt   : term -> term -> term
  val gt   : term -> term -> term
  val lte  : term -> term -> term
  val gte  : term -> term -> term

  (* val bv_sort : int -> sort *)

  val bv     : int64 -> int -> term
  val bvadd  : term -> term -> term
  val bvsub  : term -> term -> term
  val bvmul  : term -> term -> term
  val bvurem : term -> term -> term
  val bvsrem : term -> term -> term
  val bvsmod : term -> term -> term
  val bvsdiv : term -> term -> term 
  val bvudiv : term -> term -> term 
  val bvshl  : term -> term -> term
  val bvlshr : term -> term -> term
  val bvashr : term -> term -> term
  val bvor   : term -> term -> term
  val bvand  : term -> term -> term
  val bvxor  : term -> term -> term
  val bvnand : term -> term -> term
  val bvnor  : term -> term -> term
  val bvxnor : term -> term -> term
  val bvneg  : term -> term
  val bvnot  : term -> term

  val rotl  : term -> term -> term
  val rotli : term -> int -> term
  val rotr  : term -> term -> term
  val rotri : term -> int -> term

  (* Not implemented *)
  val bvule : term -> term -> term
  val bvult : term -> term -> term
  val bvuge : term -> term -> term
  val bvugt : term -> term -> term
  val bvsle : term -> term -> term
  val bvslt : term -> term -> term
  val bvsge : term -> term -> term
  val bvsgt : term -> term -> term
    
  val extsi : term -> int -> term
  val extui : term -> int -> term
  val wrap  : term -> int -> term

  val term_to_string : term -> string
  val merge : solv_type -> term -> term -> (mergetype * mergetype) option
  val merge_to_string : mergetype -> string
  val count_depth : term -> int -> bool
  val let_ : int -> term

end

module type S =
sig
  type t
  type bits
  type mtype
  type stype
  (* val of_bits : bits -> t
   * val to_bits : t -> bits *)
     
  val zero : t
  val one : t
   
  val load : t -> int -> int -> int -> Types.extension option -> t
  val store : t -> t -> int -> int -> int -> t

  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val not_ : t -> t

  val ite : t -> t -> t -> t
  val eqz : t -> t
  val eq : t -> t -> t
  val ne : t -> t -> t
  val lt_s : t -> t -> t
  val lt_u : t -> t -> t
  val le_s : t -> t -> t
  val le_u : t -> t -> t
  val gt_s : t -> t -> t
  val gt_u : t -> t -> t
  val ge_s : t -> t -> t
  val ge_u : t -> t -> t

  val band : t -> t -> t
  val bor : t -> t -> t
  val xor : t -> t -> t

     
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div_s : t -> t -> t 
  val div_u : t -> t -> t 
  val rem_s : t -> t -> t 
  val rem_u : t -> t -> t 

  val shl : t -> t -> t
  val shr_s : t -> t -> t
  val shr_u : t -> t -> t
  val rotl : t -> t -> t
  val rotr : t -> t -> t
  val clz : t -> t
  val ctz : t -> t
  val popcnt : t -> t
  val extend_s : int -> t -> t
  val extend_u : int -> t -> t
  val wrap : int -> t -> t
    
  val int_of_int : int -> t
  val bv_of_int : int64 -> int -> t
  val of_float : float -> t
  val of_high : unit -> t
  val of_low : unit -> t
  val is_low : t -> bool
  val is_high : t -> bool
  val is_int : t -> bool

  val of_int_s : int -> t
  val of_int_u : int -> t
  val of_int32 : int32 -> t
  val of_string_s : string -> t
  val of_string_u : string -> t
  val of_string : string -> t
  (* val of_list : t list -> t *)
  val to_int_s : t -> int
  val to_int_u : t -> int
  val to_string_s : t -> string
  val to_string_u : t -> string
  val to_hex_string : t -> string

  val merge : stype -> t -> t-> (mtype * mtype) option
  val merge_to_string : mtype -> string
  val count_depth : t -> int -> bool
  val let_ : int -> t
end

module Make (Rep : SmtType) : S with type bits = Rep.term and
                                     type stype = Rep.solv_type and
                                     type mtype = Rep.mergetype and
                                     type t = Rep.term  =
struct
  (*
   * Unsigned comparison in terms of signed comparison.
   *)
  (* let cmp_u x op y =
   *   op (Rep.add x Rep.min_int) (Rep.add y Rep.min_int) *)

  (*
   * Unsigned division and remainder in terms of signed division; algorithm from
   * Hacker's Delight, Second Edition, by Henry S. Warren, Jr., section 9-3
   * "Unsigned Short Division from Signed Division".
   *)
  (* let divrem_u n d =
   *   if d = Rep.zero then raise Numeric_error.IntegerDivideByZero else
   *   let t = Rep.shift_right d (Rep.bitwidth - 1) in
   *   let n' = Rep.logand n (Rep.lognot t) in
   *   let q = Rep.shift_left (Rep.div (Rep.shift_right_logical n' 1) d) 1 in
   *   let r = Rep.sub n (Rep.mul q d) in
   *   if cmp_u r (<) d then
   *     q, r
   *   else
   *     Rep.add q Rep.one, Rep.sub r d *)

  type t = Rep.term
  type bits = Rep.term
  type mtype = Rep.mergetype
  type stype = Rep.solv_type
  (* let of_bits x = x
   * let to_bits x = x *)

  let zero = Rep.zero Rep.size
  let one = Rep.one Rep.size
  let ite = Rep.ite
  (* let one = Rep.bv  1 Rep.size
   * let ten = Rep.bv 10 Rep.size *)

  (* add, sub, and mul are sign-agnostic and do not trap on overflow. *)
  let load = Rep.load
  let store = Rep.store
           
  let add = Rep.bvadd
  let sub = Rep.bvsub
  let mul = Rep.bvmul

  (* result is truncated toward zero *)
  let div_s x y =
    (Rep.bvsdiv x y)

  (* result is floored (which is the same as truncating for unsigned values) *)
  (* TODO(Romy): fix *)
  let div_u x y =
    (Rep.bvudiv x y)

  (* result has the sign of the dividend *)
  let rem_s x y =
      (Rep.bvsrem x y)
  
  let rem_u x y =
      (Rep.bvurem x y)

  let and_ = Rep.and_
  let or_ = Rep.or_
  let band = Rep.bvand
  let bor = Rep.bvor

  let not_ = Rep.not_
  let xor = Rep.bvxor

  (*TODO(ROMY): Check this?*)
  (* WebAssembly's shifts mask the shift count according to the bitwidth. *)
  (* let shift f x y = *)
    (* Rep.bvsh *)
    (* f x (Rep.to_int (Rep.logand y (Rep.of_int (Rep.bitwidth - 1)))) *)

  let shl = Rep.bvshl 
    (* shift Rep.shift_left x y  *)

  let shr_s = Rep.bvashr
 

  let shr_u = Rep.bvlshr
 

   let rotl x y =
    if Rep.is_int y then
      Rep.rotli x (Rep.term_to_int y)
    else
      Rep.rotl x y
 
  let rotr x y = (* Rep.rotr x y *)
    if Rep.is_int y then
      Rep.rotri x (Rep.term_to_int y)
    else
      Rep.rotr x y
    
  (* clz: count leading zeros 
     is defined for all values, including all-zeros. *)
  (* TODO(Romy) *)
  let clz x = failwith "not implemented clz"
    (* let rec loop acc n =
     *   if n = Rep.zero then
     *     Rep.bitwidth
     *   else if and_ n (Rep.shift_left Rep.one (Rep.bitwidth - 1)) = zero then
     *     loop (1 + acc) (Rep.shift_left n 1)
     *   else
     *     acc
     * in Rep.of_int (loop 0 x) *)

  (* ctz: count trailing zeros
     is defined for all values, including all-zeros. *)
  (* TODO(Romy) *)
  let ctz x = failwith "not implemented ctz"
    (* let rec loop acc n =
     *   if n = Rep.zero then
     *     Rep.bitwidth
     *   else if and_ n Rep.one = Rep.one then
     *     acc
     *   else
     *     loop (1 + acc) (Rep.shift_right_logical n 1)
     * in Rep.of_int (loop 0 x) *)
  (* TODO(Romy) *)
  let popcnt x = failwith "not implemented popcnt"
    (* let rec loop acc i n =
     *   if n = Rep.zero then
     *     acc
     *   else
     *     let acc' = if and_ n Rep.one = Rep.one then acc + 1 else acc in
     *     loop acc' (i - 1) (Rep.shift_right_logical n 1)
     * in Rep.of_int (loop 0 Rep.bitwidth x) *)


  let extend_s n x = Rep.extsi x n
  let extend_u n x = Rep.extui x n
  let wrap n x = Rep.wrap x n
    (* let shift = Rep.bitwidth - n in
     * Rep.shift_right (Rep.shift_left x shift) shift *)

  let eqz x = Rep.equals x (Rep.zero Rep.size)  (* x = Rep.zero *)

  let eq = Rep.equals
  let ne x y = Rep.not_ (Rep.equals x y) 
  let lt_s = Rep.bvslt
  let lt_u = Rep.bvult
  let le_s = Rep.bvsle
  let le_u = Rep.bvule
  let gt_s = Rep.bvsgt
  let gt_u = Rep.bvugt
  let ge_s = Rep.bvsge
  let ge_u = Rep.bvuge


  let int_of_int = Rep.int_to_intterm
  let bv_of_int = Rep.int64_to_bvterm
  let of_float = Rep.float_to_term
  let of_high () =
    Rep.high_to_term Rep.size
  let of_low () =
    Rep.low_to_term Rep.size

  let is_high = Rep.is_high
  let is_low = Rep.is_low
  let is_int = Rep.is_int
              
             
  let of_int_s i = Rep.int64_to_bvterm (Int64.of_int i) Rep.size
  let of_int_u i = Rep.int64_to_bvterm (Int64.of_int i) Rep.size
  let of_int32 i = Rep.int64_to_bvterm (Int64.of_int (Int32.to_int i)) Rep.size
  (*TODO(Romy) *)(* Unimplemented *)
  let of_string_s str = Rep.zero Rep.size
  let of_string_u str = Rep.zero Rep.size
  let of_string  str = Rep.zero Rep.size
  (* let of_list = Rep.list_to_term *)
  let to_int_s  t  = Rep.term_to_int t
  let to_int_u  t  = Rep.term_to_int t
  let to_string_s  t = Rep.term_to_string t
                     
  let to_string_u t = ""
  let to_hex_string t = ""

  let merge = Rep.merge
  let merge_to_string = Rep.merge_to_string
  let count_depth = Rep.count_depth
  let let_ = Rep.let_
end
