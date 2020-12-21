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
                  
  | BvURem | BvSRem | BvSMod | BvUDiv | BvSDiv
  | BvShl | BvLShr | BvAShr
                   
  | BvOr | BvAnd | BvNand | BvNor | BvXNor | BvXor
  | BvNeg | BvNot
  | BvUle | BvUlt
  | BvSle | BvSlt 
  | BvUge | BvUgt
  | BvSge | BvSgt

  | Rotli of int | Rotri of int
  | Rotl | Rotr

  | ExtendS of int
  | ExtendU of int
  | Wrap of int
          
type sort = 
  | Sort of identifier
  | SortApp of identifier * sort list
  | BitVecSort of int

type term = 
  | String of string
  | Int of int
  | Float of float
  | BitVec of int64 * int (* number + number of bits *)
  | Const of identifier * int
  (* | Multi of term list * identifier * int (\* term list, high/low, number_of_elements *\) *)
  (* index in memory and index of memory - because we cannot have the memory here*)
  | Load of term * int * int * Types.extension option
  | Store of term * term * int * int (* address, value, memory, size *) 
  (* | Load of Smemory.t * term (\* memory, index *\) *)
  | App of func * term list
  (* | Let of term * term *)
  | Let of int

type mergetype = PLUS_INF | MINUS_INF | Integer of int64 | Term of term

type solv_type = TGT | TGE | TLT | TLE | TNONE
                                  
let curr_num = ref 0

let new_const () =
  curr_num := !curr_num + 1;
  !curr_num

(* val int_sort : sort
 * 
 * val bool_sort : sort
 * 
 * val array_sort : sort -> sort -> sort *)

let zero size = BitVec (0L, size)
let one size = BitVec (1L, size)
         
let int_to_intterm i = Int i
let int64_to_bvterm i n = BitVec (i,n)
let float_to_term f = Float f

  
let rec is_high =
  function
  | Const (High _, _) -> true
  | App (f, t::ts) -> is_high_all ts
  (* | Let (t1, t2) -> is_high t1 || is_high t2 *)
  | _ -> false

and is_high_all = function
  | h::hs -> is_high h || is_high_all hs
  | [] -> false


        
let is_low l =
  not (is_high l)

let is_int = function
  | Int _
    | BitVec _ -> true
  | _ -> false

let get_high () =
  let newc = new_const() in
  High newc

let get_low () =
  let newc = new_const() in
  Low newc
                    
let high_to_term size =
  Const (get_high(), size)
  
let low_to_term size =
  Const (get_low(), size)
                   
(* let list_to_term ts =
 *   let id = if is_high_all ts then get_high () else get_low () in
 *   Multi(ts, id, List.length ts) *)
  
let term_to_int i =
  match i with
  | Int i -> i
  | BitVec (i,n) -> Int64.to_int i
  | _ -> failwith "Term_to_int error: at smt_type"

let bool_to_term b =  if b then BitVec (1L, 1) else BitVec (0L, 1)

(* let const str = Const str *)

  (* match t1, t2 with
   * | App (Eq, ts1), App (Eq, ts2) -> App(Eq, ts1 @ ts2)
   * | App (Eq, ts), t
   *   | t, App(Eq, ts) -> App(Eq, t::ts)
   * | _, _-> App(Eq, [t1;t2]) *)

let load t i sz ext = Load(t, i, sz, ext)
let store t vt i sz = Store(t, vt, i, sz) 

let and_ t1 t2 =
  match t1, t2 with
  | App (And, ts1), App (And, ts2) -> App (And, ts1 @ ts2)
  | App (And, ts), t
    | t, App (And, ts) -> App (And, t::ts)
  | _, _-> App (And, [t1;t2])

let or_ t1 t2 =
  match t1, t2 with
  | App (Or, ts1), App (Or, ts2) -> App(Or, ts1 @ ts2)
  | App (Or, ts), t
    | t, App(Or, ts) -> App(Or, t::ts)
  | _, _-> App(Or, [t1;t2])

        
let not_ t1 =
  match t1 with
  | App (Not, [ts]) -> ts
  | _ -> App(Not, [t1])
(* val not_ : term -> term *)


(* val ite : term -> term -> term -> term *)
let ite b tif telse = App (Ite, [b;tif;telse])

let equals t1 t2 = App (Eq, [t1;t2]) (* ite (App(Eq, [t1;t2])) (Int 1) (Int 0) *)
                 
let implies t1 t2 = App(Implies, [t1;t2])

let add t1 t2 =
  match t1, t2 with
  | App (Add, ts1), App (Add, ts2) -> App (Add, ts1 @ ts2)
  | App (Add, ts), t
    | t, App (Add, ts) -> App (Add, t::ts)
  | _, _-> App (Add, [t1;t2])

let sub t1 t2 = App (Sub, [t1;t2])

let mul t1 t2 =
  match t1, t2 with
  | App (Mul, ts1), App (Mul, ts2) -> App (Mul, ts1 @ ts2)
  | App (Mul, ts), t
    | t, App (Mul, ts) -> App (Mul, t::ts)
  | _, _-> App (Mul, [t1;t2])

let div t1 t2 = App (Div, [t1;t2])

let lt t1 t2 = App(Lt, [t1;t2])
             
let gt t1 t2 = App(Gt, [t1;t2])

let lte t1 t2 = App(Lte, [t1;t2])
              
let gte t1 t2 = App(Gte, [t1;t2])


let bv i nb = BitVec(i, nb)

let bvadd t1 t2 =
  match t1,t2 with
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb2 = nb1 -> BitVec(Int64.(add i1 i2), nb1)
  | BitVec(0L,nb), t
    | t, BitVec(0L,nb)-> t
  | _ -> App (BvAdd, [t1; t2])
    (* match t1, t2 with
     * | App (BvAdd, ts1), App (BvAdd, ts2) -> App (BvAdd, ts1 @ ts2)
     * | App (BvAdd, ts), t
     *   | t, App (BvAdd, ts) -> App (BvAdd, t::ts)
     * | _, _-> App (BvAdd, [t1;t2]) *)


let bvsub t1 t2 =
  match t1,t2 with
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb2 = nb1 -> BitVec(Int64.(sub i1 i2), nb1)
  | t, BitVec(0L,nb)-> t
  | _ -> App (BvSub, [t1; t2])

  

let bvmul t1 t2 =
  (* print_endline "bvmul"; *)
  match t1,t2 with 
  | BitVec(0L,nb), t
    | t, BitVec(0L,nb) -> BitVec(0L,nb)
  | BitVec(1L,nb), t
    | t, BitVec(1L,nb) -> t
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb2 = nb1 -> BitVec(Int64.(mul i1 i2), nb1)
  | _ -> App (BvMul, [t1;t2])

let bvshl t1 t2 =
  match t1,t2 with 
  (* | BitVec(0L,nb), t -> BitVec(0L,nb) *)
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb1 = nb2 ->
     BitVec(Int64.(shift_left i1 (Int64.to_int i2)), nb1)
  | _ -> App (BvShl, [t1;t2])


let bvlshr t1 t2 = 
  match t1,t2 with 
  (* | BitVec(0L,nb), t -> BitVec(0L,nb) *)
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb1 = nb2 ->
     BitVec(Int64.(shift_right_logical i1 (Int64.to_int i2)), nb1)
  | _ -> App (BvLShr, [t1;t2])


let bvashr t1 t2 = 
  match t1,t2 with 
  (* | BitVec(0L,nb), t -> BitVec(0L,nb) *)
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb1 = nb2 ->
     BitVec(Int64.(shift_right i1 (Int64.to_int i2)), nb1)
  | _ -> App (BvAShr, [t1;t2])


       
                 
                 
let bvor t1 t2 =
  match t1,t2 with 
  (* | BitVec(0L,nb), t -> t *)
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb1 = nb2 ->
     BitVec(Int64.(logor i1 i2), nb1)
  | _ -> App (BvOr, [t1;t2])
       
let bvand t1 t2 =
  match t1,t2 with 
  | BitVec(0L,nb), t -> BitVec(0L,nb)
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb1 = nb2 ->
     BitVec(Int64.(logand i1 i2), nb1)
  | _ -> App (BvAnd, [t1;t2])
       
let bvnand t1 t2 = App (BvNand, [t1;t2])
let bvnor t1 t2 = App (BvNor, [t1;t2])
let bvxnor t1 t2 = App (BvXNor, [t1;t2])
let bvxor t1 t2 =
  match t1,t2 with 
  | BitVec(0L,nb), t -> BitVec(0L,nb)
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb1 = nb2 ->
     BitVec(Int64.(logxor i1 i2), nb1)
  | _ -> App (BvXor, [t1;t2])
       
let bvneg t1 = App (BvNeg, [t1])
let bvnot t1 = App (BvNot, [t1])
                
let bvule t1 t2 = App (BvUle, [t1;t2])
let bvult t1 t2 = App (BvUlt, [t1;t2])
let bvuge t1 t2 = App (BvUge, [t1;t2])
let bvugt t1 t2 = App (BvUgt, [t1;t2])
let bvsle t1 t2 = App (BvSle, [t1;t2])
let bvslt t1 t2 = App (BvSlt, [t1;t2])
let bvsge t1 t2 = App (BvSge, [t1;t2])
let bvsgt t1 t2 = App (BvSgt, [t1;t2])

let rotl t1 t2 = App (Rotl, [t1;t2])
let rotr t1 t2 = App (Rotr, [t1;t2])

let rotli t i = App (Rotli(i), [t])
let rotri t i = App (Rotri(i), [t])

let extsi t i = App (ExtendS(i), [t])
let extui t i = App (ExtendU(i), [t])
              
let wrap t i = App (Wrap(i), [t])



(* Not accounting for overflows *)
let merge solv told tnew =
  match solv with
  | TGT -> Some (MINUS_INF, Term told)
  | TGE -> Some (MINUS_INF, Term told)
  | TLT -> Some (Term told, PLUS_INF)
  | TLE -> Some (Term told, PLUS_INF)
  | TNONE -> None
  
    
let identifier_to_string id =
  match id with
  | High i -> "h" ^ string_of_int i
  | Low i -> "l" ^ string_of_int i

let func_to_string func =
  match func with
  | Id str -> str
  | Eq -> "Eq"
  | And -> "And"
  | Or -> "Or"
  | Not -> "Not"
  | Ite -> "Ite"
  | Implies -> "Implies"
  | Add -> "Add"
  | Sub -> "Sub"
  | Mul -> "Mul"
  | Div -> "Div"
  | Lt -> "Lt"
  | Gt -> "Gt"
  | Lte -> "Lte"
  | Gte -> "Gte"

  | BvAdd -> "BvAdd"
  | BvSub -> "BvSub"
  | BvMul -> "BvMul"
  | BvURem -> "BvURem"
  | BvSRem -> "BvSRem"
  | BvSMod -> "BvSMod"
  | BvUDiv -> "BvUDiv"
  | BvSDiv -> "BvSDiv"
  | BvShl -> "BvShl"
  | BvLShr -> "BvLShr"
  | BvAShr -> "BvAShr"
  | BvOr -> "BvOr"
  | BvAnd -> "BvAnd"
  | BvNand -> "BvNand"
  | BvXor -> "BvXor"
  | BvNor -> "BvNor"
  | BvXNor -> "BvXNor"
  | BvNeg  -> "BvNeg"
  | BvNot -> "BvNot"
  | BvUle -> "BvUle"
  | BvUlt -> "BvUlt"
  | BvUge -> "BvUge"
  | BvUgt -> "BvUgt"
  | BvSle -> "BvSle"
  | BvSlt -> "BvSlt"
  | BvSge -> "BvSge"
  | BvSgt -> "BvSgt"
  | Rotl -> "Rotl"
  | Rotr -> "Rotr"
  | Rotli i -> "Rotl " ^ string_of_int i
  | Rotri i -> "Rotr " ^ string_of_int i
  | ExtendS i -> "ExtendS " ^ string_of_int i
  | ExtendU i -> "ExtendU " ^ string_of_int i
  | Wrap i -> "Wrap " ^ string_of_int i
           
let rec term_to_string (t : term) : string =
  match t with
  | Load (i, index, sz, None) ->
     "Mem[" ^ term_to_string i ^ "]" ^ "(" ^ string_of_int sz ^ ")[None]" 
  | Load (i, index, sz, Some Types.ZX) ->
     "Mem[" ^ term_to_string i ^ "]" ^ "(" ^ string_of_int sz ^ ")[Some ZX]" 
  | Load (i, index, sz, Some Types.SX) ->
     "Mem[" ^ term_to_string i ^ "]" ^ "(" ^ string_of_int sz ^ ")[Some SX]" 

  | Store (i, v, index, sz) ->
     "Mem[" ^ term_to_string i ^ "] = "
                               ^ term_to_string v ^ "(" ^ string_of_int sz ^ ")" 
  | String s -> s
  | Int i -> string_of_int i
  | Float f ->  string_of_float f
  | BitVec (i, n) -> "BitVec(" ^ I64.to_string_u i ^ ", " ^ string_of_int n ^ ")"
  | Const (id, size) ->  identifier_to_string id ^ "(" ^ string_of_int size ^ ")"
  | App (f, ts) -> func_to_string f ^ " (" ^
                     List.fold_left (fun acc -> fun t -> acc ^ term_to_string t ^ ",") "" ts ^ ")" 
  (* | Let (t1, t2) -> "let " ^ term_to_string t1 ^ "=" ^ term_to_string t2 *)
  | Let (i) -> "Let(" ^ string_of_int i ^ ")"
             
     (* type mergetype = PLUS_INF | MINUS_INF | ZERO | Term of term *)
let merge_to_string (m : mergetype) : string =
  match m with
  | PLUS_INF -> "inf"
  | MINUS_INF -> "-inf"
  | Integer i -> I64.to_string_u i
  | Term t -> term_to_string t

let count_depth si n = 
  let rec count_depth_i count si =
    if (count > n) then count
    else
    (* print_endline (string_of_int count); *)
      match si with
      | BitVec (i,n) -> count + 1
      | Const (_) -> count + 1
      | App (f, ts) ->
         List.fold_left (fun x y -> count_depth_i (x+1) y) (count + 1) ts
      | Load (i, memi, sz, ext) ->
         count_depth_i (count+1) i
      | Let i -> count + 1
      | _ -> failwith "Not supported."
  in
  let c = count_depth_i 0 si in
  c > n

(* Todo(Romy): Check doesn't exists *)
let bvudiv t1 t2 =
  match t1,t2 with
  | _, BitVec(1L,nb2)  -> t1
  | _, BitVec(2L,nb2) -> bvlshr t1 (BitVec(1L, nb2))
  | _, BitVec(4L,nb2) -> bvlshr t1 (BitVec(2L, nb2))
  | _, BitVec(8L,nb2) -> bvlshr t1 (BitVec(3L, nb2))
  | _, BitVec(16L,nb2) -> bvlshr t1 (BitVec(4L, nb2))
  | _, BitVec(32L,nb2) -> bvlshr t1 (BitVec(5L, nb2))
  | _, BitVec(64L,nb2) -> bvlshr t1 (BitVec(6L, nb2))
  | _, BitVec(128L,nb2) -> bvlshr t1 (BitVec(7L, nb2))
  | _, BitVec(256L,nb2) -> bvlshr t1 (BitVec(8L, nb2))
  | _, BitVec(512L,nb2) -> bvlshr t1 (BitVec(9L, nb2))
  | _, BitVec(1024L,nb2) -> bvlshr t1 (BitVec(10L, nb2))
  |_ ->
    print_endline "division by";
    print_endline (term_to_string t2);
    App (BvUDiv, [t1;t2])
       
(* Todo(Romy): Check if correct *)
let bvsdiv t1 t2 =
  match t1,t2 with
  | _, BitVec(1L,nb2)  -> t1
  | _, BitVec(2L,nb2) -> bvashr t1 (BitVec(1L, nb2))
  | _, BitVec(4L,nb2) -> bvashr t1 (BitVec(2L, nb2))
  | _, BitVec(8L,nb2) -> bvashr t1 (BitVec(3L, nb2))
  | _, BitVec(16L,nb2) -> bvashr t1 (BitVec(4L, nb2))
  | _, BitVec(32L,nb2) -> bvashr t1 (BitVec(5L, nb2))
  | _, BitVec(64L,nb2) -> bvashr t1 (BitVec(6L, nb2))
  | _, BitVec(128L,nb2) -> bvashr t1 (BitVec(7L, nb2))
  | _, BitVec(256L,nb2) -> bvashr t1 (BitVec(8L, nb2))
  | _, BitVec(512L,nb2) -> bvashr t1 (BitVec(9L, nb2))
  | _, BitVec(1024L,nb2) -> bvashr t1 (BitVec(10L, nb2))
  |_ ->
    print_endline "Sdivision by";
    print_endline (term_to_string t2);
    App (BvSDiv, [t1;t2])
 
(* Todo(Romy): Check if correct *)
let bvurem t1 t2 =
  match t1,t2 with
  | _, BitVec(1L,nb2)  -> t1
  | _, BitVec(2L,nb2) -> bvand  t1 (BitVec(1L, nb2))
  | _, BitVec(4L,nb2) -> bvand t1 (BitVec(3L, nb2))
  | _, BitVec(8L,nb2) -> bvand t1 (BitVec(7L, nb2))
  | _, BitVec(16L,nb2) -> bvand t1 (BitVec(15L, nb2))
  | _, BitVec(32L,nb2) -> bvand t1 (BitVec(31L, nb2))
  | _, BitVec(64L,nb2) -> bvand t1 (BitVec(63L, nb2))
  | _, BitVec(128L,nb2) -> bvand t1 (BitVec(127L, nb2))
  | _, BitVec(256L,nb2) -> bvand t1 (BitVec(255L, nb2))
  | _, BitVec(512L,nb2) -> bvand t1 (BitVec(511L, nb2))
  | _, BitVec(1024L,nb2) -> bvand t1 (BitVec(1023L, nb2))
  |_ ->
    print_endline "bvurem by";
    print_endline (term_to_string t2);
    App (BvURem, [t1;t2])

(* let bvurem t1 t2 = App (BvURem, [t1;t2]) *)
                
let bvsrem t1 t2 = App (BvSRem, [t1;t2])
let bvsmod t1 t2 = App (BvSMod, [t1;t2])

let let_ (i : int) = Let i
