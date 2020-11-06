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

  | Rotli of int | Rotri of int
  | Rotl | Rotr

          
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
  (* index in memory and index of memory - because we cannot have the memory here*)
  | Load of term * int * int * Types.extension option
  | Store of term * term * int * int (* address, value, memory, size *) 
  (* | Load of Smemory.t * term (\* memory, index *\) *)
  | App of func * term list
  | Let of term * term


type mergetype = PLUS_INF | MINUS_INF | Integer of int | Term of term

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

let zero = BitVec (0, 32)
let one = BitVec (1, 32)
         
let int_to_intterm i = Int i
let int_to_bvterm i n = BitVec (i,n)
let float_to_term f = Float f

  
let rec is_high =
  function
  | Const (High _)
    | Multi(_, High _, _) -> true
  | App (f, t::ts) -> is_high_all ts
  | Let (t1, t2) -> is_high t1 || is_high t2
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
                    
let high_to_term () =
  Const (get_high())
  
let low_to_term () =
  Const (get_low())
                   
let list_to_term ts =
  let id = if is_high_all ts then get_high () else get_low () in
  Multi(ts, id, List.length ts)
  
let term_to_int i =
  match i with
  | Int i -> i
  | BitVec (i,n) -> i
  | _ -> failwith "Term_to_int error: at smt_type"

let bool_to_term b =  if b then BitVec (1, 1) else BitVec (0, 1)

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
  | BitVec(i1,nb1), BitVec(i2,nb2) when nb2 == nb1 -> BitVec(i1+i2, nb1)
  | BitVec(0,nb), t
    | t, BitVec(0,nb)-> t
  | _ -> App (BvAdd, [t1; t2])
    (* match t1, t2 with
     * | App (BvAdd, ts1), App (BvAdd, ts2) -> App (BvAdd, ts1 @ ts2)
     * | App (BvAdd, ts), t
     *   | t, App (BvAdd, ts) -> App (BvAdd, t::ts)
     * | _, _-> App (BvAdd, [t1;t2]) *)


let bvsub t1 t2 = App (BvSub, [t1;t2])

let bvmul t1 t2 = App (BvMul, [t1;t2])
    (* match t1, t2 with
     * | App (BvMul, ts1), App (BvMul, ts2) -> App (BvMul, ts1 @ ts2)
     * | App (BvMul, ts), t
     *   | t, App (BvMul, ts) -> App (BvMul, t::ts)
     * | _, _-> App (BvMul, [t1;t2]) *)


let bvurem t1 t2 = App (BvURem, [t1;t2])
                
let bvsrem t1 t2 = App (BvSRem, [t1;t2])
let bvsmod t1 t2 = App (BvSMod, [t1;t2])

(* Todo(Romy): Check doesn't exists *)
let bvdiv t1 t2 = App (BvDiv, [t1;t2])
                 
let bvshl t1 t2 = App (BvShl, [t1;t2])
let bvlshr t1 t2 = App (BvLShr, [t1;t2])
let bvashr t1 t2 = App (BvAShr, [t1;t2])

let bvor t1 t2 = App (BvOr, [t1;t2])
let bvand t1 t2 = App (BvAnd, [t1;t2])
let bvnand t1 t2 = App (BvNand, [t1;t2])
let bvnor t1 t2 = App (BvNor, [t1;t2])
let bvxnor t1 t2 = App (BvXNor, [t1;t2])
let bvxor t1 t2 = App (BvXor, [t1;t2])
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
  | BvDiv -> "BvDiv"
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
  | Rotli i -> "Rotl" ^ string_of_int i
  | Rotri i -> "Rotr" ^ string_of_int i
           
let rec term_to_string (t : term) : string =
  match t with
  | Load (i, index, sz, ext) ->
     "Mem[" ^ term_to_string i ^ "]" ^ "(" ^ string_of_int sz ^ ")" 
  | Store (i, v, index, sz) ->
     "Mem[" ^ term_to_string i ^ "] = "
                               ^ term_to_string v ^ "(" ^ string_of_int sz ^ ")" 
  | String s -> s
  | Int i -> string_of_int i
  | Float f ->  string_of_float f
  | BitVec (i, n) -> "BitVec(" ^ string_of_int i ^ ", " ^ string_of_int n ^ ")"
  | Const id ->  identifier_to_string id
  | App (f, ts) -> func_to_string f ^ " (" ^
                     List.fold_left (fun acc -> fun t -> acc ^ term_to_string t ^ ",") "" ts ^ ")" 
  | Let (t1, t2) -> "let " ^ term_to_string t1 ^ "=" ^ term_to_string t2
  | Multi (ts, id, n) ->
     let terms = List.fold_left (fun acc -> fun t -> acc ^ term_to_string t ^ ",") "" ts in
     "Multi( " ^ terms ^ "," ^ identifier_to_string id ^ "," ^ string_of_int n ^ ")"

     (* type mergetype = PLUS_INF | MINUS_INF | ZERO | Term of term *)
let merge_to_string (m : mergetype) : string =
  match m with
  | PLUS_INF -> "inf"
  | MINUS_INF -> "-inf"
  | Integer i -> string_of_int i
  | Term t -> term_to_string t

let count_depth si = 
  let rec count_depth_i count si =
    (* print_endline (string_of_int count); *)
    match si with
    | BitVec (i,n) -> count + 1
    | Const (_) -> count + 1
    | App (f, ts) ->
       List.fold_left (fun x y -> count_depth_i (x+1) y) (count + 1) ts
    | Load (i, memi, sz, ext) ->
       count_depth_i (count+1) i
    | _ -> failwith "Not supported."
  in
  count_depth_i 0 si
