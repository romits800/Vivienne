type identifier =
  High of int | Low of int 

type func =
  | Id of string

  | Eq | And | Or
  | Ite | Not

  | Implies
  | Add | Sub | Mul | Div
  | Lt | Gt | Lte | Gte

  | BvAdd | BvSub | BvMul
                  
  | BvURem | BvSRem | BvSMod | BvDiv
  | BvShl | BvLShr | BvAShr
                   
  | BvOr | BvAnd | BvNand | BvNor | BvXNor
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
  | App of func * term list
  | Let of string * term * term

type check_sat_result = 
  | Sat
  | Unsat
  | Unknown

(* val int_sort : sort
 * 
 * val bool_sort : sort
 * 
 * val array_sort : sort -> sort -> sort *)

let zero = Int 0
let one = Int 1
         
let int_to_intterm i = Int i
let int_to_bvterm i n = BitVec (i,n)
let float_to_term f = Float f

let high_to_term i = Const (High i)
let low_to_term i = Const (Low i)
                   

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
    match t1, t2 with
    | App (BvAdd, ts1), App (BvAdd, ts2) -> App (BvAdd, ts1 @ ts2)
    | App (BvAdd, ts), t
      | t, App (BvAdd, ts) -> App (BvAdd, t::ts)
    | _, _-> App (BvAdd, [t1;t2])


let bvsub t1 t2 = App (BvSub, [t1;t2])

let bvmul t1 t2 =
    match t1, t2 with
    | App (BvMul, ts1), App (BvMul, ts2) -> App (BvMul, ts1 @ ts2)
    | App (BvMul, ts), t
      | t, App (BvMul, ts) -> App (BvMul, t::ts)
    | _, _-> App (BvMul, [t1;t2])


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

           
let rec term_to_string t =
  match t with
  | String s -> s
  | Int i -> string_of_int i
  | Float f ->  string_of_float f
  | BitVec (i, n) -> "BitVec(" ^ string_of_int i ^ ", " ^ string_of_int n ^ ")"
  | Const id ->  identifier_to_string id
  | App (f, ts) -> func_to_string f ^ " (" ^
                     List.fold_left (fun acc -> fun t -> acc ^ term_to_string t ^ ",") "" ts ^ ")" 
  | Let (st, t1, t2) -> "let " ^ st ^ "=" ^ term_to_string t1 ^ "in" ^ term_to_string t2
