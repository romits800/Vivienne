open Values
open Instance
open Ast
open Source
open Types
open Script
open Symbvalues


module Crash = Error.Make ()


let numeric_error at = function
  | Numeric_error.IntegerOverflow -> "integer overflow"
  | Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Numeric_error.InvalidConversionToInteger -> "invalid conversion to integer"
  | Eval_numeric.TypeError (i, v, t) ->
    Crash.error at
      ("type error, expected " ^ Types.string_of_value_type t ^ " as operand " ^
       string_of_int i ^ ", got " ^ Types.string_of_value_type (type_of v))
  | exn -> raise exn



module Map = Map.Make(String)

let map_var_size: int Map.t ref = ref Map.empty
(* let map_var_expr: sstack Map.t ref = ref Map.empty *)


let create_new_symb x t =
  let last = (try Map.find x !map_var_size
              with Not_found -> 0) in
  map_var_size := Map.add x (last+1) !map_var_size;
  match t with
  | "int" -> Integ (x ^ string_of_int last)
  | "bit" -> Bitmap (x ^ string_of_int last)
  | "real" -> Real (x ^ string_of_int last)
  | _ -> Sys_error ("Not such type: " ^ t) |> raise

let create_new_sstack (hl: security') =
  match hl with
  | High h ->
     let s1 = create_new_symb h "int" in
     let s2 = create_new_symb h "int" in
     Double (Symb s1, Symb s2)
  | Low l ->
     let s = create_new_symb l "int" in
     Single (Symb s)


(* Get the symbolic expression for variable x *)
(* let get_var x =
 *   Map.find x !map_var_expr *)

(* Set the symbolic expression for variable x (assign) *)
(* let set_var x expr =
 *   map_var_expr := Map.add x expr !map_var_expr *)



let add e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1+i2))
  | _ -> SAdd (e1, e2)

let sub e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1-i2))
  | _ -> SSub (e1, e2)

let mul e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1*i2))
  | _ -> SMul (e1, e2)

let div e1 e2 = SDiv (e1, e2) (*float*)
let min e1 e2 = SMin (e1, e2) (*float*)
let max e1 e2 = SMax (e1, e2) (*float*)
let copysign e1 e2 = SCopySign (e1, e2) (*float*)

let divu e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal 0) -> raise Division_by_zero
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1/i2))
  | _ -> SDivU (e1, e2)

let divs e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal 0) -> raise Division_by_zero
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1/i2))
  | _ -> SDivS (e1, e2)

let remu e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal 0) -> raise Division_by_zero
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 mod i2))
  | _ -> SRemU (e1, e2)

let rems e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal 0) -> raise Division_by_zero
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 mod i2))
  | _ -> SRemS (e1, e2)

let neg e = SNeg (e) (*float*)
let clz e = SClz (e)

let sand e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 land i2))
  | _ -> SAnd  (e1, e2)

let sor e1 e2  =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 lor i2))
  | _ -> SOr   (e1, e2)

let xor e1 e2  =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 lxor i2))
  | _ -> SXor  (e1, e2)

let shl e1 e2  =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 lsl i2))
  | _ -> SShl  (e1, e2)

let shrs e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 lsr i2))
  | _ -> SShrS  (e1, e2)

let shru e1 e2 =
  match (e1, e2) with
  | Symb(IntVal i1), Symb(IntVal i2) -> Symb(IntVal (i1 lsr i2))
  | _ -> SShrU (e1, e2)

let rotl e1 e2 = SRotl (e1, e2)
let rotr e1 e2 = SRotr (e1, e2)

let ges e1 e2 = Ite( GeS (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let geu e1 e2 = Ite( GeU (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let gts e1 e2 = Ite( GtS (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let gtu e1 e2 = Ite( GtU (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let les e1 e2 = Ite( LeS (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let leu e1 e2 = Ite( LeU (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let lts e1 e2 = Ite( LtS (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let ltu e1 e2 = Ite( LtU (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let eq e1 e2 = Ite( Eq (e1, e2), Symb (IntVal 1), Symb (IntVal 0))
let ne e1 e2 = Ite( Ne (e1, e2), Symb (IntVal 1), Symb (IntVal 0))

let eqz e = Ite (Eqz e, Symb (IntVal 1), Symb (IntVal 0))

let bin_op op e1 e2 =
  match (e1,e2) with
  | (Single e1', Single e2') -> Single (op e1' e2')
  | (Single e1', Double (e2', e2''))
    | (Double (e2', e2''), Single e1') -> Double (op e2' e1', op e2'' e1')
  | (Double (e1', e1''), Double (e2', e2'')) -> Double (op e2' e1', op e2'' e1'')

let uni_op op e =
  match e with
  | Single e' -> Single (op e')
  | Double (e1, e2) -> Double (op e1, op e2)


let const_to_symb c =
  let sv =
    match c with
    | I32 i -> IntVal (I32.to_int_s i)
    | I64 i -> IntVal (I64.to_int_s i)
    | F32 f -> RealVal (F32.to_float f)
    | F64 f -> RealVal (F64.to_float f)
  in Single ( Symb sv)

let symb_bin binop s1 s2 =
     let symb_bin_i x s1 s2 =
       (match x with
        | Ast.IntOp.Add -> bin_op add s1 s2
        | Ast.IntOp.Sub -> bin_op sub s1 s2
        | Ast.IntOp.Mul -> bin_op mul s1 s2
        | Ast.IntOp.DivS -> bin_op divs s1 s2
        | Ast.IntOp.DivU -> bin_op divu s1 s2
        | Ast.IntOp.RemS -> bin_op rems s1 s2
        | Ast.IntOp.RemU -> bin_op remu s1 s2
        | Ast.IntOp.And -> bin_op sand s1 s2
        | Ast.IntOp.Or -> bin_op sor s1 s2
        | Ast.IntOp.Xor -> bin_op xor s1 s2
        | Ast.IntOp.Shl -> bin_op shl s1 s2
        | Ast.IntOp.ShrS -> bin_op shrs s1 s2
        | Ast.IntOp.ShrU -> bin_op shru s1 s2
        | Ast.IntOp.Rotl -> bin_op rotl s1 s2
        | Ast.IntOp.Rotr -> bin_op rotr s1 s2
       ) in
     let symb_bin_f x s1 s2 =
       (match x with
        | Ast.FloatOp.Add -> bin_op add s1 s2
        | Ast.FloatOp.Sub -> bin_op sub s1 s2
        | Ast.FloatOp.Mul -> bin_op mul s1 s2
        | Ast.FloatOp.Div -> bin_op div s1 s2
        | Ast.FloatOp.Min -> bin_op min s1 s2
        | Ast.FloatOp.Max -> bin_op max s1 s2
        | Ast.FloatOp.CopySign -> bin_op copysign s1 s2
    ) in
  match binop with
  | I32 x | I64 x -> symb_bin_i x s1 s2
  | F32 x | F64 x -> symb_bin_f x s1 s2

let symb_comp relop s1 s2 =
     let symb_comp_i x s1 s2 =
       (match x with
        | Ast.IntOp.Eq ->  bin_op eq s1 s2
        | Ast.IntOp.Ne ->  bin_op ne s1 s2
        | Ast.IntOp.LtS -> bin_op lts s1 s2
        | Ast.IntOp.LtU -> bin_op ltu s1 s2
        | Ast.IntOp.GtS -> bin_op gts s1 s2
        | Ast.IntOp.GtU -> bin_op gtu s1 s2
        | Ast.IntOp.LeS -> bin_op les s1 s2
        | Ast.IntOp.LeU -> bin_op leu s1 s2
        | Ast.IntOp.GeS -> bin_op ges s1 s2
        | Ast.IntOp.GeU -> bin_op geu s1 s2
       ) in
     let symb_comp_f x s1 s2 =
       (match x with
        | Ast.FloatOp.Eq -> bin_op eq s1 s2
        | Ast.FloatOp.Ne -> bin_op ne s1 s2
        | Ast.FloatOp.Lt -> bin_op lts s1 s2
        | Ast.FloatOp.Gt -> bin_op gts s1 s2
        | Ast.FloatOp.Le -> bin_op les s1 s2
        | Ast.FloatOp.Ge -> bin_op ges s1 s2
    ) in
  match relop with
  | I32 x | I64 x -> symb_comp_i x s1 s2
  | F32 x | F64 x -> symb_comp_f x s1 s2


let symb_uni uniop s1 =
  let symb_uni_i x s1 =
    (match x with
     | Ast.IntOp.Clz -> uni_op clz s1
     | _ -> uni_op clz s1
    ) in
  let symb_uni_f x s2 =
    (match x with
     | Ast.FloatOp.Neg -> uni_op neg s1
     | _ -> uni_op neg s1
    ) in
  match uniop with
  | I32 x | I64 x -> symb_uni_i x s1
  | F32 x | F64 x -> symb_uni_f x s1


let symb_test testop s1 =
  let symb_uni_i x s1 =
    (match x with
     | Ast.IntOp.Eqz -> uni_op eqz s1
    ) in
  match testop with
  | I32 x | I64 x -> symb_uni_i x s1
  (* TODO(Romy): replace with error *)
  | _ -> Single( Symb (IntVal (-1)))



let symb_ite b s1 s2 =
  match (b, s1, s2) with
  | (Double (b', b''), Double (e1', e1''), Double (e2', e2'')) ->
     Double (Ite(b', e1', e2'), Ite(b'', e1'', e2''))
  | (Double (b', b''), Single (e1'), Double (e2', e2'')) ->
     Double (Ite(b', e1', e2'), Ite(b'', e1', e2''))
  | (Double (b', b''), Double (e1', e1''), Single (e2')) ->
     Double (Ite(b', e1', e2'), Ite(b'', e1'', e2'))
  | (Double (b', b''), Single (e1'), Single (e2')) ->
     Double (Ite(b', e1', e2'), Ite(b'', e1', e2'))
  | (Single(b'), Double (e1', e1''), Double (e2', e2'')) ->
     Double (Ite(b', e1', e2'), Ite(b', e1'', e2''))
  | (Single(b'), Single (e1'), Double (e2', e2'')) ->
     Double (Ite(b', e1', e2'), Ite(b', e1', e2''))
  | (Single (b'), Double (e1', e1''), Single (e2')) ->
     Double (Ite(b', e1', e2'), Ite(b', e1'', e2'))
  | (Single (b'), Single (e1'), Single (e2')) ->
     Single (Ite(b', e1', e2'))


(*******************************
     PRINT FUNCTIONS
 *******************************)
let print_symb s =
  match s with
  | Integ str | Bitmap str | Real str -> str
  | IntVal i -> string_of_int i
  | RealVal r -> string_of_float r

let rec print_expr e =
  match e with
  | Symb s -> print_symb s
  | SNeg e -> "-" ^ (print_expr e)
  (* No idea what clz is *)
  | SClz e -> "?" ^ (print_expr e)
  | SAdd (e1,e2) -> (print_expr e1) ^ " + " ^ (print_expr e2)
  | SSub (e1,e2) -> (print_expr e1) ^ " - " ^ (print_expr e2)
  | SMul (e1,e2) -> (print_expr e1) ^ " * " ^ (print_expr e2)
  | SDiv (e1,e2) -> (print_expr e1) ^ " / " ^ (print_expr e2)
  | SMin (e1,e2) ->  "min(" ^ (print_expr e1) ^ ", " ^ (print_expr e2) ^ ")"
  | SMax (e1,e2) ->  "max(" ^ (print_expr e1) ^ ", " ^ (print_expr e2) ^ ")"
  | SCopySign (e1,e2) -> "copy_sign(" ^ (print_expr e1) ^ ", " ^ (print_expr e2) ^ ")"
  | SDivU (e1,e2) -> (print_expr e1) ^ " / " ^ (print_expr e2)
  | SDivS (e1,e2) -> (print_expr e1) ^ " / " ^ (print_expr e2)
  | SRemU (e1,e2) -> (print_expr e1) ^ " % " ^ (print_expr e2)
  | SRemS (e1,e2) -> (print_expr e1) ^ " % " ^ (print_expr e2)
  | SAnd (e1,e2) -> (print_expr e1) ^ " ^ " ^ (print_expr e2)
  | SOr (e1,e2) -> (print_expr e1) ^ " v " ^ (print_expr e2)
  | SXor (e1,e2) -> (print_expr e1) ^ " x " ^ (print_expr e2)
  | SShl (e1,e2) -> (print_expr e1) ^ " << " ^ (print_expr e2)
  | SShrS (e1,e2) -> (print_expr e1) ^ " >> " ^ (print_expr e2)
  | SShrU (e1,e2) -> (print_expr e1) ^ " >> " ^ (print_expr e2)
  | SRotl (e1,e2) -> (print_expr e1) ^ " >>| " ^ (print_expr e2)
  | SRotr (e1,e2) -> (print_expr e1) ^ " |<< " ^ (print_expr e2)
  (*Conditions*)
  | GeS (e1,e2) -> (print_expr e1) ^ " >= " ^ (print_expr e2)
  | GeU (e1,e2) -> (print_expr e1) ^ " >= " ^ (print_expr e2)
  | GtS (e1,e2) -> (print_expr e1) ^ " > " ^ (print_expr e2)
  | GtU (e1,e2) -> (print_expr e1) ^ " > " ^ (print_expr e2)
  | LeS (e1,e2) -> (print_expr e1) ^ " <= " ^ (print_expr e2)
  | LeU (e1,e2) -> (print_expr e1) ^ " <= " ^ (print_expr e2)
  | LtS (e1,e2) -> (print_expr e1) ^ " < " ^ (print_expr e2)
  | LtU (e1,e2) -> (print_expr e1) ^ " < " ^ (print_expr e2)
  | Eq  (e1,e2) -> (print_expr e1) ^ " == " ^ (print_expr e2)
  | Ne  (e1,e2) -> (print_expr e1) ^ " != " ^ (print_expr e2)
  (* Others *)
  | Ite (b,e1,e2) -> "ite (" ^ (print_expr b) ^ ",  "
                     ^ (print_expr e1) ^ ", " ^ (print_expr e2) ^ ")"
  | Eqz  e -> (print_expr e) ^ " == 0 "


let print_sstack se =
  match se with
  | Single e -> print_expr e
  | Double (e1, e2) -> "(" ^ (print_expr e1) ^ ", " ^ (print_expr e2) ^ ")"

let rec print_pc c =
  match c with
  | P (tf) -> string_of_bool tf
  | CEqz (s) -> "(" ^ print_sstack s ^ "== 0 " ^ ")"
  | CNez (s) -> "(" ^ print_sstack s ^ "!= 0 " ^ ")"
  | PAnd (c1, c2) -> print_pc c1 ^ " ^ " ^ print_pc c2



(*******************************
    STEP FUNCTION
 *******************************)
type 'a stack = 'a list

type frame =
{
  inst : module_inst;
  locals : sstack ref list; (* Check if it works with multiple paths *)
}

type code = sstack stack * admin_instr list
and admin_instr = admin_instr' phrase
and admin_instr' =
  | Plain of instr'
  | Frame of int32 * frame * code
  | SymbEx of func_inst
  | Label of int32 * instr list * code
  | Breaking of int32 * sstack stack
  | Returning of sstack stack
  | Trapping of string
(* and admin_instr = admin_instr' phrase
 * and admin_instr' =
 *   | Invoke of func_inst
 *   | Trapping of string
 *   | Breaking of int32 * value stack
*)

type state =
  { frame: frame;
    code : code;
    pc: cond}

let frame inst locals = {inst; locals}
let state inst svs es = {frame = frame inst []; code = svs, es; pc = P true}

(* To symb*)
let lookup category list x =
  try Lib.List32.nth list x.it with Failure _ ->
    Crash.error x.at ("undefined " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (inst : module_inst) x = lookup "type" inst.types x
(* let global (inst : module_inst) x = lookup "global" inst.globals x *)
let local (frame : frame) x = lookup "local" frame.locals x


let block_type inst bt =
  match bt with
  | VarBlockType x -> type_ inst x
  | ValBlockType None -> FuncType ([], [])
  | ValBlockType (Some t) -> FuncType ([], [t])

let take n (vs : 'a stack) at =
  try Lib.List32.take n vs with Failure _ -> Crash.error at "stack underflow"

let drop n (vs : 'a stack) at =
  try Lib.List32.drop n vs with Failure _ -> Crash.error at "stack underflow"

let default_sec = function
  | _ -> Single (Symb (IntVal 0))

let plain e = Plain e.it @@ e.at

let rec step (c : state) : state list =
  let {frame; code = svs, es; pc} = c in
  let e = List.hd es in
  (* let frame', es', svs' = *)
    match e.it, svs with
    | Plain e', svs ->
       (match e', svs with
        | Unreachable, svs ->
           [{c with code = svs, List.tl es}] (*Todo(Romy): Trap *)
        | Nop, svs ->
           [{c with code = svs, List.tl es}]
        | Drop, v :: svs ->
           [{c with code = svs, List.tl es}]
        | Const v, svs ->
           let sv = const_to_symb v.it in
           [{c with code = sv:: svs, List.tl es}]
        | LocalGet x, svs ->
           let sv = !(local frame x) in
           [{c with code = sv:: svs, List.tl es}]
        | LocalSet x, sv :: svs ->
           local frame x := sv;
           [{c with code = svs, List.tl es}]
        | LocalTee x, sv :: svs ->
           local frame x := sv;
           [{c with code = sv:: svs, List.tl es}]
        (* | GlobalGet x, svs ->
         *    let gl = Symbglobal.load (global frame.inst x) in
         *    [{c with code = gl :: svs, List.tl es}]
         *    (\* Global.load (global frame.inst x) :: vs, [] *\)
         * | GlobalSet x, sv :: svs' ->
         *    (try
         *       Symbglobal.store (global frame.inst x) sv;
         *       [{c with code = svs', List.tl es}]
         *       (\* ; svs', [] *\)
         *     with Symbglobal.NotMutable -> Crash.error e.at "write to immutable global")
         *        (\* | Symbglobal.Type -> Crash.error e.at "type mismatch at global write") *\) *)
       (* | Load {offset; ty; sz; _}, I32 i :: vs' ->
        *   let mem = memory frame.inst (0l @@ e.at) in
        *   let addr = I64_convert.extend_i32_u i in
        *   (try
        *     let v =
        *       match sz with
        *       | None -> Memory.load_value mem addr offset ty
        *       | Some (sz, ext) -> Memory.load_packed sz ext mem addr offset ty
        *     in v :: vs', []
        *   with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at])
        *
        * | Store {offset; sz; _}, v :: I32 i :: vs' ->
        *   let mem = memory frame.inst (0l @@ e.at) in
        *   let addr = I64_convert.extend_i32_u i in
        *   (try
        *     (match sz with
        *     | None -> Memory.store_value mem addr offset v
        *     | Some sz -> Memory.store_packed sz mem addr offset v
        *     );
        *     vs', []
        *   with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at]);
        *
        * | MemorySize, vs ->
        *   let mem = memory frame.inst (0l @@ e.at) in
        *   I32 (Memory.size mem) :: vs, []
        *
        * | MemoryGrow, I32 delta :: vs' ->
        *   let mem = memory frame.inst (0l @@ e.at) in
        *   let old_size = Memory.size mem in
        *   let result =
        *     try Memory.grow mem delta; old_size
        *     with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
        *   in I32 result :: vs', [] *)

        | Return, svs ->
           [{c with code = svs, (Returning svs @@ e.at) :: List.tl es}]
        | Binary binop, s2 :: s1 :: svs ->
           (try
              [{c with code = symb_bin binop s1 s2 :: svs, List.tl es}]
            with exn -> [{c with code = svs,
                                        (Trapping (numeric_error e.at exn) @@ e.at) :: List.tl es}])
        | Unary unop, sv :: svs ->
           (try
              [{c with code = symb_uni unop sv :: svs, List.tl es}]
            with exn -> [{c with code = svs,
                                        (Trapping (numeric_error e.at exn) @@ e.at) :: List.tl es}])
        | Compare relop, s2 :: s1 :: svs ->
           (try
              [{c with code = symb_comp relop s1 s2 :: svs, List.tl es}]
            with exn -> [{c with code = svs,
                                        (Trapping (numeric_error e.at exn) @@ e.at) :: List.tl es}])
        | Test testop, s :: svs' ->
           (try
              [{c with code = symb_test testop s :: svs', List.tl es}]

            with exn -> [{c with code = svs,
                                        (Trapping (numeric_error e.at exn) @@ e.at) :: List.tl es}])
        (* | Convert cvtop, v :: vs' ->
         *    (try Eval_numeric.eval_cvtop cvtop v :: vs', []
         *     with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) *)

        | Block (bt, es'), svs ->
           print_endline "Block";
           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let n2 = Lib.List32.length ts2 in
           let args, svs' = take n1 svs e.at, drop n1 svs e.at in
           let es' = Label (n2, [], (args, List.map plain es')) @@ e.at in
           [{c with code = svs', es' :: List.tl es}]

        (* | Loop (bt, es'), vs ->
         *    let FuncType (ts1, ts2) = block_type frame.inst bt in
         *    let n1 = Lib.List32.length ts1 in
         *    let args, vs' = take n1 vs e.at, drop n1 vs e.at in
         *    vs', [Label (n1, [e' @@ e.at], (args, List.map plain es')) @@ e.at] *)


        | Select, sc :: sv2 :: sv1 :: svs' ->
           let ite = symb_ite sc sv2 sv1 in
           [{c with code = ite :: svs', List.tl es}]

        | If (bt, es1, es2), b :: svs' ->
           let s1 = {c with code = svs', (Plain (Block (bt, es1)) @@ e.at) :: List.tl es; pc = PAnd (pc, CNez b)} in
           let s2 = {c with code = svs', (Plain (Block (bt, es2)) @@ e.at) :: List.tl es; pc = PAnd (pc, CEqz b)} in
           [s1; s2]

        | Br x, svs ->
           (* print_endline "BrIf"; *)
           [{c with code = svs, (Breaking (x.it, svs) @@ e.at)::List.tl es}]

        | BrIf x, b :: svs' ->
           (* print_endline "BrIf"; *)
           let s1 = {c with code = svs', (Plain (Br x) @@ e.at) :: List.tl es; pc = PAnd (pc, CNez b)} in
           let s2 = {c with code = svs', List.tl es; pc = PAnd (pc, CEqz b)} in
           [s1; s2]

        | _, svs ->
           [{c with code = svs, List.tl es}]
       )
    | Trapping msg, svs ->
        assert false

    | Returning svs', svs ->
       Crash.error e.at "undefined frame"

    (* | SymbEx func, vs when c.budget = 0 ->
     *   Exhaustion.error e.at "call stack exhausted" *)

    | SymbEx func, svs ->
      let FuncType (ins, out) = Func.type_of func in
      let n1, n2 = Lib.List32.length ins, Lib.List32.length out in
      let args, svs' = take n1 svs e.at, drop n1 svs e.at in
      (match func with
      | Func.AstFunc (t, inst', f) ->
        let locals' = args @ List.map default_sec f.it.locals in
        let frame' = {inst = !inst'; locals = List.map ref locals'} in
        let instr' = [Label (n2, [], ([], List.map plain f.it.body)) @@ f.at] in
        let es' = Frame (n2, frame', ([], instr')) @@ e.at in
        [{c with code = svs', es' :: List.tl es}]


      | Func.HostFunc (t, f) ->
        (* try [], List.rev (f (List.rev args)) @ svs'
         * with
         *  Crash (_, msg) -> *)
         Crash.error e.at "Not implemented Func.HostFunc."
      )
    | Label (n, es0, (svs', {it = Trapping msg; at} :: es')), svs ->
       [{c with code = svs, (Trapping msg @@ at) :: List.tl es}]

    | Label (n, es0, (vs', {it = Returning vs0; at} :: es')), vs ->
       [{c with code = svs, (Returning vs0 @@ at) :: List.tl es}]

    | Label (n, es0, (svs', {it = Breaking (0l, vs0); at} :: es')), svs ->
       let svs'' = take n vs0 e.at @ svs in
       let plains = List.map plain es0 in
       [{c with code = svs'', plains @ List.tl es}]

    | Label (n, es0, (svs', {it = Breaking (k, vs0); at} :: es')), svs ->
       let br = Breaking (Int32.sub k 1l, vs0) @@ at in
       [{c with code = svs, br :: List.tl es}]

    | Label (n, es0, (svs', [])), svs ->
       [{c with code = svs' @ svs, List.tl es}]

    (* TODO(Romy): Check ignores the branches *)
    | Label (n, es0, code'), svs ->
       let c' = step {c with code = code'} in

       List.map (fun c'' ->
           {c'' with code = svs, (Label (n, es0, c''.code) @@ e.at) :: List.tl es}) c'

    | Frame (n, frame', (svs', [])), svs ->
       [{c with code = svs'@ svs, List.tl es}]

    | Frame (n, frame', (svs', {it = Trapping msg; at} :: es')), svs ->
       [{c with code = svs, (Trapping msg @@ at) :: List.tl es}]

    | Frame (n, frame', (svs', {it = Returning vs0; at} :: es')), svs ->
       [{c with code = take n vs0 e.at @ svs, List.tl es}]

    (* TODO(Romy): Check ignores the branches *)
    | Frame (n, frame', code'), svs ->
       let c' = step {frame = frame'; code = code'; pc} in
       List.map (fun c'' ->
           {c'' with code = svs, (Frame (n, c''.frame, c''.code) @@ e.at) :: List.tl es}) c'

    | Breaking (k, vs'), vs ->
       print_endline "Breaking";
       Crash.error e.at "undefined label"

(* let rec step (c : config) : config =
 *   let {frame; code = vs, es; _} = c in
 *   let e = List.hd es in
 *   let vs', es' =
 *     match e.it, vs with
 *     | Plain e', vs ->
 *       (match e', vs with
 *       | Unreachable, vs ->
 *         vs, [Trapping "unreachable executed" @@ e.at]
 *
 *       | Nop, vs ->
 *         vs, []
 *
 *       | Block (bt, es'), vs ->
 *         let FuncType (ts1, ts2) = block_type frame.inst bt in
 *         let n1 = Lib.List32.length ts1 in
 *         let n2 = Lib.List32.length ts2 in
 *         let args, vs' = take n1 vs e.at, drop n1 vs e.at in
 *         vs', [Label (n2, [], (args, List.map plain es')) @@ e.at]
 *
 *       | Loop (bt, es'), vs ->
 *         let FuncType (ts1, ts2) = block_type frame.inst bt in
 *         let n1 = Lib.List32.length ts1 in
 *         let args, vs' = take n1 vs e.at, drop n1 vs e.at in
 *         vs', [Label (n1, [e' @@ e.at], (args, List.map plain es')) @@ e.at]
 *
 *       | If (bt, es1, es2), I32 0l :: vs' ->
 *         vs', [Plain (Block (bt, es2)) @@ e.at]
 *
 *       | If (bt, es1, es2), I32 i :: vs' ->
 *         vs', [Plain (Block (bt, es1)) @@ e.at]
 *
 *       | Br x, vs ->
 *         [], [Breaking (x.it, vs) @@ e.at]
 *
 *       | BrIf x, I32 0l :: vs' ->
 *         vs', []
 *
 *       | BrIf x, I32 i :: vs' ->
 *         vs', [Plain (Br x) @@ e.at]
 *
 *       | BrTable (xs, x), I32 i :: vs' when I32.ge_u i (Lib.List32.length xs) ->
 *         vs', [Plain (Br x) @@ e.at]
 *
 *       | BrTable (xs, x), I32 i :: vs' ->
 *         vs', [Plain (Br (Lib.List32.nth xs i)) @@ e.at]
 *
 *       | Return, vs ->
 *         [], [Returning vs @@ e.at]
 *
 *       | Call x, vs ->
 *         vs, [Invoke (func frame.inst x) @@ e.at]
 *
 *       | CallIndirect x, I32 i :: vs ->
 *         let func = func_elem frame.inst (0l @@ e.at) i e.at in
 *         if type_ frame.inst x <> Func.type_of func then
 *           vs, [Trapping "indirect call type mismatch" @@ e.at]
 *         else
 *           vs, [Invoke func @@ e.at]
 *
 *       | Drop, v :: vs' ->
 *         vs', []
 *
 *       | Select, I32 0l :: v2 :: v1 :: vs' ->
 *         v2 :: vs', []
 *
 *       | Select, I32 i :: v2 :: v1 :: vs' ->
 *         v1 :: vs', []
 *
 *       | LocalGet x, vs ->
 *         !(local frame x) :: vs, []
 *
 *       | LocalSet x, v :: vs' ->
 *         local frame x := v;
 *         vs', []
 *
 *       | LocalTee x, v :: vs' ->
 *         local frame x := v;
 *         v :: vs', []
 *
 *       | GlobalGet x, vs ->
 *         Global.load (global frame.inst x) :: vs, []
 *
 *       | GlobalSet x, v :: vs' ->
 *         (try Global.store (global frame.inst x) v; vs', []
 *         with Global.NotMutable -> Crash.error e.at "write to immutable global"
 *            | Global.Type -> Crash.error e.at "type mismatch at global write")
 *
 *       | Load {offset; ty; sz; _}, I32 i :: vs' ->
 *         let mem = memory frame.inst (0l @@ e.at) in
 *         let addr = I64_convert.extend_i32_u i in
 *         (try
 *           let v =
 *             match sz with
 *             | None -> Memory.load_value mem addr offset ty
 *             | Some (sz, ext) -> Memory.load_packed sz ext mem addr offset ty
 *           in v :: vs', []
 *         with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at])
 *
 *       | Store {offset; sz; _}, v :: I32 i :: vs' ->
 *         let mem = memory frame.inst (0l @@ e.at) in
 *         let addr = I64_convert.extend_i32_u i in
 *         (try
 *           (match sz with
 *           | None -> Memory.store_value mem addr offset v
 *           | Some sz -> Memory.store_packed sz mem addr offset v
 *           );
 *           vs', []
 *         with exn -> vs', [Trapping (memory_error e.at exn) @@ e.at]);
 *
 *       | MemorySize, vs ->
 *         let mem = memory frame.inst (0l @@ e.at) in
 *         I32 (Memory.size mem) :: vs, []
 *
 *       | MemoryGrow, I32 delta :: vs' ->
 *         let mem = memory frame.inst (0l @@ e.at) in
 *         let old_size = Memory.size mem in
 *         let result =
 *           try Memory.grow mem delta; old_size
 *           with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
 *         in I32 result :: vs', []
 *
 *       | Const v, vs ->
 *         v.it :: vs, []
 *
 *       | Test testop, v :: vs' ->
 *         (try value_of_bool (Eval_numeric.eval_testop testop v) :: vs', []
 *         with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
 *
 *       | Compare relop, v2 :: v1 :: vs' ->
 *         (try value_of_bool (Eval_numeric.eval_relop relop v1 v2) :: vs', []
 *         with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
 *
 *       | Unary unop, v :: vs' ->
 *         (try Eval_numeric.eval_unop unop v :: vs', []
 *         with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
 *
 *       | Binary binop, v2 :: v1 :: vs' ->
 *         (try Eval_numeric.eval_binop binop v1 v2 :: vs', []
 *         with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
 *
 *       | Convert cvtop, v :: vs' ->
 *         (try Eval_numeric.eval_cvtop cvtop v :: vs', []
 *         with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
 *
 *       | _ ->
 *         let s1 = string_of_values (List.rev vs) in
 *         let s2 = string_of_value_types (List.map type_of (List.rev vs)) in
 *         Crash.error e.at
 *           ("missing or ill-typed operand on stack (" ^ s1 ^ " : " ^ s2 ^ ")")
 *       )
 *
 *     | Trapping msg, vs ->
 *       assert false
 *
 *     | Returning vs', vs ->
 *       Crash.error e.at "undefined frame"
 *
 *     | Breaking (k, vs'), vs ->
 *       Crash.error e.at "undefined label"
 *
 *     | Label (n, es0, (vs', [])), vs ->
 *       vs' @ vs, []
 *
 *     | Label (n, es0, (vs', {it = Trapping msg; at} :: es')), vs ->
 *       vs, [Trapping msg @@ at]
 *
 *     | Label (n, es0, (vs', {it = Returning vs0; at} :: es')), vs ->
 *       vs, [Returning vs0 @@ at]
 *
 *     | Label (n, es0, (vs', {it = Breaking (0l, vs0); at} :: es')), vs ->
 *       take n vs0 e.at @ vs, List.map plain es0
 *
 *     | Label (n, es0, (vs', {it = Breaking (k, vs0); at} :: es')), vs ->
 *       vs, [Breaking (Int32.sub k 1l, vs0) @@ at]
 *
 *     | Label (n, es0, code'), vs ->
 *       let c' = step {c with code = code'} in
 *       vs, [Label (n, es0, c'.code) @@ e.at]
 *
 *     | Frame (n, frame', (vs', [])), vs ->
 *       vs' @ vs, []
 *
 *     | Frame (n, frame', (vs', {it = Trapping msg; at} :: es')), vs ->
 *       vs, [Trapping msg @@ at]
 *
 *     | Frame (n, frame', (vs', {it = Returning vs0; at} :: es')), vs ->
 *       take n vs0 e.at @ vs, []
 *
 *     | Frame (n, frame', code'), vs ->
 *       let c' = step {frame = frame'; code = code'; budget = c.budget - 1} in
 *       vs, [Frame (n, c'.frame, c'.code) @@ e.at]
 *
 *     | Invoke func, vs when c.budget = 0 ->
 *       Exhaustion.error e.at "call stack exhausted"
 *
 *     | Invoke func, vs ->
 *       let FuncType (ins, out) = func_type_of func in
 *       let n1, n2 = Lib.List32.length ins, Lib.List32.length out in
 *       let args, vs' = take n1 vs e.at, drop n1 vs e.at in
 *       (match func with
 *       | Func.AstFunc (t, inst', f) ->
 *         let locals' = List.rev args @ List.map default_value f.it.locals in
 *         let frame' = {inst = !inst'; locals = List.map ref locals'} in
 *         let instr' = [Label (n2, [], ([], List.map plain f.it.body)) @@ f.at] in
 *         vs', [Frame (n2, frame', ([], instr')) @@ e.at]
 *
 *       | Func.HostFunc (t, f) ->
 *         try List.rev (f (List.rev args)) @ vs', []
 *         with Crash (_, msg) -> Crash.error e.at msg
 *       )
 *   in {c with code = vs', es' @ List.tl es} *)



let rec symbexec (cs : state list) : (sstack stack * cond) list =
  match cs with
  | [] -> []
  | c :: cs' ->
     (match c.code with
      | vs, [] -> (vs, c.pc) :: symbexec cs'
      | vs, es ->
         let ns = step c in
         (* TODO(Romy): Sort ns *)
         symbexec (ns @ cs')
     )



let run (func : func_inst) (secs : security' list) : string list =
  let at = match func with Func.AstFunc (_,_, f) -> f.at | _ -> no_region in
  let FuncType (ins, out) = Func.type_of func in
  (* TODO(Romy): check if float *)
  if List.length secs <> List.length ins then
    Crash.error at "wrong number of arguments";
  let svs = List.map create_new_sstack secs in
  let c = state empty_module_inst svs [SymbEx func @@ at] in
  let slist = symbexec [c] in
  let symbolicstack = List.map (fun (sl,_) -> List.fold_left (fun a b -> a ^ " " ^ print_sstack b ^ " |||| ") "" sl) slist in
  let pc = List.map (fun (_,pc)-> print_pc pc) slist in
  symbolicstack @ pc;
  (* try List.rev (sym_run c) with Stack_overflow ->
   *   Exhaustion.error at "call stack exhausted" *)


(* let dummy () =
 *   let s = create_new_symb "x" "int" in
 *   match s with
 *   | Integ str -> str
 *   | _ -> "mal" *)
