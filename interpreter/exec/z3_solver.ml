open Pc_type
open Z3
open Svalues
open Smt_type
(* open Z3.Symbol
 * open Z3.BitVector *)


(* open Z3.Boolean
 * open Z3.Goal *)

(* open Unix *)
(* open Sys *)
(* open Filename
 *    
 * let run_solver() =
 *   let ret = Sys.command "ls" in
 *   print_endline (string_of_int ret)
 *   (\* execve "ls" [|"ls"; "-l"; "/tmp"|] (environment ()) *\)
 *   
 * let solve_z3 (_ : pc) =
 *   let oc = open_out "filename.smt" in
 *   let tmp = temp_file ~temp_dir:"./" "swasm" ".smt" in
 *   print_endline tmp;
 *   Printf.fprintf oc "(echo \"Starting solver\")\n";
 *   Printf.fprintf oc "(declare-const n (_ BitVec 32))\n";
 *   Printf.fprintf oc "(assert (not (= n #x00000000)))\n";
 *   Printf.fprintf oc "(assert (= n #x00000000))\n";
 *   Printf.fprintf oc "(check-sat)\n";
 *   Printf.fprintf oc "(get-model)\n";
 *   Printf.fprintf oc "(echo \"Done\")\n";
 *   close_out oc;
 *   run_solver (); *)
(* TODO(Romy): implement rest *)

type rel_type = L of Expr.expr | H of Expr.expr * Expr.expr

let print_exp exp =
  (match exp with
      | L e ->
         print_endline "print_exp: L e";
         print_endline (Expr.to_string e);
      | H (e1, e2) ->
         print_endline "print_exp: H (e1,e2)";
         print_endline (Expr.to_string e1);
         print_endline (Expr.to_string e2);
  )

let propagate_policy f e1 e2 =
  (match e1,e2 with
   | L e1, L e2 -> L (f e1 e2)
   | L e1, H (e21,e22) -> H (f e1 e21, f e1 e22)
   | H (e11,e12), L e2 -> H (f e11 e2, f e12 e2)
   | H (e11,e12), H (e21,e22) -> H (f e11 e21, f e12 e22)
  )

let propagate_policy_three f e1 e2 e3 =
  (match e1,e2,e3 with
   | L e1, L e2, L e3 ->  L (f e1 e2 e3)
   | L e1, L e2, H (e31,e32)  ->  H (f e1 e2 e31, f e1 e2 e32)
   | L e1, H (e21,e22), L e3  ->  H (f e1 e21 e3, f e1 e22 e3)
   | H (e11,e12), L e2, L e3  ->  H (f e11 e2 e3, f e12 e2 e3)
   | H (e11,e12), H (e21,e22), L e3  ->  H (f e11 e21 e3, f e12 e22 e3)
   | H (e11,e12), L e2, H (e31,e32)  ->  H (f e11 e2 e31, f e12 e2 e32)
   | L e1, H (e21, e22), H (e31,e32)  ->  H (f e1 e21 e31, f e1 e22 e32)
   | H (e11,e12), H (e21,e22), H(e31,e32) ->  H (f e11 e21 e31, f e12 e22 e32)
  )

let propagate_policy_one f e =
  (match e with
   | L e ->  L (f e)
   | H (e1,e2) ->  H (f e1, f e2)
  )

let propagate_list f es =
  let rec propagate_list_i es h l is_h =
    match es with
    | L e::res -> propagate_list_i res (e::h) (e::l) is_h 
    | H (e1,e2)::res -> propagate_list_i res (e1::h) (e2::l) true
    | [] -> (h,l,is_h)
  in
  let h,l,is_h = propagate_list_i es [] [] false in
  if is_h then H (f h, f l) else L (f l)
                                    
let rec si_to_expr size ctx si: rel_type  = 
  match si with
  | BitVec (i,n) ->
     let bv = BitVector.mk_sort ctx n  in
     L (Expr.mk_numeral_int ctx i bv)
  | Const (High i) ->
     H (BitVector.mk_const_s ctx ("h1_" ^ string_of_int i) size,
        BitVector.mk_const_s ctx ("h2_" ^ string_of_int i) size) 
  | Const (Low i) ->
     L (BitVector.mk_const_s ctx ("l_" ^ string_of_int i) size )
  | App (f, ts) ->
     app_to_expr ts size ctx f
  | _ -> failwith "String, Int, Float, Let are not implemented yet."

and app_to_expr ts size ctx f =
  match f, ts with
  | Ite, t1::t2::t3::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     let e3 = si_to_expr size ctx t3 in
     propagate_policy_three (Boolean.mk_ite ctx) e1 e2 e3
  | Ite, _ -> failwith "Not valid ite."

  | BvSlt, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_slt ctx) e1 e2
  | BvSlt, _ -> failwith "Not valid slt."
  | BvSle, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_sle ctx) e1 e2
  | BvSle, _ -> failwith "Not valid sle."
  | BvSgt, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_sgt ctx) e1 e2
  | BvSgt, _ -> failwith "Not valid sgt."
  | BvSge, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_sge ctx) e1 e2
  | BvSge, _ -> failwith "Not valid sge."

  | BvUlt, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_ult ctx) e1 e2
  | BvUlt, _ -> failwith "Not valid ult."
  | BvUle, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_ule ctx) e1 e2
  | BvUle, _ -> failwith "Not valid ule."
  | BvUgt, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_ugt ctx) e1 e2
  | BvUgt, _ -> failwith "Not valid ugt."
  | BvUge, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_uge ctx) e1 e2
  | BvUge, _ -> failwith "Not valid uge."

  | BvNot, t::[] ->
     let e = si_to_expr size ctx t in
     propagate_policy_one (BitVector.mk_not ctx) e
  | BvNot, _ -> failwith "Not valid not."
  | BvNeg, t::[] ->
     let e = si_to_expr size ctx t in
     propagate_policy_one (BitVector.mk_neg ctx) e
  | BvNeg, _ -> failwith "Not valid neg."

  | BvAnd, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_and ctx) e1 e2
  | BvAnd, _ -> failwith "Not valid bitwise addition."

  | BvOr, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_or ctx) e1 e2
  | BvOr, _ -> failwith "Not valid bitwise addition."

  | BvNand, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_nand ctx) e1 e2
  | BvNand, _ -> failwith "Not valid bitwise addition."

  | BvNor, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_nor ctx) e1 e2
  | BvNor, _ -> failwith "Not valid bitwise nor."

  | BvXNor, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_xnor ctx) e1 e2
  | BvXNor, _ -> failwith "Not valid bitwise xnor."

              
  | BvAdd, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_add ctx) e1 e2
  | BvAdd, _ -> failwith "Not valid bitwise addition."

  | BvSub, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_sub ctx) e1 e2
  | BvSub, _ -> failwith "Not valid bitwise subtraction."

  | BvMul, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_mul ctx) e1 e2
  | BvMul, _ -> failwith "Not valid bitwise multiplication."

  | BvURem, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_urem ctx) e1 e2
  | BvURem, _ -> failwith "Not valid bitwise uremainder."

  | BvSRem, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_srem ctx) e1 e2
  | BvSRem, _ -> failwith "Not valid bitwise sremainder."

  | BvSMod, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_smod ctx) e1 e2
  | BvSMod, _ -> failwith "Not valid bitwise s modulo."

  | BvShl, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_shl ctx) e1 e2
  | BvShl, _ -> failwith "Not valid bitwise sremainder."

  | BvLShr, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_lshr ctx) e1 e2
  | BvLShr, _ -> failwith "Not valid bitwise sremainder."

  | BvAShr, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (BitVector.mk_ashr ctx) e1 e2
  | BvAShr, _ -> failwith "Not valid bitwise sremainder."

  (* | BvDiv, t1::t2::[] ->
   *    let e1 = si_to_expr size ctx t1 in
   *    let e2 = si_to_expr size ctx t2 in
   *    propagate_policy (BitVector.mk_div ctx) e1 e2
   * | BvDiv, _ -> failwith "Not valid bitwise sremainder." *)

  | Eq, t1::t2::[] ->
     let e1 = si_to_expr size ctx t1 in
     let e2 = si_to_expr size ctx t2 in
     propagate_policy (Boolean.mk_eq ctx) e1 e2
  | Eq, _ -> failwith "Not valid equation."

  | Not, t::[] ->
     let e = si_to_expr size ctx t in
     propagate_policy_one (Boolean.mk_not ctx) e
  | Not, _ -> failwith "Not valid boolean not."


  | And, ts ->
     let es = List.map (si_to_expr size ctx) ts in
     propagate_list (Boolean.mk_and ctx) es 
  | Or, ts ->
     let es = List.map (si_to_expr size ctx) ts in
     propagate_list (Boolean.mk_or ctx) es 
  | _ -> failwith "Not implemented yet."

let sv_to_expr sv ctx =
    match sv with
    | SI32 si32 -> si_to_expr 32 ctx si32
    | SI64 si64 -> si_to_expr 64 ctx si64
    (*TODO(Romy): Not implemented*)
    | _ -> failwith "Float not implemented."


let rec pc_to_expr pc ctx: rel_type =
  match pc with
  | PCTrue -> L (Boolean.mk_true ctx)
  | PCFalse -> L (Boolean.mk_false ctx)
  | PCAnd (sv, pc) ->
     let ex1 = sv_to_expr sv ctx in
     let ex2 = pc_to_expr pc ctx in
     propagate_list (Boolean.mk_and ctx) [ex1; ex2] 


   
let solve_z3 (pc : pc) =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = mk_context cfg in
  let v = pc_to_expr pc ctx in
  (* let bv = BitVector.mk_sort ctx 32  in
   * let bvzero = Expr.mk_numeral_int ctx 0 bv in
   * let n = BitVector.mk_const_s ctx "n" 32 in
   * let eq = Boolean.mk_eq ctx n bvzero  in
   * let neq = Boolean.mk_not ctx eq in *)
  (* no idea what the bools mean *)
  let g = Goal.mk_goal ctx true false false in
  (match v with
   | L v -> Goal.add g [v]
   | H (v1,v2) ->
       let v2' = Boolean.mk_not ctx v2 in
      Goal.add g [v1; v2']
  );
  (* Goal.add g [neq]; *)
  Printf.printf "Goal: %s\n" (Goal.to_string g);
  let solver = Solver.mk_solver ctx None in
  List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);
  if (Solver.check solver []) != Solver.SATISFIABLE then
    Printf.printf "Not Satisfiable\n"
  else
    Printf.printf "Satisfiable\n"

