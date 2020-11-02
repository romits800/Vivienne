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

let rec update_mem size ctx mem a s =
  (match s with
   | SI32 Store (ad, v, i) ->
      let index = si_to_expr true size ctx mem ad in
      let value = si_to_expr true size ctx mem v in
      propagate_policy_three (Z3Array.mk_store ctx) a index value
   | _ -> failwith "Unexpected store - not implemented f64/32 i64"
  )


and si_to_expr is_value size ctx mem si: rel_type  = 
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
     app_to_expr is_value ts size ctx mem f
  | Load (i, memi) -> 
     let bv = BitVector.mk_sort ctx size in
     let arr1 = Z3Array.mk_const_s ctx  "mem1" bv bv in
     let arr2 = Z3Array.mk_const_s ctx  "mem2" bv bv in     
     let smem, memlen = mem in
     let tmem = Lib.List32.nth smem (Int32.of_int (memlen - memi)) in
     let stores = Smemory.get_stores tmem in
     let fmem = List.fold_left (update_mem size ctx mem) (H (arr1,arr2)) (List.rev stores) in
     let index = si_to_expr is_value size ctx mem i in
     propagate_policy (Z3Array.mk_select ctx) fmem index
     (* index *)
  | _ -> failwith "String, Int, Float, Let, Multi, Load, Store are not implemented yet."

and app_to_expr is_value ts size ctx mem f =
  match f, ts with
  | Ite, t1::t2::t3::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     let e3 = si_to_expr is_value size ctx mem t3 in
     propagate_policy_three (Boolean.mk_ite ctx) e1 e2 e3
  | Ite, _ -> failwith "Not valid ite."

  | BvSlt, t1::t2::[] ->
     (* (if is_value then print_endline "true" else print_endline "false"); *)
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     (* if is_value then 
      *   let slt = propagate_policy (BitVector.mk_slt ctx) e1 e2 in
      *   let bv = BitVector.mk_sort ctx size  in
      *   let zero = L (Expr.mk_numeral_int ctx 0 bv) in
      *   let one = L (Expr.mk_numeral_int ctx 1 bv) in
      *   propagate_policy_three (Boolean.mk_ite ctx) slt one zero
      * else *)
     propagate_policy (BitVector.mk_slt ctx) e1 e2
  | BvSlt, _ -> failwith "Not valid slt."

  | BvSle, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_sle ctx) e1 e2
  | BvSle, _ -> failwith "Not valid sle."

  | BvSgt, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_sgt ctx) e1 e2
  | BvSgt, _ -> failwith "Not valid sgt."

  | BvSge, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_sge ctx) e1 e2
  | BvSge, _ -> failwith "Not valid sge."

  | BvUlt, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_ult ctx) e1 e2
  | BvUlt, _ -> failwith "Not valid ult."

  | BvUle, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_ule ctx) e1 e2
  | BvUle, _ -> failwith "Not valid ule."

  | BvUgt, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_ugt ctx) e1 e2
  | BvUgt, _ -> failwith "Not valid ugt."

  | BvUge, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_uge ctx) e1 e2
  | BvUge, _ -> failwith "Not valid uge."

  | BvNot, t::[] ->
     let e = si_to_expr is_value size ctx mem t in
     propagate_policy_one (BitVector.mk_not ctx) e
  | BvNot, _ -> failwith "Not valid not."

  | BvNeg, t::[] ->
     let e = si_to_expr is_value size ctx mem t in
     propagate_policy_one (BitVector.mk_neg ctx) e
  | BvNeg, _ -> failwith "Not valid neg."

  | BvAnd, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_and ctx) e1 e2
  | BvAnd, _ -> failwith "Not valid bitwise and."

  | BvOr, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_or ctx) e1 e2
  | BvOr, _ -> failwith "Not valid bitwise or."

  | BvNand, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_nand ctx) e1 e2
  | BvNand, _ -> failwith "Not valid bitwise nand."

  | BvNor, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_nor ctx) e1 e2
  | BvNor, _ -> failwith "Not valid bitwise nor."

  | BvXNor, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_xnor ctx) e1 e2
  | BvXNor, _ -> failwith "Not valid bitwise xnor."

  | BvXor, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_xor ctx) e1 e2
  | BvXor, _ -> failwith "Not valid bitwise xor."
               
  | BvAdd, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_add ctx) e1 e2
  | BvAdd, ts ->
     List.iter (fun t -> print_endline (Smt_type.term_to_string t)) ts; 
     failwith "Not valid bitwise addition." 

  | BvSub, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_sub ctx) e1 e2
  | BvSub, _ -> failwith "Not valid bitwise subtraction."

  | BvMul, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_mul ctx) e1 e2
  | BvMul, _ -> failwith "Not valid bitwise multiplication."

  | BvURem, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_urem ctx) e1 e2
  | BvURem, _ -> failwith "Not valid bitwise uremainder."

  | BvSRem, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_srem ctx) e1 e2
  | BvSRem, _ -> failwith "Not valid bitwise sremainder."

  | BvSMod, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_smod ctx) e1 e2
  | BvSMod, _ -> failwith "Not valid bitwise s modulo."

  | BvShl, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_shl ctx) e1 e2
  | BvShl, _ -> failwith "Not valid bitwise sremainder."

  | BvLShr, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_lshr ctx) e1 e2
  | BvLShr, _ -> failwith "Not valid bitwise sremainder."

  | BvAShr, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (BitVector.mk_ashr ctx) e1 e2
  | BvAShr, _ -> failwith "Not valid bitwise sremainder."

  (* | BvDiv, t1::t2::[] ->
   *    let e1 = si_to_expr is_value size ctx mem t1 in
   *    let e2 = si_to_expr is_value size ctx mem t2 in
   *    propagate_policy (BitVector.mk_div ctx) e1 e2
   * | BvDiv, _ -> failwith "Not valid bitwise sremainder." *)

  | Eq, t1::t2::[] ->
     let e1 = si_to_expr is_value size ctx mem t1 in
     let e2 = si_to_expr is_value size ctx mem t2 in
     propagate_policy (Boolean.mk_eq ctx) e1 e2
  | Eq, _ -> failwith "Not valid equation."

  | Not, t::[] ->
     let e = si_to_expr is_value size ctx mem t in
     propagate_policy_one (Boolean.mk_not ctx) e
  | Not, _ -> failwith "Not valid boolean not."


  | And, ts ->
     let es = List.map (si_to_expr is_value size ctx mem) ts in
     propagate_list (Boolean.mk_and ctx) es 
  | Or, ts ->
     let es = List.map (si_to_expr is_value size ctx mem) ts in
     propagate_list (Boolean.mk_or ctx) es 
  | _ -> failwith "Not implemented yet."

and sv_to_expr is_value sv ctx mem =
    match sv with
    | SI32 si32 -> si_to_expr is_value 32 ctx mem si32
    | SI64 si64 -> si_to_expr is_value 64 ctx mem si64
    (*TODO(Romy): Not implemented*)
    | _ -> failwith "Float not implemented."


let rec pc_to_expr pc ctx mem: rel_type =
  match pc with
  | PCTrue -> L (Boolean.mk_true ctx)
  | PCFalse -> L (Boolean.mk_false ctx)
  | PCAnd (sv, pc') ->
     let ex1 = sv_to_expr false sv ctx mem in
     let ex2 = pc_to_expr pc' ctx mem in
     propagate_list (Boolean.mk_and ctx) [ex1; ex2]


let create_mem ctx size =
  let bv = BitVector.mk_sort ctx size in
  Z3Array.mk_const_s ctx  "mem" bv bv


let is_unsat (pc : pc) (sv : svalue) (mem: Smemory.t list * int) =
  (* print_endline "is_unsat";
   * Pc_type.print_pc pc |> print_endline;
   * svalue_to_string sv |> print_endline; *)

  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = mk_context cfg in

  let v = sv_to_expr false sv ctx mem in
  let pc = pc_to_expr pc ctx mem in

  let g = Goal.mk_goal ctx true false false in
  
  (match v with
  | L v ->
     (match pc with
      | L p ->  Goal.add g [p; v ]
      | H (pc1,pc2) ->  Goal.add g [pc1; v ]
     )
  | H (v1,v2) ->
     (match pc with
      | L p ->  Goal.add g [p; v1 ]
      | H (pc1,pc2) ->  Goal.add g [pc1; v1 ]
     )
  );
  (* Printf.printf "Goal: %s\n" (Goal.to_string g); *)
  let solver = Solver.mk_solver ctx None in
  List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);
  match (Solver.check solver []) with
  | Solver.UNSATISFIABLE -> true
  | _ ->
     (* let model = Solver.get_model solver in
      * (match model with
      *  | None -> print_endline "None"
      *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
      * ); *)
     false


  
let is_ct_unsat (pc : pc) (sv : svalue) (mem: Smemory.t list * int) =
  (* print_endline "is_ct_unsat";
   * Pc_type.print_pc pc |> print_endline;
   * svalue_to_string sv |> print_endline; *)

  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = mk_context cfg in

  let v = sv_to_expr false sv ctx mem in
  let pc = pc_to_expr pc ctx mem in
  let g = Goal.mk_goal ctx true false false in
  match v with
  | L v -> true
  | H (v1,v2) ->
     let bv = Expr.get_sort v1  in
     let zero = Expr.mk_numeral_int ctx 0 bv in

     let v1' = Boolean.mk_eq ctx v1 zero in
     let v2' = Boolean.mk_eq ctx v2 zero in
     let v2' = Boolean.mk_not ctx v2' in
     Goal.add g [v1'; v2'];
     (match pc with
      | L p ->  Goal.add g [p ]
      | H (pc1, pc2) ->  Goal.add g [pc1; pc2 ]
     );
     (* Printf.printf "Goal: %s\n" (Goal.to_string g); *)
     let solver = Solver.mk_solver ctx None in
     List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);
     match (Solver.check solver []) with
     | Solver.UNSATISFIABLE -> true
     | _ ->
        (* let model = Solver.get_model solver in
         * (match model with
         *  | None -> print_endline "None"
         *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
         * ); *)
        false

  
let is_v_ct_unsat (pc : pc) (sv : svalue) (mem: Smemory.t list * int) : bool =
  (* print_endline "is_v_ct_unsat";
   * Pc_type.print_pc pc |> print_endline; *)
  (* svalue_to_string sv |> print_endline; *)
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = mk_context cfg in
  
  let g = Goal.mk_goal ctx true false false in

  let v = sv_to_expr false sv ctx mem in
  match v with
   | L v -> true 
   | H (v1,v2) ->
      let v' = Boolean.mk_eq ctx v1 v2 in
      let v' = Boolean.mk_not ctx v' in
      let pcexp = pc_to_expr pc ctx mem in
      let pcexp' = 
        match pcexp with
        | L pcv -> pcv 
        | H (pcv1, pcv2) -> Boolean.mk_and ctx [pcv1; pcv2]
      in
      Goal.add g [v'];
      Goal.add g [pcexp'];
      (* Printf.printf "Goal: %s\n" (Goal.to_string g); *)
      let solver = Solver.mk_solver ctx None in
      List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);
      match (Solver.check solver []) with
      | Solver.UNSATISFIABLE -> true
      (* | Solver.UNKNOWN  -> false *)    
      | _ -> false




let is_sat (pc : pc) (mem: Smemory.t list * int) : bool =
  (* check only satisfiability *)
  (* print_endline "is_sat"; *)
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = mk_context cfg in
  (* print_endline (print_pc pc); *)
  let v = pc_to_expr pc ctx mem in
  let g = Goal.mk_goal ctx true false false in
  (match v with
   | L v -> Goal.add g [v]
   | H (v1,v2) -> Goal.add g [v1;v2]
  );
  (* Printf.printf "Goal: %s\n" (Goal.to_string g); *)
  let solver = Solver.mk_solver ctx None in
  List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);
  let check_solver = Solver.check solver [] in
  match check_solver with
  | Solver.SATISFIABLE
    | Solver.UNKNOWN  -> true  
  | _ -> false


(* let max = Optimize.maximize
 * let min = Optimize.minimize
 * 
 * 
 * let optimize (f : Z3.Optimize.optimize -> Z3.Expr.expr -> Z3.Optimize.handle)
 *       (pc : pc) (mem: Smemory.t list * int) (sv : svalue)  =
 *   print_endline "optimize";
 *   svalue_to_string sv |> print_endline;
 *   let cfg = [("model", "true"); ("proof", "false")] in
 *   let ctx = mk_context cfg in
 *   let g1 = Goal.mk_goal ctx true false false in
 * 
 *   let opt1 = Optimize.mk_opt ctx in
 * 
 *   let pcexp = pc_to_expr pc ctx mem in
 *   (\* TODO(Romy): Fix for two paths *\)
 *   (match pcexp with
 *    | L pcv -> Goal.add g1 [pcv] 
 *    | H (pcv1, pcv2) -> Goal.add g1 [pcv1]
 *                        (\* Goal.add g2 [pcv2] *\) 
 *   );
 * 
 *   List.iter (fun f -> Optimize.add opt1 [f]) (Goal.get_formulas g1);
 * 
 *   let v = sv_to_expr false sv ctx mem in
 *   (\* TODO(Romy): Fix for two paths *\)
 *   let h =
 *     (match v with
 *      | L v ->
 *         let bv = Expr.get_sort v  in
 *         (\* half max int *\)
 *         let hmi = Expr.mk_numeral_int ctx 0x80000000 bv in
 *         let v' =
 *           match Sort.get_sort_kind bv with
 *           | Z3enums.BV_SORT ->  BitVector.mk_add ctx v hmi
 *           | _ -> failwith ("Wrong type of sort " ^ (Sort.to_string bv))
 *         in
 *         f opt1 v'
 *      | H (v1,v2) ->
 *         let bv = Expr.get_sort v1  in
 *         (\* half max int *\)
 *         let hmi = Expr.mk_numeral_int ctx 0x80000000 bv in
 *         let v' =
 *           match Sort.get_sort_kind bv with
 *           | Z3enums.BV_SORT ->  BitVector.mk_add ctx v1 hmi
 *           | _ -> failwith ("Wrong type of sort " ^ (Sort.to_string bv))
 *         in
 *         f opt1 v'
 *     ) in
 * 
 *   (\* List.iter (fun f -> Optimize.add opt2 [f]) (Goal.get_formulas g2); *\)
 *   match (Optimize.check opt1) with
 *    | Solver.SATISFIABLE ->
 *       let ex1 = Optimize.get_lower h in
 *       let ex2 = Optimize.get_upper h in
 *       if Expr.equal ex1 ex2 then
 *         let i = Arithmetic.Integer.get_big_int ex1 in
 *         let bi = Big_int.sub_big_int i (Big_int.big_int_of_int64 2147483648L) in
 *         let i = Big_int.int_of_big_int bi in
 *         print_endline "max/min sat";
 *         Printf.printf "Optimize: %s\n" (Optimize.to_string opt1);
 *         string_of_int i |> print_endline;
 *         Some (i)
 *       else None
 *    | _ ->  None *)
