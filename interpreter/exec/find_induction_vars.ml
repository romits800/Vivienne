open Eval
open Svalues
open Types
open Instance
open Ast
open Source


            
(* let is_basic_induction_var k v =
 *   let open Smt_type in
 *   match v with
 *     (v', SI32 (BitVec(1L,_)), SI32 (BitVec(1L,_))) -> true
 *   | (v', SI64 (BitVec(1L,_)), SI64 (BitVec(1L,_))) -> true
 *   | _ -> false
 *             
 * let extract_induction_variable ivs =
 *   let iv = IndVarMap.filter is_basic_induction_var ivs in
 *   IndVarMap.choose iv *)

let lowbound_ind_var v c =
  let open Pc_type in
  let pclet, pc = c.pc in
  let pc' = PCAnd (SI32 (Si32.ge_u v Si32.zero), pc) in
  { c with pc = pclet,pc' }
                  

            
let create_induction_variable c =
  let v' = Si32.of_low() in
  let c' = lowbound_ind_var v' c in
  (SI32 v', SI32 v', SI32 Si32.one, SI32 Si32.one), c'
  
(* TODO(Romy): add the same patterns for SI64 *)
let get_iv_triple vold_orig vold vnew ivs =
  (* print_endline "compare_values";
   * svalue_to_string vold |> print_endline;
   * svalue_to_string vnew |> print_endline; *)
  let open Smt_type in
  let v = 
    match vold, vnew with
    | SI32 v1, SI32 (App (BvAdd,
                          [(App
                              (BvMul, [v2;BitVec(_) as v2']));
                           BitVec(_) as v3]))
      | SI32 v1, SI32 (App (BvAdd,
                            [(App
                                (BvMul, [BitVec(_) as v2'; v2]));
                             BitVec(_) as v3]))
      | SI32 v1, SI32 (App (BvAdd,
                            [BitVec(_) as v3;
                             App
                               (BvMul, [v2;BitVec(_) as v2'])] ))
      | SI32 v1, SI32 (App (BvAdd,
                            [BitVec(_) as v3;
                             App
                               (BvMul, [BitVec(_) as v2';v2])] )) ->

       if (v1 = v2) then
         let tr = (vold_orig, vold, SI32 v2', SI32 v3) in
         IndVarMap.add vold tr ivs
       else 
         (try
            let _ = IndVarMap.find (SI32 v2) ivs in
            let tr = (vold_orig, SI32 v2, SI32 v2', SI32 v3) in
            IndVarMap.add vold tr ivs
          with Not_found ->
            ivs
         )
    | SI32 v1, SI32 (App (BvSub,
                          [(App
                              (BvMul, [v2;BitVec(_) as v2']));
                           BitVec(_) as v3]))
      | SI32 v1, SI32 (App (BvSub,
                            [(App
                                (BvMul, [BitVec(_) as v2'; v2]));
                             BitVec(_) as v3]))
      | SI32 v1, SI32 (App (BvSub,
                            [BitVec(_) as v3;
                             App
                               (BvMul, [v2;BitVec(_) as v2'])] ))
      | SI32 v1, SI32 (App (BvSub,
                            [BitVec(_) as v3;
                             App
                               (BvMul, [BitVec(_) as v2';v2])] )) ->

       let v3 = Si32.sub Si32.zero v3 in
       if (v1 = v2) then
         let tr = (vold_orig, vold, SI32 v2', SI32 v3) in
         IndVarMap.add vold tr ivs
       else 
         (try
            let _ = IndVarMap.find (SI32 v2) ivs in
            let tr = (vold_orig, SI32 v2, SI32 v2', SI32 v3) in
            IndVarMap.add vold tr ivs
          with Not_found ->
            ivs
         )
      
    | SI32 v1, SI32 (App (BvAdd, [v2;BitVec(_) as v3]))
      | SI32 v1, SI32 (App (BvAdd, [BitVec(_) as v3;v2])) ->

       if (v1 = v2) then
         let tr = (vold_orig, vold, SI32 (Si32.one), SI32 v3) in
         IndVarMap.add vold tr ivs
       else 
         (try
            let _ = IndVarMap.find (SI32 v2) ivs in
            let tr = (vold_orig, SI32 v2, SI32 (Si32.one), SI32 v3) in
            IndVarMap.add vold tr ivs
          with Not_found ->
            ivs
         )
    | SI32 v1, SI32 (App (BvSub, [v2;BitVec(_) as v3]))
      | SI32 v1, SI32 (App (BvSub, [BitVec(_) as v3;v2])) ->

       let v3 = Si32.sub Si32.zero v3 in
       if (v1 = v2) then
         let tr = (vold_orig, vold, SI32 (Si32.one), SI32 v3) in
         IndVarMap.add vold tr ivs
       else 
         (try
            let _ = IndVarMap.find (SI32 v2) ivs in
            let tr = (vold_orig, SI32 v2, SI32 (Si32.one), SI32 v3) in
            IndVarMap.add vold tr ivs
          with Not_found ->
            ivs
         )

    | SI32 v1, SI32 (App (BvMul, [v2;BitVec(_) as v3]))
      | SI32 v1, SI32 (App (BvMul, [BitVec(_) as v3;v2])) ->
       if (v2 = v2) then
         let tr = (vold_orig, vold, SI32 v3, SI32 (Si32.zero)) in
         IndVarMap.add vold tr ivs
       else 
         (try
            let _ = IndVarMap.find (SI32 v2) ivs in
            let tr = (vold_orig, SI32 v2, SI32 v3, SI32 (Si32.zero)) in
            IndVarMap.add vold tr ivs
          with Not_found ->
            ivs
         )
    | _ -> IndVarMap.remove vold ivs
  in
  v


let rec find_induction_vars (lv : triple IndVarMap.t) (c : config) (c_orig : config) :
          (triple IndVarMap.t) * config list =
  (* print_endline "find_induction_vars"; *)
  let {frame; code = vs, es; pc = pclet, pc; _} = c in
  (* let s1 = Svalues.string_of_values (List.rev vs) in *)
  (* print_endline s1; *)
  match es with
  | e::est -> 
     (match e.it, vs with
      | Plain e', vs ->
         (* let no = Arrange.instr (e'@@e.at) in
          * (match no with | Sexpr.Node(h,inner) -> print_endline h
          *                | _ -> print_endline "no node"); *)
         (match e', vs with
          | Unreachable, vs ->
             let vs', es' = vs, [Trapping "unreachable executed" @@ e.at] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
          | Nop, vs ->
             (* print_endline "nop"; *)
             let vs', es' = vs, [] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
          | Block (bt, es'), vs ->
             (* print_endline "block"; *)
             let FuncType (ts1, ts2) = block_type frame.inst bt in
             let n1 = Lib.List32.length ts1 in
             let n2 = Lib.List32.length ts2 in
             let args, vs' = take n1 vs e.at, drop n1 vs e.at in
             let vs', es' = vs', [Label (n2, [], (args, List.map plain es'),
                                         (pclet,pc),
                                         c.induction_vars,
                                         c.ct_check) @@ e.at] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
          | Loop (bt, es'), vs ->
             (* print_endline "Loop find_induction_vars"; *)
             let FuncType (ts1, ts2) = block_type frame.inst bt in
             let n1 = Lib.List32.length ts1 in
             let args, vs' = take n1 vs e.at, drop n1 vs e.at in
             let vs', es' = vs', [Label (n1, [],
                                         (args, List.map plain es'),
                                         (pclet,pc),
                                         c.induction_vars,
                                         c.ct_check) @@ e.at] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
          | If (bt, es1, es2), v :: vs' ->
             (* print_endline "if"; *)
             let pc', pc'' = split_condition v pc in
             let vs'', es'' = vs', [Plain (Block (bt, es1)) @@ e.at] in (* True *)
             let vs', es' = vs', [Plain (Block (bt, es2)) @@ e.at] in (* False *)
             (* Don't check sat *)
             
             let lv1,c1 = find_induction_vars lv
                            {c with code = vs', es' @ est; pc = (pclet,pc')} c_orig in
             let lv2,c2 = find_induction_vars lv1
                            {c with code = vs'', es'' @ est; pc = (pclet,pc'')} c_orig in
             lv2,c1 @ c2

          | Br x, vs ->
             (* print_endline "br"; *)
             let vs', es' = [], [Breaking (x.it, vs) @@ e.at] in
             lv, [{c with code = vs', es' @ List.tl es}]
             
          | BrIf x, v :: vs' ->
             (* print_endline "br_if"; *)
             let pc', pc'' = split_condition v pc in
             let vs'', es'' = vs', [Plain (Br x) @@ e.at] in
             let vs', es' = vs', [] in
             
             let lv1, c1 = find_induction_vars lv
                             {c with code = vs', es' @ est; pc = (pclet,pc')} c_orig in
             find_induction_vars lv1 {c with code = vs'', es'' @ est; pc = (pclet,pc'')} c_orig

             
          (* | BrTable (xs, x), I32 i :: vs' when I32.ge_u i (Lib.List32.length xs) ->
           *   vs', [Plain (Br x) @@ e.at]
           * 
           * | BrTable (xs, x), I32 i :: vs' ->
           *   vs', [Plain (Br (Lib.List32.nth xs i)) @@ e.at] *)

          | Return, vs ->
             (* print_endline "return"; *)
             let vs', es' = [], [Returning vs @@ e.at] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          | Call x, vs ->
             (* print_endline "call"; *)
             let vs', es' = vs, [Invoke (func frame.inst x) @@ e.at] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          (* | CallIndirect x, I32 i :: vs ->
           *   let func = func_elem frame.inst (0l @@ e.at) i e.at in
           *   if type_ frame.inst x <> Func.type_of func then
           *     vs, [Trapping "indirect call type mismatch" @@ e.at]
           *   else
           *     vs, [Invoke func @@ e.at] *)

          | Drop, v :: vs' ->
             (* print_endline "drop"; *)
             let vs', es' = vs', [] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
             
          | Select, v0 :: v2 :: v1 :: vs' ->
             (* print_endline "select"; *)
             let vselect = select_condition v0 v1 v2 in
             (* let pc' = PCAnd(cond, pc) in *)
             let vs', es' = vselect :: vs', [] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
             
          | LocalGet x, vs ->
             (* print_endline "local get"; *)
             let vs', es' = (local frame x) :: vs, [] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          | LocalSet x, v :: vs' ->
             (* print_endline "local set"; *)
             let vv = local frame x in
             let vv_orig = local c_orig.frame x in

             let lv' = get_iv_triple vv_orig vv v lv in
             let frame' = update_local c.frame x v in
             let vs', es' = vs', [] in
             find_induction_vars lv' {c with code = vs', es' @ List.tl es; frame = frame'} c_orig

          | LocalTee x, v :: vs' ->
             (* print_endline "local tee"; *)
             let vv = local frame x in
             let vv_orig = local c_orig.frame x in
             
             let lv' = get_iv_triple vv_orig vv v lv in

             (* print_loopvar (LocalVar (x,is_low)); *)
             let frame' = update_local c.frame x v in
             let vs', es' = v :: vs', [] in
             find_induction_vars lv' {c with code = vs', es' @ List.tl es; frame = frame'} c_orig

          | GlobalGet x, vs ->
             let vs', es' = Sglobal.load (sglobal frame.inst x) :: vs, [] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          | GlobalSet x, v :: vs' ->

             let vv = Sglobal.load (sglobal c.frame.inst x) in
             let vv_orig = Sglobal.load (sglobal c_orig.frame.inst x) in
             
             let lv' = get_iv_triple vv_orig vv v lv in
             let newg, vs', es' =
               (try Sglobal.store (sglobal frame.inst x) v, vs', []
                with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                   | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
             in
             let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
             find_induction_vars lv' {c with code = vs', es' @ List.tl es; frame = frame'} c_orig

          | Load {offset; ty; sz; _}, si :: vs' ->
             (* print_endline "load"; *)
             let addr =
               (match si with
                | SI32 v -> v
                | _ -> failwith "Error: Address should be 32-bit integer"
               ) in (* I64_convert.extend_i32_u i in *)
             let offset = Int32.to_int offset in        
             let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in
             let nv =
               (match sz with
                | None -> Eval_symbolic.eval_load ty final_addr
                            (smemlen frame.inst) (Types.size ty) None
                | Some (sz, ext) ->
                   assert (packed_size sz <= Types.size ty);
                   let n = packed_size sz in 
                   Eval_symbolic.eval_load ty final_addr
                     (smemlen frame.inst) n (Some ext)
               )
             in

             let vs', es' =  nv :: vs', [] in 

             find_induction_vars lv {c with code = vs', est}  c_orig
             
          | Store {offset; ty; sz; _}, sv :: si :: vs' ->
             (* print_endline "store"; *)
             let mem = smemory frame.inst (0l @@ e.at) in
             let frame = {frame with
                           inst = update_smemory frame.inst mem (0l @@ e.at)} in
             let addr =
               (match si with
                | SI32 v -> v
                | _ -> failwith "Error: Address should be 32-bit integer"
               ) in (* I64_convert.extend_i32_u i in *)
             let offset = Int32.to_int offset in
             (* check if we satisfy CT  for the index *)

             (* if (Z3_solver.is_v_ct_unsat (pclet, pc) si mems) then *)
             let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in

             (* let lv = (StoreVar final_addr)::lv in *)
             let nv, lvn, lvn_orig =
               (match sz with
                | None ->
                   let nv = Eval_symbolic.eval_store ty final_addr sv
                              (smemlen frame.inst) (Types.size ty) in
                   let lvn = (Eval_symbolic.eval_load ty final_addr
                                (smemlen frame.inst) (Types.size ty) None) in
                   let lvn_orig = (Eval_symbolic.eval_load ty final_addr
                                     (smemlen c_orig.frame.inst) (Types.size ty) None) in

                   nv,lvn,lvn_orig
                | Some (sz) ->
                   assert (packed_size sz <= Types.size ty);
                   let n = packed_size sz in
                   let nv = Eval_symbolic.eval_store ty final_addr sv
                              (smemlen frame.inst) n in
                   let lvn = Eval_symbolic.eval_load ty final_addr
                               (smemlen frame.inst) n None in
                   let lvn_orig = Eval_symbolic.eval_load ty final_addr
                               (smemlen c_orig.frame.inst) n None in
                   nv, lvn, lvn_orig)
             in
             let lv' = get_iv_triple lvn_orig lvn sv lv in
             
             (* let memtuple = (c.frame.inst.smemories, smemlen c.frame.inst) in
              * let is_low = Z3_solver.is_v_ct_unsat c.pc lvn memtuple in
              * let mo = compare_svalues lvn sv in
              * 
              * let lv = (StoreVar (final_addr, ty, sz, is_low, mo))::lv in *)

             let mem' = Smemory.store_sind_value mem nv in
             let vs', es' = vs', [] in
             (* Update memory with a store *)
             let nframe = {frame with inst = insert_smemory frame.inst mem'} in

             find_induction_vars lv' {c with code = vs', es' @ est;
                                               frame = nframe}  c_orig

          (*TODO(Romy): Implement Const*)
          | Const v, vs ->
             (* print_endline "const"; *)
             let va = 
               match v.it with
               | Values.I32 i ->
                  let ii = Int32.to_int i in
                  let ii' = Int64.of_int ii in
                  SI32 (Si32.bv_of_int ii' 32)
               | Values.I64 i ->
                  SI64 (Si64.bv_of_int i 64)
               | Values.F32 i -> SF32 i
               | Values.F64 i -> SF64 i
             in
             let vs', es' = va :: vs, [] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es}  c_orig
             
          (* | Const v, vs ->
           *    v.it :: vs, [] *)

          | Test testop, v :: vs' ->
             (* print_endline "testop"; *)
             let vs', es' =
               (try (Eval_symbolic.eval_testop testop v) :: vs', []
                with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
             
          | Compare relop, v2 :: v1 :: vs' ->
             (* print_endline "relop"; *)
             let vs', es' =
               (try (Eval_symbolic.eval_relop relop v1 v2) :: vs', []
                with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          | Unary unop, v :: vs' ->
             (* print_endline "unop"; *)
             let vs', es' = 
               (try Eval_symbolic.eval_unop unop v :: vs', []
                with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          | Binary binop, v2 :: v1 :: vs' ->
             (* print_endline "binop"; *)
             let vs', es' = 
               (try
                  let nv = Eval_symbolic.eval_binop binop v1 v2 in
                  (* "Printing binop" |> print_endline; *)
                  (* Pc_type.svalue_to_string nv |> print_endline; *)
                  nv :: vs', []
                with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig
          | Convert cvtop, v :: vs' ->
             let vs', es' = 
               (try Eval_symbolic.eval_cvtop cvtop v :: vs', []
                with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
             in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          | _ ->
             let s1 = Svalues.string_of_values (List.rev vs) in
             let s2 = Types.string_of_svalue_types (List.map Svalues.type_of (List.rev vs)) in
             let no = Arrange.instr (e' @@ e.at) in
             (match no with | Sexpr.Node(h,inner) -> print_endline h
                            | _ -> print_endline "no node");

             Crash.error e.at
               ("missing or ill-typed operand on stack (" ^ s1 ^ " : " ^ s2 ^ ")")
         )

      | Trapping msg, vs ->
         assert false

      | Assert (_,_), vs ->
         failwith "Unexpected Assert in find_induction_vars";
         
      | Havoc lvs, vs ->
         failwith "Unexpected Havoc in find_induction_vars";

      | SecondPass _, vs ->
         failwith "Unexpected SecondPass in find_induction_vars";

      | FirstPass _, vs ->
         failwith "Unexpected FirstPass in find_induction_vars";

      (* assert false *)

      | Returning vs', vs ->
         Crash.error e.at "undefined frame"

      | Breaking (k, vs'), vs ->
         (* print_endline "breaking"; *)
         lv, []
      (* Crash.error e.at "undefined label" *)

      | Label (n, es0, (vs', []), pc', iv', cct'), vs ->
         (* print_endline "lab"; *)
         let vs', es' = vs' @ vs, [] in
         find_induction_vars lv {c with code = vs', es' @ List.tl es}  c_orig
         
      | Label (n, es0, (vs', {it = Trapping msg; at} :: es'), pc', iv', cct'), vs ->
         (* print_endline "lab2"; *)
         let vs', es' = vs, [Trapping msg @@ at] in
         find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

      | Label (n, es0, (vs', {it = Returning vs0; at} :: es'), pc', iv', cct'), vs ->
         (* print_endline "lab3"; *)
         let vs', es' = vs, [Returning vs0 @@ at] in
         find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

      | Label (n, es0, (vs', {it = Breaking (0l, vs0); at} :: es'), pc', iv', cct'), vs ->
         (* print_endline "lab4"; *)
         let vs', es' = take n vs0 e.at @ vs, List.map plain es0 in
         find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

      | Label (n, es0, (vs', {it = Breaking (k, vs0); at} :: es'), pc', iv', cct'), vs ->
         (* print_endline "lab5"; *)
         let vs', es' = vs, [Breaking (Int32.sub k 1l, vs0) @@ at] in
         find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

      | Label (n, es0, code', pc', iv', cct'), vs ->
         (* print_endline "lab6"; *)
         (* TODO(Romy): not sure if correct to change the pc *)
         let lv', c' = find_induction_vars lv {c with code = code'; pc = pc'; induction_vars = iv'}  c_orig in
         (* print_endline "lab6_back"; *)
         let res =
           List.fold_left (fun (lvi, cprev) ci ->
               let lvi', ci' =
                 find_induction_vars lvi
                   {c with code = vs,
                                  [Label (n, es0, ci.code,
                                          ci.pc,
                                          ci.induction_vars,
                                          ci.ct_check) @@ e.at]
                                  @ List.tl es;
                           pc = ci.pc; 
                           frame = ci.frame;
                           induction_vars = ci.induction_vars} c_orig
               in
               lvi', ci' @ cprev
             ) (lv', []) c'
         in
         (* print_endline "lab6_end"; *)
         res

      | Frame (n, frame', (vs', []), pc', iv'), vs ->
         (* print_endline ("frame1:" ^ (string_of_int c.counter)); *)
         let vs', es' = vs' @ vs, [] in
         let c = {c with code = vs', es' @ List.tl es;
                         frame = {frame
                                 with inst = {frame.inst
                                             with smemories = frame'.inst.smemories;
                                                  smemlen = frame'.inst.smemlen;
                                                  sglobals = frame'.inst.sglobals
                                             }
                                 };
                         pc = pc';
                         induction_vars = iv'
                 } in
         find_induction_vars lv c c_orig
      | Frame (n, frame', (vs', {it = Trapping msg; at} :: es'), _, _), vs ->
         (* print_endline "frame2"; *)
         let vs', es' = vs, [Trapping msg @@ at] in
         find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

      | Frame (n, frame', (vs', {it = Returning vs0; at} :: es'), pc', iv'), vs ->
         (* print_endline "frame returning"; *)
         (* print_endline ("frame3:" ^ (string_of_int c.counter)); *)
         let vs', es' = take n vs0 e.at @ vs, [] in
         let c = {c with code = vs', es' @ List.tl es;
                         frame = {frame
                                 with inst = {frame.inst
                                             with smemories = frame'.inst.smemories;
                                                  smemlen = frame'.inst.smemlen;
                                                  sglobals = frame'.inst.sglobals
                                             }
                                 };
                         pc = pc';
                         induction_vars = iv'} in
         find_induction_vars lv c c_orig

      | Frame (n, frame', code', pc', iv'), vs ->
         (* print_endline "frame4"; *)
         let lv', c' = find_induction_vars lv {c with frame = frame';
                                                      code = code';
                                                      budget = c.budget - 1;
                                                      pc = pc';
                                                      induction_vars = iv'} c_orig in
         (* print_endline "frame4_end"; *)
         (* TODO(Romy): the pc etc  should probably not be here *)
         
         List.fold_left
           (fun (lvi,cprev) ci ->
             let lvi', ci' =
               find_induction_vars lvi {c with code = vs, [Frame (n, ci.frame, ci.code,
                                                                  ci.pc, ci.induction_vars)
                                                           @@ e.at] @ List.tl es;} c_orig
             in
             lvi', ci' @ cprev) (lv',[]) c'
         

      | Invoke func, vs when c.budget = 0 ->
         Exhaustion.error e.at "call stack exhausted"

      | Invoke func, vs ->
         (* print_endline "inv2"; *)
         let FuncType (ins, out) = func_type_of func in
         let n1, n2 = Lib.List32.length ins, Lib.List32.length out in
         let args, vs' = take n1 vs e.at, drop n1 vs e.at in
         (match func with
          | Func.AstFunc (t, inst', f) ->
             let rest = List.map value_to_svalue_type f.it.locals in
             (* let locals' = List.rev args @ List.map Svalues.default_value rest in *) 
             let locals' = List.rev args @ List.map Svalues.default_value rest in
             let frame' = {inst = !inst'; locals = locals'} in
             let instr' = [Label (n2, [], ([], List.map plain f.it.body),
                                  c.pc, c.induction_vars, c.ct_check) @@ f.at] in 
             let vs', es' = vs', [Frame (n2, frame', ([], instr'), c.pc, c.induction_vars) @@ e.at] in
             find_induction_vars lv {c with code = vs', es' @ List.tl es} c_orig

          (* | Func.HostFunc (t, f) ->
           *   (try List.rev (f (List.rev args)) @ vs', []
           *   with Crash (_, msg) -> Crash.error e.at msg) *)
          | _ -> Crash.error e.at "Func.Hostfunc not implemented yet."
         )
     )
  | [] -> lv, []

(*vold, mul, add*)
let rec replace_induction_vars (iv : triple) (ivs : triple IndVarMap.t):
          triple IndVarMap.t =
  let _,ivvar, _, _ = iv in
  let ivk =
    match ivvar with
    | SI32 ivk -> (Si32.add ivk (Si32.one))
    | _ -> failwith "Not supported"
  in
  let ivs' =
    IndVarMap.mapi (fun k (vorig, v, b1, b2) ->
        if (k = SI32 ivk || k = SI64 ivk) then
          (vorig, v, b1, b2)
        else if (k = v) then
          (match v with
           | SI32 v' ->
              let ivk' = SI32 ivk in
              (* let newb2 = SI32 () *)
              (vorig, ivk', b2, vorig)
           | SI64 v' ->
              let ivk' = SI64 (Si32.extend_s 64 ivk) in
              (vorig, ivk', b2, vorig)
           | _ -> failwith "Floating point not supported"
          )
        else
          (try
             let vorig, v',b1',b2' = IndVarMap.find v ivs in
             if (v' = SI32 ivk || v' = SI64 ivk) then 
               (match v', b1', b2', b1, b2 with
                | SI32 v', SI32 b1', SI32 b2', SI32 b1, SI32 b2 ->
                   let ivk' = SI32 ivk in
                   let newb1 = SI32 (Si32.mul b1' b1) in
                   let newb2 = SI32 (Si32.add (Si32.mul b2 b1') b2') in
                   (* let newb2 = SI32 () *)
                   (vorig, ivk', newb1, newb2)
                (* TODO(Romy): check that it works when reporting*)
                | SI64 v', SI64 b1', SI64 b2', SI64 b1, SI64 b2 ->
                   let ivk' = SI64 (Si32.extend_s 64 ivk) in
                   let newb1 = SI64 (Si64.mul b1' b1) in
                   let newb2 = SI64 (Si64.add (Si64.mul b2 b1') b2') in
                   (vorig, ivk', newb1, newb2)
                | _ -> failwith "Floating point not supported"
               )

             else
               (vorig, v, b1, b2)
           with Not_found ->
             (vorig, v, b1, b2)
          )
          
        ) ivs
  in
  if IndVarMap.equal (fun a b -> a = b) ivs ivs' then
    ivs'
  else
    replace_induction_vars iv ivs'

  (* ivs *)

(* TODO(Romy)*)
(* let eliminate_vars (c : config) (lv : loopvar_t list)
 *       (ivs : triple IndVarMap.t): config =
 *   match lv with
 *   | LocalVar (x, is_low, mo) :: lvs ->
 *      let v = local c.frame x in
 *      (try (
 *         let (v', b1, b2) = IndVarMap.find v ivs in
 *         if (v' = v) then c
 *         else c
 *       ) with Not_found ->
 *         c
 *      )
 *   | _ -> c *) 

let triple_to_string v =
  let orig, old, b1, b2 = v in
  "(" ^ Pc_type.svalue_to_string orig ^ ", " ^
    Pc_type.svalue_to_string old ^ ", " ^
      Pc_type.svalue_to_string b1 ^ ", " ^
        Pc_type.svalue_to_string b2 ^ ", " ^ ")"

  
let induction_vars_to_string ivs : string =
  let iv_to_string ivs =
    IndVarMap.fold (fun k v str -> Pc_type.svalue_to_string k ^
                                     ":" ^ triple_to_string v ^ ";" ^ str) ivs ""
  in
  match ivs with
  | None -> "_"
  | Some ivs -> iv_to_string ivs

let induction_vars (c : config) (c_orig : config) (lv : loopvar_t list) :
      triple *  config =
  (*(triple IndVarMap.t) = *) 
  let ivs,_ = find_induction_vars IndVarMap.empty c c_orig in  
  let iv,c' = create_induction_variable c in
  let ivs' = replace_induction_vars iv ivs in
  let c' = { c' with  induction_vars = Some ivs' } in
  (iv, c')
  (* eliminate_vars c lv ivs' *)

