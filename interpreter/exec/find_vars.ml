open Eval
open Svalues
open Types
open Instance
open Ast
open Source

let compare_svalues vold vnew = Nothing
  (* print_endline "compare_values";
   * svalue_to_string vold |> print_endline;
   * svalue_to_string vnew |> print_endline; *)
  (* let v = 
   *   match vold, vnew with
   *   | SI32 v1, SI32 (Smt_type.App (Smt_type.BvAdd, [v2;v3]))
   *        when v1 = v2 || v1 = v3 -> Increase vold
   *   | SI32 (Smt_type.BitVec(i1,nd1)), SI32 (Smt_type.BitVec(i2,nd2))
   *        when i1 < i2 -> Increasge vold
   *   | SI32 v1, SI32 (Smt_type.App (Smt_type.BvSub, [v2;v3]))
   *        when v1 = v2 -> Decrease vold
   *   | SI32 (Smt_type.BitVec(i1,nd1)), SI32 (Smt_type.BitVec(i2,nd2))
   *        when i1 > i2 -> Decrease vold
   *   | SI64 v1, SI64 (Smt_type.App (Smt_type.BvAdd, [v2;v3]))
   *        when v1 = v2 || v1 = v3 -> Increase vold
   *   | SI64 (Smt_type.BitVec(i1,nd1)), SI64 (Smt_type.BitVec(i2,nd2))
   *        when i1 < i2 -> Increase vold
   *   | SI64 v1, SI64 (Smt_type.App (Smt_type.BvSub, [v2;v3]))
   *        when v1 = v2 -> Decrease vold
   *   | SI64 (Smt_type.BitVec(i1,nd1)), SI64 (Smt_type.BitVec(i2,nd2))
   *        when i1 > i2 -> Decrease vold                 
   *   | _ ->  Nothing
   * in *)
  (* modifier_to_string v |> print_endline; *)
  (* v *)

let collect_local = ref true

                  
let rec fv_step (analyzed_loop : int ) (lv : loopvar_t list)
          (c : config) : loopvar_t list * config list =
    let {frame; code = vs, es; pc = pcnum, pclet, pc; _} = c in

    let e = List.hd es in
    let est = List.tl es in
    (* if !Flags.debug then (
     *   print_endline "Finding modified variables..";
     *   print_endline (string_of_int analyzed_loop)); *)

    (* let s1 = Svalues.string_of_values (List.rev vs) in *)
    (* print_endline s1; *)
   (match e.it, vs with
    | Plain e', vs ->
       (* let no = Arrange.instr (e'@@e.at) in
        * (match no with | Sexpr.Node(h,inner) -> print_endline h
        *                | _ -> print_endline "no node"); *)
       (match e', vs with
        | Unreachable, vs ->
           let vs', es' = vs, [Trapping "unreachable executed" @@ e.at] in
           lv, [{c with code = vs', es' @ List.tl es}]
        | Nop, vs ->
           (* print_endline "nop"; *)
           let vs', es' = vs, [] in
           lv, [{c with code = vs', es' @ List.tl es}]
        | Block (bt, es'), vs ->
           (* print_endline "block"; *)
           if (!Flags.debug) then (
             print_endline "block fv";
             print_endline (string_of_region e.at));


           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let n2 = Lib.List32.length ts2 in
           let args, vs' = take n1 vs e.at, drop n1 vs e.at in
           let vs', es' = vs', [Label (n2, [], (args, List.map plain es'),
                                       (pcnum, pclet,pc), c.induction_vars, c.ct_check) @@ e.at] in
           lv, [{c with code = vs', es' @ List.tl es}]
        | Loop (bt, es'), vs ->
           (* print_endline "Loop find_vars"; *)
           if !Flags.debug then 
             print_endline ("Loop fv: " ^ (string_of_int (Obj.magic e') )
                                        ^ ": anloop: " ^ (string_of_int (analyzed_loop))   
                                        ^  " loc: " ^ (string_of_region e.at));

           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let args, vs' = take n1 vs e.at, drop n1 vs e.at in
           if (analyzed_loop != Obj.magic e') then (
             if !Flags.debug then 
                  print_endline "Find_modified_vars: Found other loop.";
             (* TODO(Romy): fix for return not 0 args to the value stack *)
             let vs', es' = vs', [Label (n1, [],
                                         (args, List.map plain es'),
                                         (pcnum, pclet,pc), c.induction_vars,
                                         c.ct_check) @@ e.at] in
             (* find_vars lv {c with code = vs, List.tl es} *)
             lv, [{c with code = vs', es' @ List.tl es}]
           )
           else (                 

             let vs', es' = vs', [Label (n1, [],
                                         (args, List.map plain es'),
                                         (pcnum, pclet,pc), c.induction_vars,
                                         c.ct_check) @@ e.at] in
             lv, [{c with code = vs', es' @ List.tl es}]
           )
        | If (bt, es1, es2), v :: vs' ->
           (* print_endline "if"; *)
           if (!Flags.debug) then (
             print_endline "if fv";
             print_endline (string_of_region e.at));

           let pc', pc'' = split_condition v (pcnum, pclet, pc) in
           let vs'', es'' = vs', [Plain (Block (bt, es1)) @@ e.at] in (* True *)
           let vs', es' = vs', [Plain (Block (bt, es2)) @@ e.at] in (* False *)
           (* Don't check sat *)

           let mem = get_mem_tripple frame in 
           
           let c1 =
             let pcnum' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum', pclet, pc') mem then (
               [{c with code = vs', es' @ est; pc = (pcnum', pclet,pc')}])
             else []
           in
           let c2 =
             let pcnum'' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum'', pclet, pc'') mem then (
               [{c with code = vs'', es'' @ est; pc = (pcnum'', pclet,pc'')}])
             else []
           in
           lv, c1 @ c2

        | Br x, vs ->
           (* print_endline "br"; *)
           if (!Flags.debug) then (
             print_endline "Br";
             print_endline (string_of_region e.at));


           let vs', es' = [], [Breaking (x.it, vs) @@ e.at] in
           lv, [{c with code = vs', es' @ List.tl es}]
           
        | BrIf x, v :: vs' ->
           (* print_endline "br_if"; *)
           if (!Flags.debug) then (
             print_endline "brif fv";
             (* print_endline (Pc_type.svalue_to_string v); *)
             print_endline (string_of_region e.at));

           let pc', pc'' = split_condition v (pcnum, pclet, pc) in (* false, true *)
           let vs'', es'' = vs', [Plain (Br x) @@ e.at] in
           let vs', es' = vs', [Plain Nop @@ e.at] in

           let mem = get_mem_tripple frame in 
           
           let c1 =
             let pcnum'' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum'', pclet, pc'') mem then (
               [{c with code = vs'', es'' @ est; pc = (pcnum'', pclet, pc'')}]
             ) else [] 
           in
           let c2 =
             let pcnum' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum', pclet, pc') mem then (
               [{c with code = vs', es' @ est; pc = (pcnum', pclet, pc')}]
              ) else []
           in
           if (!Flags.debug) then (
             print_endline "br_if";
             print_endline (string_of_int (List.length (c1 @ c2)))
           );

           lv, c1 @ c2
           
        (* | BrTable (xs, x), I32 i :: vs' when I32.ge_u i (Lib.List32.length xs) ->
         *   vs', [Plain (Br x) @@ e.at]
         * 
         * | BrTable (xs, x), I32 i :: vs' ->
         *   vs', [Plain (Br (Lib.List32.nth xs i)) @@ e.at] *)

        | Return, vs ->
           (* print_endline "return"; *)
           let vs', es' = [], [Returning vs @@ e.at] in
           lv, [{c with code = vs', es' @ List.tl es}]

        | Call x, vs ->
           (* print_endline "call"; *)
           let vs', es' = vs, [Invoke (func frame.inst x) @@ e.at] in
           lv, [{c with code = vs', es' @ List.tl es}]

        (* | CallIndirect x, I32 i :: vs ->
         *   let func = func_elem frame.inst (0l @@ e.at) i e.at in
         *   if type_ frame.inst x <> Func.type_of func then
         *     vs, [Trapping "indirect call type mismatch" @@ e.at]
         *   else
         *     vs, [Invoke func @@ e.at] *)

        | Drop, v :: vs' ->
           (* print_endline "drop"; *)
           let vs', es' = vs', [] in
           lv, [{c with code = vs', es' @ List.tl es}]
           
        | Select, v0 :: v2 :: v1 :: vs' ->
           (* print_endline "select"; *)
           let vselect = select_condition v0 v1 v2 in
           (* let pc' = PCAnd(cond, pc) in *)
           let vs', es' = vselect :: vs', [] in
           lv, [{c with code = vs', es' @ List.tl es}]
           
        | LocalGet x, vs ->
           (* print_endline "local get"; *)
           let vs', es' = (local frame x) :: vs, [] in
           lv, [{c with code = vs', es' @ List.tl es}]

        | LocalSet x, v :: vs' ->
           (* print_endline "local set"; *)
           if (!Flags.debug) then (
             print_endline "localset fv";
             print_endline (string_of_region e.at));


           (* let vv = local frame x in *)

           let lv = if c.ct_check then (
                      let mem = get_mem_tripple frame in 
                      (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc v mem in *)
                      let is_low = Z3_solver.is_v_ct_unsat ~timeout:300 c.pc v mem in
                      if (!Flags.debug) then (
                        print_endline (string_of_bool is_low););

                      
                      let mo = Nothing in (*compare_svalues v v in*)
                      let _,simp = Z3_solver.simplify v c.pc mem in
                      (* print_loopvar (LocalVar (x, is_low)); *)
                      (LocalVar (x, is_low, mo, Some (v,simp)))::lv)
                    else lv
           in
           (* let v, c =
            *   if svalue_depth v 10 then (
            *     let nl, pc' = add_let (pcnum, pclet, pc) (Sv v) in
            *     let nv = svalue_newlet (Sv v) nl in
            *     (\* let eq = svalue_eq nv v in *\)
            *     let c = {c with pc = pc'} in 
            *     nv,c)
            *   else
            *     v, c
            * in *)
           let frame' = update_local c.frame x v in
           let vs', es' = vs', [] in
           lv, [{c with code = vs', es' @ List.tl es; frame = frame'}]

        | LocalTee x, v :: vs' ->
               if (!Flags.debug) then (
                 print_endline "localtee fv";
                 print_endline (string_of_region e.at));


           (* print_endline "local tee"; *)
           (* let vv = local frame x in *)
           let lv = if c.ct_check then (
                      let mem = get_mem_tripple frame in 
                      (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc v mem in *)
                      let is_low = Z3_solver.is_v_ct_unsat ~timeout:300 c.pc v mem in
                      let mo = Nothing in (*compare_svalues vv v in*)
                      let _,simp = Z3_solver.simplify v c.pc mem in
                      (LocalVar (x, is_low, mo, Some (v,simp)))::lv)
                    else lv
           in
           (* print_loopvar (LocalVar (x,is_low)); *)
           let frame' = update_local c.frame x v in
           let vs', es' = v :: vs', [] in
           lv, [{c with code = vs', es' @ List.tl es; frame = frame'}]

        | GlobalGet x, vs ->
           let vs', es' = Sglobal.load (sglobal frame.inst x) :: vs, [] in
           lv, [{c with code = vs', es' @ List.tl es}]

        | GlobalSet x, v :: vs' ->

           (* let vv = Sglobal.load (sglobal c.frame.inst x) in *)
           let mem = get_mem_tripple frame in 
           let is_low = Z3_solver.is_v_ct_unsat ~timeout:300 c.pc v mem in
           (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc v mem in *)
           let mo = Nothing in (* compare_svalues vv v in *)
           let _, simp = Z3_solver.simplify v c.pc mem in
           let lv = (GlobalVar (x, is_low, mo, Some (v,simp)))::lv in
           let newg, vs', es' =
             (try Sglobal.store (sglobal frame.inst x) v, vs', []
              with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                 | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
           in
           let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
           lv, [{c with code = vs', es' @ List.tl es; frame = frame'}]

        | Load {offset; ty; sz; _}, si :: vs' ->
           (* print_endline "load"; *)
           if (!Flags.debug) then (
             print_endline "load fv";
             print_endline (string_of_region e.at));
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
                          (smemlen frame.inst) (smemnum frame.inst)
                          (Types.size ty) None
              | Some (sz, ext) ->
                 assert (packed_size sz <= Types.size ty);
                 let n = packed_size sz in 
                 Eval_symbolic.eval_load ty final_addr
                   (smemlen frame.inst) (smemnum frame.inst) n (Some ext)
             )
           in

           let vs', es' =  nv :: vs', [] in 

           lv, [{c with code = vs', est}]
           
        | Store {offset; ty; sz; _}, sv :: si :: vs' ->
           (* print_endline "store"; *)
           if (!Flags.debug) then (
             print_endline "store fv";
             print_endline (string_of_region e.at));


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

           (* if (Z3_solver.is_v_ct_unsat (pcnum, pclet, pc) si mems) then *)
           let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in
           let num = Instance.next_num() in
           let nv, lvn =
             (match sz with
              | None ->
                 let nv = Eval_symbolic.eval_store ty final_addr sv
                            (smemlen frame.inst) num (Types.size ty) in
                 let lvn = (Eval_symbolic.eval_load ty final_addr
                              (smemlen frame.inst) (smemnum frame.inst)
                              (Types.size ty) None) in
                 nv,lvn
              | Some (sz) ->
                 assert (packed_size sz <= Types.size ty);
                 let n = packed_size sz in
                 let nv = Eval_symbolic.eval_store ty final_addr sv
                            (smemlen frame.inst) num n in
                 let lvn = Eval_symbolic.eval_load ty final_addr
                             (smemlen frame.inst) (smemnum frame.inst)
                             n None in
                 nv, lvn)
           in

           (* Check store variable only if they have constant index *)
           (* We might for example be storing the loop index in memory *)
           let memtuple = get_mem_tripple frame in 
           (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc sv memtuple in *)
           let is_low = Z3_solver.is_v_ct_unsat ~timeout:300 c.pc sv memtuple in 
           (* let mo = compare_svalues lvn sv in *)
           if (!Flags.debug) then (
             print_endline (string_of_bool is_low););
           (* let tf, simp = Z3_solver.simplify final_addr c.pc  memtuple in *) 
           let lv = (StoreVar (Some final_addr, ty, sz, is_low, Nothing, e.at))::lv in

           let mem' = Smemory.store_sind_value num mem nv in
           let vs', es' = vs', [] in
           (* Update memory with a store *)
           let nframe = {frame with inst = insert_smemory frame.inst num mem'} in

           lv, [{c with code = vs', es' @ est;
                                    frame = nframe}]

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
           lv, [{c with code = vs', es' @ List.tl es}]
           
        (* | Const v, vs ->
         *    v.it :: vs, [] *)

        | Test testop, v :: vs' ->
           (* print_endline "testop"; *)
           let vs', es' =
             (try (svalue32_of_bool (Eval_symbolic.eval_testop testop v)) :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           lv, [{c with code = vs', es' @ List.tl es}]
           
        | Compare relop, v2 :: v1 :: vs' ->
           (* print_endline "relop"; *)
           let vs', es' =
             (try (svalue32_of_bool (Eval_symbolic.eval_relop relop v1 v2)) :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           lv, [{c with code = vs', es' @ List.tl es}]

        | Unary unop, v :: vs' ->
           (* print_endline "unop"; *)
           let vs', es' = 
             (try Eval_symbolic.eval_unop unop v :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           lv, [{c with code = vs', es' @ List.tl es}]

        | Binary binop, v2 :: v1 :: vs' ->
         (* print_endline "binop";
            print_endline (Pc_type.svalue_to_string v1);
            print_endline (Pc_type.svalue_to_string v2); *)
           let vs', es' = 
             (try
                let nv = Eval_symbolic.eval_binop binop v1 v2 in
                (* "Printing binop" |> print_endline; *)
                (* Pc_type.svalue_to_string nv |> print_endline; *)
                nv :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           lv, [{c with code = vs', es' @ List.tl es}]
        | Convert cvtop, v :: vs' ->
           let vs', es' = 
             (try Eval_symbolic.eval_cvtop cvtop v :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
           in
           lv, [{c with code = vs', es' @ List.tl es}]

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

    | Assert (_,_,_), vs ->
       failwith "Unexpected Assert in find_vars";
       
    | Havoc lvs, vs ->
       failwith "Unexpected Havoc in find_vars";

    | SecondPass _, vs ->
       failwith "Unexpected SecondPass in find_vars";

    | NonCheckPass _, vs ->
       failwith "Unexpected NonCheck in find_vars";

    | FirstPass _, vs ->
       failwith "Unexpected FirstPass in find_vars";

    (* assert false *)

    | Returning vs', vs ->
       Crash.error e.at "undefined frame"

    | Breaking (k, vs'), vs ->
       if !Flags.debug then print_endline "breaking fv";
       lv, []
    (* Crash.error e.at "undefined label" *)

    | Label (n, es0, (vs', []), pc', iv', cct'), vs ->
       (*print_endline "lab";*)
       let vs', es' = vs' @ vs, [] in
       lv, [{c with code = vs', es' @ List.tl es}]
       
    | Label (n, es0, (vs', {it = Trapping msg; at} :: es'), pc', iv', cct'), vs ->
       (* print_endline "lab2"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       lv, [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Returning vs0; at} :: es'), pc', iv', cct'), vs ->
       (*print_endline "lab3";*)
       let vs', es' = vs, [Returning vs0 @@ at] in
       lv, [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (0l, vs0); at} :: es'), pc', iv', cct'), vs ->
       (*print_endline "lab4";*)
       if (!Flags.debug) then (
             print_endline "lab br fv";
             print_endline (string_of_region e.at));


       let vs', es' = take n vs0 e.at @ vs, es0 in
       lv, [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (k, vs0); at} :: es'), pc', iv', cct'), vs ->
       (*print_endline "lab5"; *)
       let vs', es' = vs, [Breaking (Int32.sub k 1l, vs0) @@ at] in
       lv, [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, code', pc', iv', cct'), vs ->
       (*print_endline "lab6"; *)
       (* TODO(Romy): not sure if correct to change the pc *)
       let lv', c' = fv_step analyzed_loop lv {c with code = code'; 
                                               pc = pc';
                                               induction_vars = iv';
                                               ct_check = cct'} in
       (*print_endline "lab6_back";*)
       let res = List.map (fun ci ->
             {c with code = vs,
                          [Label (n, es0, ci.code, ci.pc,
                          ci.induction_vars, ci.ct_check) @@ e.at]
                          @ List.tl es;
                     pc = ci.pc; 
                     frame = ci.frame}) c'
       in
       (* print_endline "lab6_end"; *)
       lv', res

    | Frame (n, frame', (vs', []), pc', iv'), vs ->
       (* print_endline ("frame1:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs' @ vs, [] in
       let c = {c with code = vs', es' @ List.tl es;
                       frame = {frame
                               with inst = {frame.inst
                                           with smemories = frame'.inst.smemories;
                                                smemlen = frame'.inst.smemlen;
                                                smemnum = frame'.inst.smemnum;
                                                sglobals = frame'.inst.sglobals
                                           }
                               };
                       pc = pc';
                       induction_vars = iv'
               } in
       lv, [c]
    | Frame (n, frame', (vs', {it = Trapping msg; at} :: es'), _, _), vs ->
       (* print_endline "frame2"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       lv, [{c with code = vs', es' @ List.tl es}]

    | Frame (n, frame', (vs', {it = Returning vs0; at} :: es'), pc', iv'), vs ->
       (* print_endline "frame returning"; *)
       (* print_endline ("frame3:" ^ (string_of_int c.counter)); *)
       let vs', es' = take n vs0 e.at @ vs, [] in
       let c = {c with code = vs', es' @ List.tl es;
                       frame = {frame
                               with inst = {frame.inst
                                           with smemories = frame'.inst.smemories;
                                                smemlen = frame'.inst.smemlen;
                                                smemnum = frame'.inst.smemnum;
                                                sglobals = frame'.inst.sglobals
                                           }
                               };
                       pc = pc';
                       induction_vars = iv'} in
       lv, [c]

    | Frame (n, frame', code', pc', iv'), vs ->
       (* print_endline "frame4"; *)
       let lv', c' = fv_step analyzed_loop lv {c with frame = frame'; code = code';
                                              budget = c.budget - 1; pc = pc';
                                              induction_vars = iv'} in
       (* print_endline "frame4_end"; *)
       (* TODO(Romy): the pc etc  should probably not be here *)
       
       let res = List.map
         (fun ci ->
             {c with code = vs, [Frame (n, ci.frame,
                                          ci.code, ci.pc,
                                          ci.induction_vars)
                                       @@ e.at] @ List.tl es;}
          ) c'
       in
       lv', res 

    | Invoke func, vs when c.budget = 0 ->
       Exhaustion.error e.at "call stack exhausted"

    | Invoke func, vs ->
       (* print_endline "inv2"; *)
       let FuncType (ins, out) = func_type_of func in
       let n1, n2 = Lib.List32.length ins, Lib.List32.length out in

       let vs' = drop n1 vs e.at in
       let vs'' = add_high out in

       lv, [{c with code = vs'' @ vs', List.tl es}]
       
       (* let args, vs' = take n1 vs e.at, drop n1 vs e.at in
        * (match func with
        *  | Func.AstFunc (t, inst', f) ->
        *     let rest = List.map value_to_svalue_type f.it.locals in
        *     (\* let locals' = List.rev args @ List.map Svalues.default_value rest in *\) 
        *     let locals' = List.rev args @ List.map Svalues.default_value rest in
        * 
        *     let nsmem = if (List.length frame.inst.smemories == 0) then !inst'.smemories
        *                 else frame.inst.smemories
        *     in
        *     let sglobals =  if (List.length frame.inst.sglobals == 0) then !inst'.sglobals
        *                     else frame.inst.sglobals in
        *     let nmemlen = List.length nsmem in
        *     let inst' = {!inst' with smemories = nsmem;
        *                              smemlen =  nmemlen;
        *                              sglobals = sglobals;
        *                 } in
        * 
        * 
        *     let frame' = {inst = inst'; locals = locals'} in
        *     let instr' = [Label (n2, [], ([], List.map plain f.it.body),
        *                          c.pc, c.induction_vars, false) @@ f.at] in 
        *     let vs', es' = vs', [Frame (n2, frame', ([], instr'), c.pc, c.induction_vars) @@ e.at] in
        *     lv, [{c with code = vs', es' @ List.tl es}] *)

        (* | Func.HostFunc (t, f) ->
         *   (try List.rev (f (List.rev args)) @ vs', []
         *   with Crash (_, msg) -> Crash.error e.at msg) *)
        (* | _ -> Crash.error e.at "Func.Hostfunc not implemented yet." *)
       (* ) *)
    )



let fv_eval_dfs (analyzed_loop : int) (cs : config list) 
                : loopvar_t list =
  let rec fv_eval_dfs_i (cs : config list) (acc: loopvar_t list) : loopvar_t list =
    (* print_endline "eval_dfs_i"; *)
    match cs with
    | c::cs' ->
       (match c.code with
        | vs, [] -> fv_eval_dfs_i cs' acc
        | vs, {it = Trapping msg; at} :: _ -> Trap.error at msg
        | vs, es -> (
           let lvs,cs = fv_step analyzed_loop acc c in
           fv_eval_dfs_i (cs @ cs') lvs
        )
       )
      
    | [] -> acc
  in
  fv_eval_dfs_i cs []

let fv_eval (analyzed_loop: int) (c : config) = 
    fv_eval_dfs analyzed_loop [c]

let find_policy lvs c  =
  if !Flags.debug then (
    print_endline "Find policy of already analyzed loop"
  );
  let rec find_policy_i lvs acc =
    match lvs with
    | (LocalVar (x,_,mo,v)) :: lvs' ->
       let vv = local c.frame x in
       let mem = get_mem_tripple c.frame in 
       let is_low = Z3_solver.is_v_ct_unsat ~timeout:300 c.pc vv mem in
       (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc vv mem in *)
       let mo = Nothing in
       find_policy_i lvs' (LocalVar (x,is_low,mo, v)::acc)
    | (GlobalVar (x,_,mo,v)) :: lvs' ->
       let vv = Sglobal.load (sglobal c.frame.inst x) in
       let mem = get_mem_tripple c.frame in 
       let is_low = Z3_solver.is_v_ct_unsat ~timeout:300 c.pc vv mem in
       (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc vv mem in *)
       let mo = Nothing in
       find_policy_i lvs' (GlobalVar (x,is_low,mo, v)::acc)
    | (StoreVar (Some final_addr, ty, sz, is_low, mo, loc)) :: lvs' ->
       let vv =
         (match sz with
          | None ->
             Eval_symbolic.eval_load ty final_addr
               (smemlen c.frame.inst) (smemnum c.frame.inst)
               (Types.size ty) None
          | Some (sz) ->
             assert (packed_size sz <= Types.size ty);
             let n = packed_size sz in
             let lvn = Eval_symbolic.eval_load ty final_addr
                         (smemlen c.frame.inst) (smemnum c.frame.inst)
                         n None in
             lvn)
       in
       let mem = get_mem_tripple c.frame in
       let is_low = Z3_solver.is_v_ct_unsat ~timeout:300 c.pc vv mem in
       (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc vv mem in *)
       let mo = Nothing in
       find_policy_i lvs' (StoreVar (Some final_addr, ty, sz, is_low, mo, loc)::acc)

    | (StoreZeroVar (sv) as lh) :: lvs' ->
       find_policy_i lvs' (lh::acc)
    | lh :: lvs' -> (* TODO(Check this)*)
       find_policy_i lvs' (lh::acc)
    | [] -> List.rev acc
  in
  find_policy_i lvs []




let compare_policies lvs1 lvs2 =
  if !Flags.debug then (
    print_endline "Comparing policies"
  );
  let rec compare_policies_i lvs1 lvs2 = 
    match lvs1,lvs2 with
    | (LocalVar (_,il1,_,_)) :: lvs1', (LocalVar (_,il2,_,_)) :: lvs2'
         when il1 = il2 ->
       compare_policies_i lvs1' lvs2'
    | (GlobalVar (_,il1,_,_)) :: lvs1', (GlobalVar (_,il2,_,_)) :: lvs2'
         when il1 = il2 ->
       compare_policies_i lvs1' lvs2'
    | (StoreVar (_,_,_,il1,_,_)) :: lvs1', (StoreVar (_,_,_,il2,_,_)) :: lvs2'
         when il1 = il2 ->
       compare_policies_i lvs1' lvs2'
    | (LocalVar (_,il1,_,_)) :: lvs1', (LocalVar (_,il2,_,_)) :: lvs2' ->
       false
    | (GlobalVar (_,il1,_,_)) :: lvs1', (GlobalVar (_,il2,_,_)) :: lvs2' ->
       false
    | (StoreVar (_,_,_,il1,_,_)) :: lvs1', (StoreVar (_,_,_,il2,_,_)) :: lvs2' ->
       false
    | [], [] -> true
    | _, _ -> failwith "Not matching variables."  
  in
  compare_policies_i lvs1 lvs2
