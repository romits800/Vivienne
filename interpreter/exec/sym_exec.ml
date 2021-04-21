open Svalues
open Types
open Instance
open Ast
open Source
open Pc_type
open Eval
open Havoc
open Merge_vars
open Find_vars
open Find_induction_vars
open Elim_induction_vars
open Config
open Loop_stats   


let simplify_v frame (pc: pc_ext) v =
  if svalue_depth v 5 then (
    let mem = get_mem_tripple frame in
    (match Z3_solver.simplify v pc mem with
     | false, v 
       | true, (Z3Expr32 _ as v)
       | true, (Z3Expr64 _ as v) -> 
        let nl, pc' = add_let pc v in
        let nv = svalue_newlet v nl in
        (* let eq = svalue_eq nv v in *)
        (* let c = {c with pc = pc'} in *) 
        nv, pc'
     | true, Sv v ->
        (* print_endline "true";
         * svalue_to_string v |> print_endline; *)
        v, pc
    )
  ) else
    v, pc

(* let simplify_pc frame pc =
 *   let pclet, pc = pc in
 *   if pc_depth pc 10 then (
 *     let mem = (frame.inst.smemories, smemlen frame.inst) in
 *     (match Z3_solver.simplify_pc (pclet,pc) mem with
 *      | false, pc 
 *        | true, pc -> pc
 *     )
 *   ) else
 *     (pclet,pc) *)

module ModifiedVarsMap = Map.Make(struct
                              type t = int
                              let compare = (-)
                            end)
let modified_vars = ref ModifiedVarsMap.empty 
                       
(* module AnalyzedLoopsMap = Map.Make(struct
 *                               type t = int
 *                               let compare = compare
 *                             end)
 *                         
 * let analyzed_loops = ref AnalyzedLoopsMap.empty *) 



module VulnerabilitiesMap = Map.Make(struct
                                type t = int
                                let compare = (-)
                              end)
(* Vulnerability types *)
                        
let cond_vuln = ref VulnerabilitiesMap.empty
let noninter_vuln = ref VulnerabilitiesMap.empty

let memindex_vuln = ref VulnerabilitiesMap.empty 

                   


let estimate_loop_size e' bt frame e vs pcext es' c es = 
  let pcnum, pclet, pc = pcext in
  try (
    (* print_endline (string_of_int (Obj.magic e')); *)
    let maxl = find_maxloop (Obj.magic e') in
    if maxl < magic_number_loop_inv then (
      let FuncType (ts1, ts2) = block_type frame.inst bt in
      let n1 = Lib.List32.length ts1 in
      let args, vs' = take n1 vs e.at, drop n1 vs e.at in
      let vs', es' = vs', [Label (n1, [Plain e' @@ e.at],
                                  (args, List.map plain es'), pcext,
                                  c.induction_vars, c.ct_check) @@ e.at] in
      [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
    ) else (
      failwith ("Not expected to be greater than " ^ (string_of_int maxl)); 
    )
  )
  with Not_found -> (
    let FuncType (ts1, ts2) = block_type frame.inst bt in
    let n1 = Lib.List32.length ts1 in
    let args, vs' = take n1 vs e.at, drop n1 vs e.at in

    (* HAVOC *)
    let lvs =
      let index = (Obj.magic e') in
      try (
        let lvs = ModifiedVarsMap.find index !modified_vars in
        (* check if we have different initial policy *)
        find_policy lvs c
      ) with Not_found -> (
        let vs'', es'' = vs', [Label (n1, [Plain e' @@ e.at],
                                      (args, List.map plain es'), (pcnum, pclet,pc),
                                      c.induction_vars, c.ct_check) @@ e.at] in
        (*let lvs, _ = find_modified_vars (Obj.magic e')*)
        let lvs = fv_eval (Obj.magic e')
                    {c with code = vs'', es''} in (* @ List.tl es;} in*)
        let lvs = merge_vars lvs in
        modified_vars := ModifiedVarsMap.add index lvs !modified_vars;
        lvs
      )
    in
    
    if !Flags.debug then (
      print_endline "printing loopvars.";
      List.iter print_loopvar lvs
    );
    let havc = havoc_vars lvs c (Loop_stats.init_stats()) in

    (* FIND INDUCTION VARIABLES *)
    let vs'', es'' = vs', [Label (n1, [],
                                  (args, List.map plain es'), (pcnum, pclet,pc),
                                  c.induction_vars, c.ct_check) @@ e.at] in
    let nhavc = {havc with code = vs'', es'' @ List.tl es;} in
    let nc = {c with code = vs'', es'' @ List.tl es;} in
    let iv, havc' = induction_vars nhavc nc lvs in


    (* RUN ONE PASS TO REPLACE THE INDUCTION VARIABLES *)
    (* print_endline "NonCheckPass Putting checkpass in the queue"; *)
    let nc_pass = NonCheckPass (n1, [Plain e' @@ e.at],
                                (args, List.map plain es'), iv, lvs, c) in
    let vs', es' = vs', [Label (n1, [nc_pass @@ e.at],
                                (args, List.map plain es'),
                                havc'.pc,
                                havc'.induction_vars, false) @@ e.at ] in
    [{havc' with code = vs', es' @ List.tl es; progc = Obj.magic e'}]

  )


                  
(*   assertX;
     havocv1; ... ;havocvn;
     assume X;
     if(c) {
       B;
       assertX;
       assume false;
     } *)



let loop_invariant e' bt frame e vs es es' pcext c stats =
  let FuncType (ts1, ts2) = block_type frame.inst bt in
  let n1 = Lib.List32.length ts1 in
  let args, vs' = take n1 vs e.at, drop n1 vs e.at in

  if !Flags.unroll_one then (
    
    let second_pass = SecondPass (n1, [Plain e' @@ e.at],
                                  (args, List.map plain es')) in

    let vs'', es'' = vs', [Label (n1, [second_pass @@ e.at],
                                  (args, List.map plain es'), pcext,
                                  c.induction_vars, c.ct_check) @@ e.at] in

    [{c with code = vs'', es'' @ List.tl es; progc = Obj.magic e'}]

  ) else (
    
    let vs'', es'' = vs', [Label (n1, [Plain e' @@ e.at],
                                  (args, List.map plain es'), pcext,
                                  c.induction_vars, c.ct_check) @@ e.at] in

    if !Flags.debug then 
      print_endline "Finding variables modified in loop..";

    (* print_endline "Finding vars"; *)
    let lvs, analyzed =
      (* let index = (Obj.magic e') in *)
      (*try (
        let lvs = ModifiedVarsMap.find index !modified_vars in
        (* check if we have different initial policy *)
        let lvs' = find_policy lvs c in
        lvs', compare_policies lvs lvs'
        
      ) with Not_found -> ( *)
        (*let lvs, _ = find_modified_vars (Obj.magic e')*)
        let lvs = fv_eval (Obj.magic e')
                    {c with code = vs'', es''} in (* @ List.tl es;} in*)

        if !Flags.debug then (
          print_endline ("Printing loopvars 1." ^ (string_of_int (Obj.magic e')));
          List.iter print_loopvar lvs
        );

        let lvs = merge_vars lvs in
        (* modified_vars := ModifiedVarsMap.add index lvs !modified_vars; *)
        lvs, false
      (* ) *)
    in
    if !Flags.debug then (
      print_endline ("Printing loopvars." ^ (string_of_int (Obj.magic e')));
      List.iter print_loopvar lvs
    );

    (* HAVOC *)
    let havc = havoc_vars lvs c stats in
    (*print_pc havc.pc |> print_endline; *)
    if !Flags.elim_induction_variables then (
      let vs'', es'' = vs', [Label (n1, [], (*Plain e' @@ e.at],*)
                                    (args, List.map plain es'), 
                                    pcext,
                                    c.induction_vars, c.ct_check) @@ e.at] in
      let nhavc = {havc with code = vs'', es'' (*@ List.tl es;*)} in
      let nc = {c with code = vs'', es'' @ List.tl es;} in
      let iv, havc' = induction_vars nhavc nc lvs in

      let nc_pass = NonCheckPass (n1, [Plain e' @@ e.at],
                                  (args, List.map plain es'), iv, lvs, c) in
      let vs', es' = vs', [Label (n1, [nc_pass @@ e.at],
                                  (args, List.map plain es'),
                                  havc'.pc,
                                  havc'.induction_vars, false) @@ e.at ] in
      [{havc' with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
    ) else (                     
      let assrt = Assert (lvs, e', analyzed) in
      let vs', es' = vs', [Label (n1, [assrt @@ e.at],
                                  (args, List.map plain es'),
                                  havc.pc,
                                  havc.induction_vars, true) @@ e.at ] in
      [{havc with code = vs', es' @ List.tl es; progc = Obj.magic e'}]

    ) (* No elim induction vars *)
  ) (* No unroll *)



(* Symbolic Execution *)

(*
 * Conventions:
 *   e  : instr
 *   v  : svalue
 *   es : instr list
 *   vs : svalue stack
 *   c : config
 *)

  
let rec step (c : config) : config list =
  let {frame; code = vs, es; pc = pcnum, pclet, pc; _} = c in
  let e = List.hd es in


  let vs, (pcnum, pclet, pc) = 
      match vs with
      | v::vs' ->
         if svalue_depth v 5 then (
           if (!Flags.simplify) then (
             let v, pc' = simplify_v frame (pcnum, pclet,pc) v in
             v::vs', pc'
           ) else (
             let nl, pc' = add_let (pcnum, pclet, pc) (Sv v) in
             (* print_endline (string_of_int nl);
              * print_endline (svalue_to_string v); *)
             let nv = svalue_newlet (Sv v) nl in
             nv::vs', pc'
           )
         ) else (
           vs, (pcnum, pclet,pc)
         )
      | [] -> vs, (pcnum, pclet,pc)
  in
  (* let pclet,pc = simplify_pc frame (pclet,pc) in *)
  let c = {c with pc = (pcnum, pclet,pc)} in
  let vs = 
    if (!Flags.replace_expressions >= 0 && (Random.int !Flags.replace_expressions == 0)) then (
      if !Flags.debug then (
        print_endline "Testing expression simplification.";
      );
      match vs with
      | v::vs' -> 
         let mem = get_mem_tripple frame in
         let num_exprs = Z3_solver.get_num_exprs (pcnum, pclet,pc) v mem in
         if num_exprs > magic_number_num_exprs then (
           if !Flags.debug then (
             print_endline ("Num exprs: " ^ (string_of_int num_exprs) ^ " " ^ (string_of_region e.at));
           );

           let v = 
           if (num_exprs > magic_number_num_exprs_max) || not (Z3_solver.is_v_ct_unsat ~timeout:60 (pcnum, pclet, pc) v mem) 
           then (
             match v with
             | SI32 v -> (SI32 (Si32.of_high()))
             | SI64 v -> (SI64 (Si64.of_high()))
             | _ -> failwith "Not supporting floats."             
            ) else ( 
             match v with
             | SI32 v -> (SI32 (Si32.of_low()))
             | SI64 v -> (SI64 (Si64.of_low()))
             | _ -> failwith "Not supporting floats."
           )
           in
           if !Flags.debug then (
               print_endline ("Simplified" ^ (svalue_to_string v));
           );
           v::vs'
         )
         else vs
      | [] -> [] ) 
    else vs
  in
  (* print_endline ("Step:" ^ (string_of_int c.counter)); *)
  let res =
    match e.it, vs with
    | Plain e', vs ->

       (match e', vs with
        | Unreachable, vs ->
           (* print_endline "Unreachable"; *)
           let vs', es' = vs, [Trapping "unreachable executed" @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
        | Nop, vs ->
           (* print_endline "nop"; *)
           (*let mem = (frame.inst.smemories, smemlen frame.inst) in
           let v  =  Eval_symbolic.eval_load I32Type (SI32 (Si32.of_int32 67876l))
                       (smemlen frame.inst) 4 None in
           
           let solv = Z3_solver.is_ct_unsat (pclet, pc) v mem in
           
           print_endline (string_of_bool solv);
           *)
           let vs', es' = vs, [] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'};]
        | Block (bt, es'), vs ->
           (* print_endline "block";
            * print_endline (string_of_region e.at); *)
           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let n2 = Lib.List32.length ts2 in
           let args, vs' = take n1 vs e.at, drop n1 vs e.at in
           let vs', es' = vs', [Label (n2, [], (args, List.map plain es'),
                                       (pcnum, pclet,pc), c.induction_vars, c.ct_check) @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
        | Loop (bt, es'), vs ->
           if !Flags.debug then (
             print_endline "Entering loop..";
             print_endline (string_of_region e.at);
             (* print_endline ("Number of local variables: " ^ (string_of_int (List.length frame.locals))); *)
             print_endline ("Loop number of instructions: " ^ (string_of_int (List.length es')));
           );
           
               (*let tmp_select reg = 
                match reg.left.line with
                | 27694
                 | 27728 
                 | 27927
                 | 24689
                 | 24792 -> true
                | _ -> false
               in*)


           (match loop_stats es' e.at with
              stats ->
               if !Flags.stats then (
                 print_endline (string_of_region e.at);
                 print_endline ("Number of local variables: " ^ (string_of_int (stats.number_modified)));
                 print_endline ("Possible loop iterations: " ^ (string_of_int (stats.possible_loop_iterations)));
                 print_endline ("Number instructions: " ^ (string_of_int (stats.number_instructions)));
                 print_endline ("Number calls: " ^ (string_of_int (stats.number_calls)));
                 print_endline ("Number ifs: " ^ (string_of_int (stats.number_ifs)));
                 print_endline ("Number mem ops: " ^ (string_of_int (stats.number_mem_ops)));
               );
               let pcext = pcnum, pclet, pc in
               if !Flags.estimate_loop_size then (
                 (* failwith "Estimate loop size not supported." *)
                 estimate_loop_size e' bt frame e vs pcext es' c es 
               )
               else if !Flags.loop_invar &&
                         select_invar stats (*&& tmp_select e.at*) then (
                 if !Flags.debug then print_endline "Running loop invariant.";
                 loop_invariant e' bt frame e vs es es' pcext c stats
               )
               else ( (* Not using loop invariants *)
                 let FuncType (ts1, ts2) = block_type frame.inst bt in
                 let n1 = Lib.List32.length ts1 in
                 let args, vs' = take n1 vs e.at, drop n1 vs e.at in
                 let vs', es' = vs', [Label (n1, [Plain e' @@ e.at],
                                             (args, List.map plain es'),
                                             (pcnum, pclet,pc),
                                             c.induction_vars, c.ct_check) @@ e.at] in
                 [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
                 )
            (* | stats, true -> (\* No stats *\)
             *    let pcext = pcnum, pclet, pc in
             *    if !Flags.loop_invar (\*&& tmp_select e.at*\) then (
             *      if !Flags.debug then print_endline "Running loop invariant.";
             *      loop_invariant e' bt frame e vs es es' pcext c
             *     ) else (
             *    let FuncType (ts1, ts2) = block_type frame.inst bt in
             *    let n1 = Lib.List32.length ts1 in
             *    let args, vs' = take n1 vs e.at, drop n1 vs e.at in
             *    let vs', es' = vs', [Label (n1, [Plain e' @@ e.at],
             *                                (args, List.map plain es'), (pcnum, pclet,pc),
             *                                c.induction_vars, c.ct_check) @@ e.at] in
             *    [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
             *    ) *)
           )
        | If (bt, es1, es2), v :: vs' ->
           if (!Flags.debug) then (
             print_endline "if";
             print_endline (string_of_region e.at);
             print_endline (svalue_to_string v)
           );
           let pc', pc'' = split_condition v (pcnum, pclet, pc) in (* false, true *)
           let vs'', es'' = vs', [Plain (Block (bt, es1)) @@ e.at] in (* True *)
           let vs', es' = vs', [Plain (Block (bt, es2)) @@ e.at] in (* False *)
           (* Check sat of if *)
           
           let mem = get_mem_tripple frame in
           
           let c = {c with observations = CT_UNSAT((pcnum, pclet,pc), v, mem, c.observations)} in
           
           let res =
             let pcnum' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum', pclet, pc') mem then
               [{c with code = vs', es' @ List.tl es;
                        pc =(pcnum', pclet,pc');
                        progc = Obj.magic e'}]
             else [] in
           let res =
             let pcnum'' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum'', pclet, pc'') mem then
               {c with code = vs'', es'' @ List.tl es;
                       pc = (pcnum'', pclet,pc'');
                       progc = (Obj.magic e')+ 1}::res
             else res in
           if (!Flags.debug) then (
             print_endline "if";
             print_endline (string_of_int (List.length res))
           );
 
           (match res with
            | [] -> failwith "If: No active path";
               (* let vs', es' = vs, [] in
                * [{c with code = vs', es' @ List.tl es}] *)
            | _::[] -> res
            | _ ->
               if (c.ct_check) then (
                 (* print_endline ("ct_check if" ^ (Source.string_of_region e.at)); *)
                 let index =  (Obj.magic e') in
                 (try let _ = VulnerabilitiesMap.find index !cond_vuln in ()
                  with Not_found ->
                   let solv = Z3_solver.is_ct_unsat (pcnum, pclet, pc) v mem in
                   if solv then () else (
                     cond_vuln := VulnerabilitiesMap.add (Obj.magic e') solv !cond_vuln;
                     ConstantTime.warn e.at "If: Constant-time Violation"
                   )
                 );
                 res
                
               ) else res
           )

        | Br x, vs ->
           (* print_endline "br"; *)
           let vs', es' = [], [Breaking (x.it, vs) @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
           
        | BrIf x, v :: vs' ->
           if (!Flags.debug) then (
             print_endline "br_if";
             print_endline (string_of_region e.at);
             print_endline (svalue_to_string v);
             (*let mem = get_mem_tripple frame in
             let _,nv = Z3_solver.simplify v c.pc mem in
             Z3_solver.print_simpl nv; *)
 
            );

           (* print_endline "br_if"; *)
           (* svalue_to_string v |> print_endline; *)
           let pc', pc'' = split_condition v (pcnum, pclet, pc) in (* false, true *)
           let vs'', es'' = vs', [Plain (Br x) @@ e.at] in (* true *) 
           let vs', es' = vs', [] in (* false *)
           
           let mem = get_mem_tripple frame in

           (* proof obligation *)
           let c = {c with observations = CT_UNSAT((pcnum, pclet,pc), v, mem, c.observations)} in
          
           let res =
             let pcnum' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum', pclet, pc') mem then (
               [{c with code = vs', es' @ List.tl es;
                        pc = pcnum', pclet,pc';
                        progc = Obj.magic e'}])
             else [] in
           
           let res =
             let pcnum'' = Pc_type.next_pc_num() in
             if Z3_solver.is_sat (pcnum'', pclet, pc'') mem then (
                       {c with code = vs'', es'' @ List.tl es;
                               pc = pcnum'', pclet,pc'';
                               progc = Obj.magic e' + 1}::res)
                     else res in
           if (!Flags.debug) then (
             print_endline "br_if";
             print_endline (string_of_int (List.length res))
           );
           (match res with
            | [] -> 
                (*print_endline "BrIf No active path";
                Z3_solver.is_sat (pcnum, pclet, pc) mem |> string_of_bool |> print_endline;
                *)
                failwith "BrIf: No active path";
            | _::[] -> res
            | _ ->
               if (c.ct_check) then (
                 (* print_endline ("ct_check br_if" ^ (Source.string_of_region e.at)); *)
                 let index =  (Obj.magic e') in
                 (try let _ = VulnerabilitiesMap.find index !cond_vuln in ()
                  with Not_found ->
                    let solv = Z3_solver.is_ct_unsat (pcnum, pclet, pc) v mem in
                    if solv then () else (
                      cond_vuln := VulnerabilitiesMap.add index solv !cond_vuln;
                      ConstantTime.warn e.at "Br_if: Constant-time Violation"
                    )
                 );
                 res
               )
               else res
           )

        (* Must be unsat *)
           
        (* | BrTable (xs, x), I32 i :: vs' when I32.ge_u i (Lib.List32.length xs) ->
         *   vs', [Plain (Br x) @@ e.at]
         * 
         * | BrTable (xs, x), I32 i :: vs' ->
         *   vs', [Plain (Br (Lib.List32.nth xs i)) @@ e.at] *)

        | Return, vs ->
           (* print_endline "return"; *)
           let vs', es' = [], [Returning vs @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]

        | Call x, vs ->
           if !Flags.debug then (
             print_endline ("Calling function:" ^ string_of_int (Int32.to_int x.it))
            ); 
           (* print_endline "call";
            * print_endline (string_of_int (Int32.to_int x.it)); *)
           let vs', es' = vs, [Invoke (func frame.inst x) @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]

        | CallIndirect x, SI32 i :: vs ->
            if !Flags.debug then (
             print_endline ("Calling indirect function:" ^ svalue_to_string (SI32 i));
             print_endline (print_pc c.pc);
            ); 
            
           (* print_endline "call indirect"; *)

           (* Check Constant-time violation *)
           let mem = get_mem_tripple frame in
           if (Z3_solver.is_v_ct_unsat ~timeout:60  (pcnum, pclet, pc) (SI32 i) mem) then ()
           else ConstantTime.warn e.at "CallIndirect: Constant-time Violation";

           (* print_endline "before find_solutions"; *)
           let i_sol = Z3_solver.find_solutions (SI32 i) (pcnum, pclet, pc) mem  in
           (match i_sol with
            | [] -> failwith "No solution for the symbolic value of the index."
            | _ -> List.map (fun sol ->

                       if !Flags.debug then (
                         print_endline ("Calling indirect:" ^ (string_of_int sol))
                       ); 
 
                       (* print_endline "call indirect_inside";
                        * print_endline (string_of_int sol); *)
                       let func = func_elem frame.inst (0l @@ e.at) (Int32.of_int sol) e.at in
                       if type_ frame.inst x <> Func.type_of func then
                         let vs', es' = vs, [Trapping "indirect call type mismatch" @@ e.at] in
                         {c with code = vs', es' @ List.tl es; progc = Obj.magic e' + sol}
                       else
                         let vs', es' = vs, [Invoke func @@ e.at] in
                         {c with code = vs', es' @ List.tl es; progc = Obj.magic e' + sol}
                     ) i_sol
           )
           
        | Drop, v :: vs' ->
           let vs', es' = vs', [] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
           
        | Select, v0 :: v2 :: v1 :: vs' ->
           (* print_endline "select"; *)
           let vselect = select_condition v0 v1 v2 in
           let vs', es' = vselect :: vs', [] in
           let res = [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}] in
           if (!Flags.select_unsafe) then (
             let mem = get_mem_tripple frame in
             if Z3_solver.is_ct_unsat (pcnum, pclet, pc) v0 mem then res
             else (
               ConstantTime.warn e.at "Select: Constant-time Violation";
               res
             )
           )
           else res
        | LocalGet x, vs ->
           (* print_endline "localget"; *)
           let vs', es' = (local frame x) :: vs, [] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]

        | LocalSet x, v :: vs' ->
           (* print_endline "localset";
            * print_endline (string_of_region e.at); *)
           if !Flags.elim_induction_variables then (
             (try 
                let oldv = local frame x in
                (* print_endline "local set";
                 * print_endline (svalue_to_string oldv); *)
                let ivs = match c.induction_vars with Some ivs -> ivs | None -> failwith "No ivs"; in
                (* print_endline (svalue_to_string oldv); *)
                let init_val, iv, b1, b2 = IndVarMap.find (oldv,e.at) ivs in
                (* print_endline (triple_to_string (init_val, iv, b1, b2)); *)
                let nv, cond = multiply_triple iv b1 b2 in
                (* let pc' = add_equality nv v pc in *)
                let pcnum' = Pc_type.next_pc_num() in
                let pc' = add_condition cond (pcnum', pclet, pc) in
                (* print_endline (Pc_type.svalue_to_string cond); *)
                (* print_endline (Pc_type.svalue_to_string v); *)
                let frame' = update_local c.frame x nv in
                let vs', es' = vs', [] in
                [{c with code = vs', es' @ List.tl es;
                         frame = frame';
                         progc = Obj.magic e';
                         pc = (pcnum', pclet, pc')}]
              with e ->
                let frame' = update_local c.frame x v in
                let vs', es' = vs', [] in
                [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
             )
           ) else (
             if !Flags.debug then (
               (*let mem = get_mem_tripple frame in
               let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc v mem in
               print_endline "localset is_low:";
               print_endline (string_of_bool is_low);*)
             );
             
             let frame' = update_local c.frame x v in
             let vs', es' = vs', [] in
             [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
           )
        | LocalTee x, v :: vs' ->
           (* print_endline "localtee";
            * print_endline (string_of_region e.at); *)
           if !Flags.elim_induction_variables then (
             (try
                (* print_endline "local tee"; *)
                let oldv = local frame x in
                (* print_endline (svalue_to_string oldv); *)
                let ivs = match c.induction_vars with Some ivs -> ivs | None -> failwith "No ivs"; in
                let init_val, iv, b1, b2 = IndVarMap.find (oldv,e.at) ivs in
                (* print_endline (triple_to_string (init_val, iv, b1, b2)); *)
                let nv, cond = multiply_triple iv b1 b2 in
                (* print_endline (Pc_type.svalue_to_string nv);
                 * print_endline (Pc_type.svalue_to_string v); *)
                (* let pc' =  add_equality nv v pc in *)
                let pcnum' = Pc_type.next_pc_num() in
                let pc' = add_condition cond (pcnum', pclet, pc) in
                let frame' = update_local c.frame x nv in
                let vs', es' = nv :: vs', [] in
                [{c with code = vs', es' @ List.tl es;
                         frame = frame';
                         progc = Obj.magic e';
                         pc = (pcnum', pclet, pc')}]
              with e ->
                let frame' = update_local c.frame x v in
                let vs', es' = v :: vs', [] in
                [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
             )
           ) else (
             let frame' = update_local c.frame x v in
             let vs', es' = v :: vs', [] in
             [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
           )
        | GlobalGet x, vs ->
           let vs', es' = Sglobal.load (sglobal frame.inst x) :: vs, [] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]              
           

        | GlobalSet x, v :: vs' ->
           if !Flags.elim_induction_variables then (
             (try 
               let oldv = Sglobal.load (sglobal frame.inst x) in
               let ivs = match c.induction_vars with Some ivs -> ivs | None -> failwith "No ivs"; in
                 let _, iv, b1, b2 = IndVarMap.find (oldv,e.at) ivs in
                 let nv, cond = multiply_triple iv b1 b2 in
                 (* let pc' = add_equality nv v pc in *)
                 let pcnum' = Pc_type.next_pc_num() in
                 let pc' = add_condition cond (pcnum', pclet, pc) in
                 let newg, vs', es' =
                   (try Sglobal.store (sglobal frame.inst x) nv, vs', []
                    with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                       | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
                 in
                 let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
                 [{c with code = vs', es' @ List.tl es;
                          frame = frame';
                          progc = Obj.magic e';
                          pc = (pcnum', pclet, pc')}]
              with _ ->
               let newg, vs', es' =
                 (try Sglobal.store (sglobal frame.inst x) v, vs', []
                  with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                     | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
               in
               let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
               [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}])
               
           ) else (
             let newg, vs', es' =
               (try Sglobal.store (sglobal frame.inst x) v, vs', []
                with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                   | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
             in
             let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
             [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
           )
           
        | Load {offset; ty; sz; _}, si :: vs' ->
           if (!Flags.debug) then (
             print_endline "load";
             print_endline (string_of_region e.at));

           (* print_endline "load"; *)
           (* let imem = smemory frame.inst (0l @@ e.at) in *)

           (* let frame = {frame with
            *               inst = update_smemory frame.inst imem (0l @@ e.at)} in *)
           
           let addr =
             (match si with
              | SI32 v -> v
              | _ -> failwith "Error: Address should be 32-bit integer"
             ) in (* I64_convert.extend_i32_u i in *)
           let offset = Int32.to_int offset in        
           let mem = get_mem_tripple frame in
           let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in



           (* svalue_to_string si |> print_endline;
            * print_endline "printing_test_addr 37356";
            * let test_addr = SI32 (Si32.bv_of_int 37356L 32) in
            * let load = Eval_symbolic.eval_load I32Type test_addr (smemlen frame.inst) (Types.size I32Type) None in
            * let i_sol = Z3_solver.find_solutions load (pcnum, pclet, pc) mem  in
            * List.iter (fun x-> string_of_int x |> print_endline) i_sol; *)
           (* if (c.ct_check) then ( *)
             
             let c = {c with observations = CT_V_UNSAT((pcnum, pclet, pc), final_addr,
                                                       mem, c.observations)} in
             (* let msec = Smemory.get_secrets imem in
              * let mpub = Smemory.get_public imem in *)
             (* let pc', pc'' = split_msec final_addr msec mpub pc in *)
             (* The loaded value consists of the (symbolic) index and the memory
                   index *)
             let nv =
               (* (try *)
               (match sz with
                | None ->
                   Eval_symbolic.eval_load ty final_addr
                     (smemlen frame.inst) (smemnum frame.inst) (Types.size ty) None
                | Some (sz, ext) ->
                   assert (packed_size sz <= Types.size ty);
                   let n = packed_size sz in 
                   Eval_symbolic.eval_load ty final_addr
                     (smemlen frame.inst) (smemnum frame.inst) n (Some ext)
               )
             in

             if (c.ct_check) then (
               let index = (Obj.magic e') in
               let memind, found =
                 try
                   VulnerabilitiesMap.find index !memindex_vuln, true 
                 with Not_found ->
                       let solv = Z3_solver.is_v_ct_unsat ~timeout:60 (pcnum, pclet, pc) final_addr mem in
                       if not solv then (
                         memindex_vuln := VulnerabilitiesMap.add index solv !memindex_vuln
                       );
                       solv, false
               in

               if not found && not memind then 
                 ConstantTime.warn e.at "Load: Constant-time violation"
               else (););
             
             (* let is_low = Z3_solver.is_v_ct_unsat ~timeout:60 (pcnum, pclet, pc) nv mem in
              * print_endline ("Load: is low" ^ (string_of_bool is_low)); *) 
             
             let vs', es' =  nv :: vs', [] in 
             let res =
                  [{c with code = vs', es' @ List.tl es;
                           frame = frame;
                           pc = pcnum, pclet, pc;
                           progc = Obj.magic e'}]
               (* | true, false ->
                *    [{c with code = vs', es' @ List.tl es;
                *             frame = frame;
                *             pc = pcnum, pclet, pc';
                *             progc = Obj.magic e'}]
                * | false, true ->
                *    [{c with code = vs', es' @ List.tl es;
                *             frame = frame;
                *             pc = pcnum, pclet, pc'';
                *             progc = Obj.magic e'}]
                * | false, false -> failwith "Load No path left"; *)
             in
             res
           (* ) *)
           
           (* else (
            *   let nv =
            *     (match sz with
            *      | None -> Eval_symbolic.eval_load ty final_addr
            *                  (smemlen frame.inst) (Types.size ty) None
            *      | Some (sz, ext) ->
            *         assert (packed_size sz <= Types.size ty);
            *         let n = packed_size sz in 
            *         Eval_symbolic.eval_load ty final_addr
            *           (smemlen frame.inst) n (Some ext)
            *     )
            *   in
            * 
            *   let vs', es' =  nv :: vs', [] in 
            *   [{c with code = vs', es' @ List.tl es;
            *            progc = Obj.magic e'}]
            * ) *)
           
        | Store {offset; ty; sz; _}, sv :: si :: vs' ->
           if (!Flags.debug) then (
             print_endline "store";
             print_endline (string_of_region e.at);
             (*print_endline (svalue_to_string sv);
             print_endline (svalue_to_string si)*)
            );

           (*if !Flags.debug then (
             let mem = get_mem_tripple frame in
             let is_low = Z3_solver.is_v_ct_unsat ~timeout:30 c.pc sv mem in

             print_endline "store value is_low:";
             print_endline (string_of_bool is_low);
           );*)

           let mem = smemory frame.inst (0l @@ e.at) in
           (* let frame = {frame with
            *               inst = update_smemory frame.inst mem (0l @@ e.at)} in *)
           let addr =
             (match si with
              | SI32 v -> v
              | _ -> failwith "Error: Address should be 32-bit integer"
             ) in (* I64_convert.extend_i32_u i in *)
           let offset = Int32.to_int offset in
           (* check if we satisfy CT  for the index *)

           let mems = get_mem_tripple frame in

           let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in

           
           
           (* if (c.ct_check) then ( *)
             
             let c = {c with observations =
                               CT_V_UNSAT((pcnum, pclet,pc), final_addr, mems, c.observations)} in

             if (c.ct_check) then (
               let index =  (Obj.magic e') in
               let memind, found =
                 try
                   VulnerabilitiesMap.find index !memindex_vuln, true 
                 with Not_found ->
                       let solv = Z3_solver.is_v_ct_unsat ~timeout:60 (pcnum, pclet, pc) final_addr mems in
                       if not solv then ( 
                         memindex_vuln := VulnerabilitiesMap.add index solv !memindex_vuln;
                       );
                       solv, false
               in

               

               if not memind && not found then
                 ConstantTime.warn e.at "Store: Constant-time violation";
             );
             (* [{c with code = vs', [] @ List.tl es;
              *          frame = frame;
              *          pc = pcnum, pclet, pc;
              *          progc = Obj.magic e'}] *)
             (* ) *)
             let msec = Smemory.get_secrets mem in
             let mpub = Smemory.get_public mem in
             (* print_endline "c.msecrets";
              * List.length msec |> string_of_int |> print_endline; *)
             let pc', pc'' = split_msec final_addr msec mpub (pcnum, pclet, pc) in
             (* print_endline "Store:";
              * svalue_to_string sv |> print_endline;
              * svalue_to_string final_addr |> print_endline; *)
             (* print_pc pc' |> print_endline; *)
             (* print_pc pc'' |> print_endline; *)

             let num = Instance.next_num() in
             let nv =
               (match sz with
                | None -> Eval_symbolic.eval_store ty final_addr sv
                            (smemlen frame.inst) num (Types.size ty)
                | Some (sz) ->
                   assert (packed_size sz <= Types.size ty);
                   let n = packed_size sz in
                   Eval_symbolic.eval_store ty final_addr sv
                     (smemlen frame.inst) num n
               )
             in

             (* let nv = Eval_symbolic.eval_store ty final_addr sv
              *            (smemlen frame.inst) 4 in *)
             let mem' = Smemory.store_sind_value num mem nv in
             let vs', es' = vs', [] in
             (* Update memory with a store *)
             let nframe = {frame with inst = insert_smemory frame.inst num mem'} in

             (* Path1: we store the value in secret memory *)
             let res =
               (* match Z3_solver.is_sat (pcnum, pclet, pc') mems, *)
               (* match Z3_solver.is_sat (pcnum, pclet, pc'') mems with
                * | true -> *)
               let pcnum'' = Pc_type.next_pc_num() in
               let pcnum' = Pc_type.next_pc_num() in
               let c =
                 {c with observations =
                           CT_V_UNSAT((pcnum'', pclet,pc''), sv, mems, c.observations)} in
               
               if (!Flags.explicit_leaks) then (
               
               let nonv, found =
                 if (c.ct_check) then (
                   let index =  (Obj.magic e') in
                   try VulnerabilitiesMap.find index !noninter_vuln, true 
                   with Not_found ->
                         let solv = Z3_solver.is_v_ct_unsat ~timeout:60 (pcnum'', pclet, pc'') sv mems in
                         if not solv then  
                           noninter_vuln := VulnerabilitiesMap.add index solv !noninter_vuln;
                         solv, false)
                 else true, false
               in

               (if nonv then
                  (match Z3_solver.is_sat (pcnum', pclet, pc') mems with
                   | true -> [{c with code = vs', es' @ List.tl es;
                                      frame = nframe;
                                      pc = pcnum', pclet, pc';
                                      progc = Obj.magic e'}]
                   | false -> [{c with code = vs', es' @ List.tl es;
                                       frame = nframe;
                                       pc = pcnum'', pclet, pc'';
                                       progc = Obj.magic e'}]
                  )
                else (
                  if not found then 
                    NonInterference.warn e.at "Trying to write high values in low memory"
                  else ();
                  [{c with code = vs', es' @ List.tl es;
                           frame = nframe;
                           pc = pcnum, pclet, pc;
                           progc = Obj.magic e'}]
                )
               )
            ) else (
                  [{c with code = vs', es' @ List.tl es;
                           frame = nframe;
                           pc = pcnum, pclet, pc;
                           progc = Obj.magic e'}]

                ) 
            
             (* | false ->
              *    (match Z3_solver.is_sat (pcnum, pclet, pc') mems with *)
             (* | true -> [{c with code = vs', es' @ List.tl es;
              *                    frame = nframe;
              *                    pc = pcnum, pclet, pc';
              *                    progc = Obj.magic e'}]
              * | false -> failwith "No possible path available" *)
                 (* ) *)
             in res
        (* ) *)
        (* else (
         *   let nv =
         *     (match sz with
         *      | None ->
         *         Eval_symbolic.eval_store ty final_addr sv
         *           (smemlen frame.inst) (Types.size ty)
         *      | Some (sz) ->
         *         assert (packed_size sz <= Types.size ty);
         *         let n = packed_size sz in
         *         Eval_symbolic.eval_store ty final_addr sv
         *           (smemlen frame.inst) n
         *     )
         *   in
         * 
         *   let mem' = Smemory.store_sind_value mem nv in
         *   let vs', es' = vs', [] in
         *   (\* Update memory with a store *\)
         *   let nframe = {frame with inst = insert_smemory frame.inst mem'} in
         * 
         *   [{c with code = vs', es' @ List.tl es;
         *            frame = nframe;
         *            progc = Obj.magic e'}]
         * ) *)
        (* | MemorySize, vs ->
         *   let mem = smemory frame.inst (0l @@ e.at) in
         *   let vs', es' = (Si32.of_int_s (Smemory.size mem)) :: vs, [] in
         *   [{c with code = vs', es' @ List.tl es} *)
              
        (* | MemoryGrow, I32 delta :: vs' ->
         *   let mem = memory frame.inst (0l @@ e.at) in
         *   let old_size = Memory.size mem in
         *   let result =
         *     try Memory.grow mem delta; old_size
         *     with Memory.SizeOverflow | Memory.SizeLimit | Memory.OutOfMemory -> -1l
         *   in I32 result :: vs', [] *)

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
           [{c with code = vs', es' @ List.tl es;
                    progc = Obj.magic e'}]
           
        (* | Const v, vs ->
         *    v.it :: vs, [] *)

        | Test testop, v :: vs' ->
           (* print_endline "testop"; *)
           let vs', es' =
             (try (svalue32_of_bool (Eval_symbolic.eval_testop testop v)) :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es;
                    progc = Obj.magic e'}]
           
        | Compare relop, v2 :: v1 :: vs' ->
           (* print_endline "relop"; *)
           let vs', es' =
             (try (svalue32_of_bool (Eval_symbolic.eval_relop relop v1 v2)) :: vs', []
              with exn ->
                vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es;
                    progc = Obj.magic e'}]
        | Unary unop, v :: vs' ->
           (* print_endline "unop"; *)
           let vs', es' = 
             (try Eval_symbolic.eval_unop unop v :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es;
                    progc = Obj.magic e'}]
        | Binary binop, v2 :: v1 :: vs' ->
           (* print_endline "binop"; *)
           let vs', es' = 
             (try
                let nv = Eval_symbolic.eval_binop binop v1 v2 in
                (* "Printing binop" |> print_endline; *)
                (* Pc_type.svalue_to_string nv |> print_endline; *)
                nv :: vs', []
              with exn ->
                vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es;
                    progc = Obj.magic e'}]
        | Convert cvtop, v :: vs' ->
           let vs', es' = 
             (try Eval_symbolic.eval_cvtop cvtop v :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
           in [{c with code = vs', es' @ List.tl es;
                       progc = Obj.magic e'}]
            
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
       print_endline "trapping";
       assert false

    | Assert (lvs, e, analyzed), vs ->
       if !Flags.debug then 
         print_endline ("Asserting invariant.. The loop is already analyzed:" ^ (string_of_bool analyzed));
       (* print_endline "assert"; *)
       if analyzed || assert_invar lvs c then (
         [] 
        (*[{c with code = vs, List.tl es}]*)
       )
       else (
         (* print_endline "Assertion failed"; *)
         (* [{c with code = vs, List.tl es}] *)
         failwith "Assertion failed"
       )
    | Havoc lvs, vs ->
       (* print_endline "havoc"; *)
       (* let havc = havoc_vars lvs c in
        * [{havc with code = vs, List.tl es}] *)
       failwith "Havoc: Not in use"
      
    | FirstPass  (n, es0, (vs', code')), vs ->
       (* print_endline "first pass"; *)
       (* Not used right now *)
       let vs', es' = vs, [Label (n, es0, (vs', code'),
                                  (pcnum, pclet, pc), c.induction_vars, true) @@ e.at] in
       [{c with code = vs', es' @ List.tl es}]

    | SecondPass  (n, [{it=Plain ((Loop (bt, es') ) as l); at=loc}], (vs''', code''')), vs ->
       (* print_endline "second pass"; *)
       (* print_endline "Printing induction variables";
        * print_endline (induction_vars_to_string c.induction_vars); *)

       (* let vv = local frame (18l @@ e.at) in
        * let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in
        * let is_low = Z3_solver.is_v_ct_unsat c.pc vv mem in
        * print_endline (string_of_bool is_low); *)
       let args, vs' = take n vs e.at, drop n vs e.at in
       let lvs, analyzed =
         let index = (Obj.magic l) in
         (*try (
           let lvs = ModifiedVarsMap.find index !modified_vars in
           let lvs' = find_policy lvs c in
           lvs', compare_policies lvs lvs'
         ) with Not_found -> ( *)
           let vs'', es'' = vs', [Label (n, [Plain l @@ loc],
                                        (args, code'''), (pcnum, pclet,pc),
                                        c.induction_vars, c.ct_check) @@ e.at] in
           
           (*let lvs, _ = find_modified_vars (Obj.magic l)*)
           let lvs = fv_eval (Obj.magic l)
                          {c with code = vs'', es''} in (* @ List.tl es;} in*)

           let lvs = merge_vars lvs in
           modified_vars := ModifiedVarsMap.add index lvs !modified_vars;
           lvs, false
         (* ) *)
       in
       if !Flags.debug then (
           print_endline ("Printing loopvars." ^ (string_of_int (Obj.magic l)));
           List.iter print_loopvar lvs
       );

       let stats = loop_stats es' loc in
       (* HAVOC *)
       let havc = havoc_vars lvs c stats in
        (* print_endline ("Number memories" ^ string_of_int (List.length havc.frame.inst.smemories));
                  let stores = Smemory.get_stores (List.hd havc.frame.inst.smemories) in
        List.iter (fun st -> print_endline (svalue_to_string st)) stores;
        *)


       if !Flags.elim_induction_variables then (
         let vs'', es'' = vs', [Label (n, [], (*Plain l @@ loc],*)
                                       (args, code'''), havc.pc,
                                       c.induction_vars, c.ct_check) @@ e.at] in
         let nhavc = {havc with code = vs'', es'' (*@ List.tl es;*)} in
         let nc = {c with code = vs'', es'' @ List.tl es;} in
         let iv, havc' = induction_vars nhavc nc lvs in

         (* print_endline "Printing induction vars.";
          * print_endline (triple_to_string iv);
          * ( match havc'.induction_vars with
          *   | None -> ()
          *   | Some ivs ->
          *      IndVarMap.iter (fun k iv -> print_endline (svalue_to_string k ^ " " ^ triple_to_string iv)) ivs
          * );
          * print_endline "Done printing."; *)

         (* print_endline "Starting NonCheckPass"; *) 

         (* let assrt = Assert (lvs, e') in *)
         let nc_pass = NonCheckPass (n, [Plain l @@ e.at],
                                     (args, code'''), iv, lvs, c) in
         (* let vs'', es'' = vs', [
          *       nc_pass @@ e.at; 
          *     ] in *)
         let vs', es' = vs', [Label (n, [nc_pass @@ e.at],
                                     (args, code'''),
                                     havc'.pc,
                                     havc'.induction_vars, false) @@ e.at ] in
         [{havc' with code = vs', es' @ List.tl es; progc = Obj.magic l}]

       ) else (
         let assrt = Assert (lvs, l, analyzed) in
         
         let vs'', es'' = vs', [Label (n, [assrt @@ e.at],
                                       (args, code'''), havc.pc,
                                       havc.induction_vars, c.ct_check) @@ e.at] in

         (* print_endline "Finish second pass"; *)
         let havc' = {havc with code = vs'', es'' @ List.tl es;} in
         [{havc' with code = vs'', es'' @ List.tl es; progc = Obj.magic l}]
       )

    | SecondPass  (n, _, (vs''', code''')), vs ->
       Crash.error e.at "Unexpected SecondPass without loop"


    | NonCheckPass  (n, [{it=Plain ((Loop _) as l); at=loc}],
                     (vs''', code'''), iv, lvs, c_old), vs ->

       (* print_endline "Done NonCheckPass"; *) 
       (* TODO(Romy): estimation of loop size *)
       (* estimating loop size *)
       if !Flags.estimate_loop_size then (
         let maxl = get_maximum_loop_size iv c in
         match maxl with
         | Some ml when ml < magic_number_loop_inv -> (
           if !Flags.debug then print_endline ("MaxL: " ^ (string_of_int ml));
          let {frame; code = vs, es; pc = pcnum, pclet, pc; _} = c_old in
           let args, vs' = take n vs e.at, drop n vs e.at in
           let vs'', es'' = vs', [Label (n, [Plain l @@ e.at],
                                           (args, code'''), (pcnum, pclet,pc),
                                           c_old.induction_vars, c_old.ct_check) @@ e.at]
           in
           (* print_endline (string_of_int (Obj.magic l)); *)
           update_maxloop (Obj.magic l) ml;
           [{c_old with code = vs'', es'' @ List.tl es; progc = Obj.magic l}]
         )
         | _ -> ( 
           if !Flags.debug then print_endline ("No MaxL");
           let args, vs' = take n vs e.at, drop n vs e.at in
           let assrt = Assert (lvs, l, false) in
           let vs'', es'' = vs', [Label (n, [assrt @@ e.at],
                                         (args, code'''),
                                         (pcnum, pclet, pc),
                                         c.induction_vars, true) @@ e.at ] in
           [{c with code = vs'', es'' @ List.tl es; progc = Obj.magic l}]

         )
       (* let _, v, _, _ = iv in
          * let mem = (frame.inst.smemories, smemlen frame.inst) in
          * (\* let maxl = Z3_solver.is_v_ct_unsat (pcnum, pclet, pc) v mem in *\)
          * let maxl = Z3_solver.optimize Z3_solver.max (pcnum, pclet, pc) mem v in
          * (match maxl with
          *    Some v -> print_endline ("Maxl: " ^ (string_of_int v))
          *  | None -> print_endline ("No value")); *)
       ) else (
       (* print_endline (string_of_bool maxl); *)
         (* print_endline "Check pass: Putting assert in the queue"; *)
         let args, vs' = take n vs e.at, drop n vs e.at in
         let assrt = Assert (lvs, l, false) in
         let vs'', es'' = vs', [Label (n, [assrt @@ e.at],
                                       (args, code'''),
                                       (pcnum, pclet, pc),
                                       c.induction_vars, true) @@ e.at ] in
         [{c with code = vs'', es'' @ List.tl es; progc = Obj.magic l}]
       )
    | NonCheckPass  (n, _, (vs''', code'''), _,  _, _), vs ->
       Crash.error e.at "Unexpected NonCheckPass without loop"

    | Returning vs', vs ->
       Crash.error e.at "undefined frame"

    | Breaking (k, vs'), vs ->
       Crash.error e.at "undefined label"

    | Label (n, es0, (vs', []), pc', iv', cct), vs ->
       (* print_endline ("lab:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs' @ vs, [] in
       [{c with code = vs', es' @ List.tl es;}]
       
    | Label (n, es0, (vs', {it = Trapping msg; at} :: es'), pc', iv', cct'), vs ->
       (* print_endline "lab2"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Returning vs0; at} :: es'), pc', iv', cct'), vs ->
       (* print_endline ("lab3:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs, [Returning vs0 @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (0l, vs0); at} :: es'), pc', iv', cct'), vs ->
       (* print_endline ("lab4:" ^ (string_of_int c.counter)); *)
       let vs', es' = take n vs0 e.at @ vs, es0 in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (k, vs0); at} :: es'), pc', iv', cct'), vs ->
       (* print_endline ("lab5:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs, [Breaking (Int32.sub k 1l, vs0) @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, code', pc', iv', cct'), vs ->
       (* print_endline ("lab6:" ^ (string_of_int c.counter)); *)
       (*TODO(Romy): not sure if correct to change the pc *)
       let c' = step {c with code = code';
                             pc = pc';
                             induction_vars = iv';
                             counter = c.counter + 1;
                             ct_check = cct'
                  } in
       List.map (fun ci ->
           {c with code = vs,
                          [Label (n, es0, ci.code, ci.pc,
                                  ci.induction_vars,
                                  ci.ct_check) @@ e.at]
                          @ List.tl es;
                   pc = ci.pc; (*  *)
                   observations = ci.observations;
                   induction_vars = ci.induction_vars;
                   frame = ci.frame
         }) c'

    | Frame (n, frame', (vs', []), pc', iv'), vs ->
       (* print_endline ("frame1:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs' @ vs, [] in
       [{c with code = vs', es' @ List.tl es;
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
       }]

    | Frame (n, frame', (vs', {it = Trapping msg; at} :: es'), _, _), vs ->
       (* print_endline "frame trappping"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Frame (n, frame', (vs', {it = Returning vs0; at} :: es'), pc', iv'), vs ->
       (* print_endline "frame returning"; *)
       (* print_endline ("frame3:" ^ (string_of_int c.counter)); *)
       let vs', es' = take n vs0 e.at @ vs, [] in
       [{c with code = vs', es' @ List.tl es;
                frame = {frame
                        with inst = {frame.inst
                                    with smemories = frame'.inst.smemories;
                                         smemlen = frame'.inst.smemlen;
                                         smemnum = frame'.inst.smemnum;
                                         sglobals = frame'.inst.sglobals
                                    }
                        };
                pc = pc';
                induction_vars = iv'}]

    | Frame (n, frame', code', pc', iv'), vs ->
       (* print_endline "frame normal"; *)
       (* print_endline ("frame4:" ^ (string_of_int c.counter)); *)

       let c' = step {c with frame = frame'; code = code';
                             budget = c.budget - 1; pc = pc';
                             counter = c.counter + 1} in
       (* print_endline ("frame4_end:" ^ (string_of_int c.counter)); *)
       (* TODO(Romy): the pc etc  should probably not be here *)
       List.map (fun ci ->
           {c with code = vs, [Frame (n, ci.frame,
                                      ci.code,
                                      ci.pc,
                                      ci.induction_vars) @@ e.at] @ List.tl es;
                   (* pc = ci.pc; *)
                   observations = ci.observations;
                   induction_vars = iv'
                   (* frame = ci.frame *)
           }
         ) c'

    | Invoke func, vs when c.budget = 0 ->
       Exhaustion.error e.at "call stack exhausted"

    | Invoke func, vs ->
       (* print_endline "invoke"; *)
       (* print_endline ("inv:" ^ (string_of_int c.counter)); *)
       let FuncType (ins, out) = func_type_of func in
       let n1, n2 = Lib.List32.length ins, Lib.List32.length out in
       let args, vs' = take n1 vs e.at, drop n1 vs e.at in
       (match func with
        | Func.AstFunc (t, inst', f) ->
           let rest = List.map value_to_svalue_type f.it.locals in

           
           let locals' = List.rev args @ List.map Svalues.default_value rest in
           let locals_map,_ = List.fold_left
                                (fun (m,i) l -> (LocalVarsMap.add i l m, i+1))
                                (LocalVarsMap.empty,0) locals' in 
           (* TODO(Romy): check if this is correct - 
              using current memory instead of old *)
           let nsmem = if (List.length frame.inst.smemories == 0) then !inst'.smemories
                       else frame.inst.smemories
           in
           let sglobals =  if (List.length frame.inst.sglobals == 0) then !inst'.sglobals
                           else frame.inst.sglobals in
           let nmemlen = List.length nsmem in
           let inst' = {!inst' with smemories = nsmem;
                                    smemlen =  nmemlen;
                                    sglobals = sglobals;
                       } in

           let frame' = {inst = inst'; locals = locals_map} in
           let instr' = [Label (n2, [], ([], List.map plain f.it.body),
                                c.pc, c.induction_vars, c.ct_check) @@ f.at] in 
           let vs', es' = vs', [Frame (n2, frame', ([], instr'), c.pc, c.induction_vars) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]

        (* | Func.HostFunc (t, f) ->
         *   (try List.rev (f (List.rev args)) @ vs', []
         *   with Crash (_, msg) -> Crash.error e.at msg) *)
        | _ -> Crash.error e.at "Func.Hostfunc not implemented yet."
       )
  in
  (* print_endline "end of step"; *)
  (* List.length res |> string_of_int |> print_endline;
   * List.iter (fun c -> Pc_type.print_pc c.pc |> print_endline;) res; *)
  res

(* Eval BFS *)
let filter_step (c: config) : config list option =
  match c.code with
  | vs, [] -> None
  | vs, {it = Trapping msg; at } :: _ ->
     Trap.error at msg
  | vs, es ->
     let st = step {c with counter = c.counter + 1} in
     Some st

let filter_done (c: config) : pc_ext option = 
  match c.code with
  | vs, [] ->
     (* "Printing pc" |> print_endline;
      * print_pc c.pc |> print_endline; *)
     Some c.pc
  | vs, {it = Trapping msg; at } :: _ ->
     Trap.error at msg
  | vs, es -> None


(* let filter_map (a' -> b' option) -> a' list -> b' list *)
let filter_map f cs =
  let rec filter_map_i f cs acc =
        match cs with
        | c::cs' ->
           (match f c with
            | Some v -> filter_map_i f cs' (v::acc)
            | None -> filter_map_i f cs' acc
           )
        | [] -> acc
  in
  filter_map_i f cs [] |> List.rev
     
let rec eval_bfs (cs : config list) : pc_ext list =
  (* print_endline "BFS"; *)
  let spaths = filter_map filter_done cs in
  let css = filter_map filter_step cs in
  spaths @ (List.fold_left (@) [] css |> eval_bfs)

        
     
(* Eval DFS *)
let eval_dfs (cs : config list) : pc_ext list =
  let rec eval_dfs_i (cs : config list) (acc : pc_ext list) (num_paths : int) :
        pc_ext list * int =
    (* print_endline "eval_dfs_i"; *)
    match cs with
    | c::cs' ->
       (match c.code with
        | vs, [] -> eval_dfs_i cs' (c.pc::acc) num_paths
        | vs, {it = Trapping msg; at} :: _ -> Trap.error at msg
        | vs, es -> (
           let ncs = step {c with counter = c.counter + 1} in
           let num_paths' = num_paths * (List.length ncs) in
           eval_dfs_i (ncs @ cs') acc num_paths'
        )
       )
    | [] -> List.rev acc, num_paths
  in
  let pcs, num_paths = eval_dfs_i cs [] 1 in
  if !Flags.debug || !Flags.stats then
    print_endline ("Number of paths" ^ (string_of_int num_paths));
  pcs


let merge_globals c1 c2 =
  let newglobals =
    List.map2
      (fun g1 g2 ->
        let g1' = Sglobal.load g1 in
        let g2' = Sglobal.load g2 in
        match g1', g2' with
        | g1', g2' when g1' = g2' -> g1
        | g1', g2' ->
           let mem1 = (c1.frame.inst.smemories, smemlen c1.frame.inst, smemnum c1.frame.inst) in
           let mem2 = (c2.frame.inst.smemories, smemlen c2.frame.inst, smemnum c2.frame.inst) in
           let is_low1 = Z3_solver.is_v_ct_unsat ~timeout:30 c1.pc g1' mem1 in
           let is_low2 = Z3_solver.is_v_ct_unsat ~timeout:30 c2.pc g2' mem2 in
           let newg' =
             (match is_low1,is_low2 with
                true,true ->
                (match g1', g2' with
                   SI32 _, SI32 _ -> SI32 (Si32.of_low ())
                 | SI64 _, SI64 _ -> SI64 (Si64.of_low ())
                 | _, _ -> failwith "Float number not supported.";
                )
              | _, _ ->
                (match g1', g2' with
                   SI32 _, SI32 _ -> SI32 (Si32.of_high ())
                 | SI64 _, SI64 _ -> SI64 (Si64.of_high ())
                 | _, _ -> failwith "Float number not supported.";
                )
             )
           in
           let g = Sglobal.store g1 newg' in 
           g
      )
      c1.frame.inst.sglobals c2.frame.inst.sglobals in
  { c1 with frame = {c1.frame with inst = {c1.frame.inst with sglobals = newglobals}}}


let merge_memories c1 c2 =
  (* let rec reduce_stores st1 acc =
   *   match st1 with
   *   | [] -> acc
   *   | (SI32 (Smt_type.Store (ad, v, i, sz)) as sth)::st -> reduce_stores st (sth::acc) 
   *   | (SI64 (Smt_type.Store (ad, v, i, sz)) as sth)::st -> reduce_stores st (sth::acc)
   *   | _ -> failwith "Should not happen: wrong type of store."
   * in *)
  let rec merge_stores st1 st2 acc =
    match st1, st2 with
    | s1::st1, s2::st2 when s1 = s2 -> merge_stores st1 st2 (s1::acc)
    | s1::st1, s2::st2 ->
       let mem1 = get_mem_tripple c1.frame in
       let mem2 = get_mem_tripple c2.frame in
       let is_low1 = Z3_solver.is_v_ct_unsat ~timeout:30 c1.pc s1 mem1 in
       let is_low2 = Z3_solver.is_v_ct_unsat ~timeout:30 c2.pc s2 mem2 in
       let news =
         (match is_low1,is_low2 with
            true,true ->
             (match s1, s2 with
                SI32 _, SI32 _ -> SI32 (Si32.of_low ())
              | SI64 _, SI64 _ -> SI64 (Si64.of_low ())
              | _, _ -> failwith "Float number not supported.";
             )
          | _, _ ->
             (match s1, s2 with
                SI32 _, SI32 _ -> SI32 (Si32.of_high ())
              | SI64 _, SI64 _ -> SI64 (Si64.of_high ())
              | _, _ -> failwith "Float number not supported.";
             )
         )
       in
       merge_stores st1 st2 (news::acc)
    | [], [] -> acc
    | s1::st1, [] ->
       (* let mem1 = get_mem_tripple c1.frame in
        * let is_low1 = Z3_solver.is_v_ct_unsat ~timeout:30 c1.pc s1 mem1 in *)
       let news =
         (match s1 with
            SI32 _ -> SI32 (Si32.of_high ())
                        (* if is_low1 then SI32 (Si32.of_low ())
                       * else SI32 (Si32.of_high ()) *)
          | SI64 _ -> SI64 (Si64.of_high())
                        (* if is_low1 then SI64 (Si64.of_low ())
                       * else SI64 (Si64.of_high ()) *)
          | _ -> failwith "Float numbers not supported.";
         )
       in
       merge_stores st1 st2 (news::acc)
    | [], s2::st2 ->
       (* let mem2 = get_mem_tripple c2.frame in
        * let is_low2 = Z3_solver.is_v_ct_unsat ~timeout:30 c2.pc s2 mem2 in *)
       let news =
         (match s2 with
            SI32 _ -> SI32 (Si32.of_low ())
                        (* if is_low2 then SI32 (Si32.of_low ())
                       * else SI32 (Si32.of_high ()) *)
          | SI64 _ -> SI64 (Si32.of_high ())
                        (* if is_low2 then SI64 (Si64.of_low ())
                       * else SI64 (Si64.of_high ()) *)
          | _ -> failwith "Float numbers not supported."
         )
       in
       merge_stores st1 st2 (news::acc)       
  in
  let rec merge_mems m1s m2s acc =
    match m1s, m2s with
    | [], [] -> acc
    | m1::m1s', m2::m2s' ->
       let st1 = List.rev (Smemory.get_stores m1) in
       let st2 = List.rev (Smemory.get_stores m2) in
       (* let st1 = List.rev st1 in
        * let st2 = List.rev st2 in *)
       let newstores = merge_stores st1 st2 [] in
       let newm = Smemory.replace_stores m1 newstores in
       merge_mems m1s' m2s' (newm::acc)
    | ms', []
      | [], ms' -> 
       (List.rev ms') @ acc
  in
  let m1 = c1.frame.inst.smemories in
  let m2 = c2.frame.inst.smemories in
  let newsmemories = merge_mems m1 m2 [] in
  { c1 with frame =
              {c1.frame with inst =
                               {c1.frame.inst with smemories = newsmemories}}}  
  
let merge_locals c1 c2 =
  let loc1 = List.map snd (LocalVarsMap.bindings c1.frame.locals) in
  let loc2 = List.map snd (LocalVarsMap.bindings c2.frame.locals) in 
  let newlocals =
    List.map2
      (fun l1 l2 ->
        let l1' = l1 in
        let l2' = l2 in
        match l1', l2' with
        | l1', l2' when l1' = l2' -> l1
        | l1', l2' ->
           let mem1 = get_mem_tripple c1.frame in
           let mem2 = get_mem_tripple c2.frame in
           let is_low1 = Z3_solver.is_v_ct_unsat ~timeout:30 c1.pc l1' mem1 in
           let is_low2 = Z3_solver.is_v_ct_unsat ~timeout:30 c2.pc l2' mem2 in
           let newl' =
             (match is_low1,is_low2 with
                true,true ->
                (match l1', l2' with
                   SI32 _, SI32 _ -> SI32 (Si32.of_low ())
                 | SI64 _, SI64 _ -> SI64 (Si64.of_low ())
                 | _, _ -> failwith "Float number not supported.";
                )
              | _, _ ->
                (match l1', l2' with
                   SI32 _, SI32 _ -> SI32 (Si32.of_high ())
                 | SI64 _, SI64 _ -> SI64 (Si64.of_high ())
                 | _, _ -> failwith "Float number not supported.";
                )
             )
           in
           newl'
      )
      loc1 loc2 in
  let newlocals_map,_ = List.fold_left
                        (fun (m,i) l -> (LocalVarsMap.add i l m, i+1))
                        (LocalVarsMap.empty,0) newlocals in 

  { c1 with frame = {c1.frame with locals = newlocals_map}}

let merge_pcs c1 c2 =
  let pc1 = c1.pc in
  let pc2 = c2.pc in
  let pc' = Pc_type.merge_pcs pc1 pc2 in
  { c1 with pc = pc' }
  
let merge_two_states c1 c2 =
  let c = merge_globals c1 c2 in
  let c = merge_locals c c2 in (* a bit hacky: c is a copy of c1 *)
  let c = merge_memories c c2 in
  let c = merge_pcs c c2 in
  c
  
let rec merge_states cs =
  match cs with
  | [] -> failwith "Unexpected: no states to merge"
  | c::[] -> c
  | c1::c2::cs' -> merge_states (merge_two_states c1 c2::cs')


(* TODO(Romy) *)
let rec eval_pfs (cs : config list) : pc_ext list =
  (* print_endline "BFS"; *)
  if !Flags.debug then
    print_endline "eval_PFS.";

  List.iter add_locmap cs;

  let cr = next_locmap () in
  match cr with
    None -> []
  | Some (loc, cs) ->
     if !Flags.debug then
       print_endline ("loc:" ^ loc);
     ( match cs with
       | [] -> []
       | cs' ->
          if !Flags.debug then
            print_endline ("Config size:"  ^ (string_of_int (List.length cs')));

          if List.length cs' > magic_number_of_states then (
            if !Flags.debug then
              print_endline ("Merging states."  ^ (string_of_int (List.length cs')));
            
            let c = merge_states cs' in
            let c' = step {c with counter = c.counter + 1} in
            remove_locmap loc;
            eval_pfs c'
          )
          else (
            let ncs = List.fold_left
                        (fun ac c ->
                          let res = step {c with counter = c.counter + 1} in
                          res @ ac ) [] cs'  in
            remove_locmap loc;
          if !Flags.debug then
            print_endline ("Step config size:"  ^ (string_of_int (List.length ncs)));

            (* let ncs = step {c with counter = c.counter + 1} in *)
            eval_pfs ncs
          )
     )

                 
(********************** MERGE STATES - Not done ******************************)
(* module MPMap = Map.Make(struct
 *                    type t = int
 *                    let compare = compare
 *                  end)
 * 
 * let mp = ref MPMap.empty
 * 
 * let merge_states c cs =
 *   let merge_state c c' =
 *     (* Compare PC *)
 *     (* Compare Locals/Globals/Mem *)
 *     None
 *   in
 *   let rec merge_states_i c cs acc =
 *     match cs with
 *     | [] -> c::acc
 *     | c'::cs' ->
 *        match merge_state c c' with
 *        | None -> merge_states_i c cs' (c'::acc)
 *        | Some c -> c::acc @ cs'
 *   in
 *   merge_states_i c cs []
 * 
 * 
 *         
 * (* Eval Merge States *)
 * let eval_mp (cs : config list) : pc_ext list =
 *   let rec eval_mp_i acc =
 *     (* print_endline "eval_dfs_i"; *)
 *     let k, cs = MPMap.find_first (fun k -> true) !mp in
 *     match cs with
 *     | c::cs' ->
 *        (* add back the rest *)
 *        mp :=  MPMap.add k cs' !mp;
 *        (match c.code with
 *         | vs, [] -> eval_mp_i (c.pc::acc)
 *         | vs, {it = Trapping msg; at} :: _ -> Trap.error at msg
 *         | vs, es -> (
 *           let ncs = step {c with counter = c.counter + 1} in
 *           mp := List.fold_left (fun mp c ->
 *                     let old_s =
 *                       ( try MPMap.find c.progc mp
 *                         with Not_found -> []
 *                       ) in
 *                     MPMap.add c.progc (c::old_s) mp) !mp  ncs; 
 *           eval_mp_i acc
 *         )
 *        )      
 *     | [] -> acc
 *   in
 *   mp := List.fold_left (fun mp c ->
 *             let old_s =
 *               ( try MPMap.find c.progc mp
 *                 with Not_found -> []
 *               ) in
 *             MPMap.add c.progc (c::old_s) mp) !mp  cs; 
 *   eval_mp_i [] *)

let eval (c : config) : pc_ext list =
  if !Flags.bfs then
    eval_bfs [c]
  else if !Flags.pfs then
    eval_pfs [c]
  else 
    eval_dfs [c] (* {cs = [c]; loops = []} *)

(* Functions & Constants *)

let invoke (func : func_inst) (vs : svalue list) : pc_ext list =
  let at = match func with Func.AstFunc (_,_, f) -> f.at | _ -> no_region in
  (* let FuncType (ins, out) = Func.type_of func in
   * if List.map Svalues.type_of vs <> ins then
   *   Crash.error at "wrong number or types of arguments"; *)
  let c = config empty_module_inst (List.rev vs) [Invoke func @@ at] in
  try List.rev (eval c) with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"

(* Todo(Romy): fix the check *)
let symb_invoke (func : func_inst) (vs : svalue list) : pc_ext list =
  let at = match func with Func.AstFunc (_,_, f) -> f.at | _ -> no_region in
  (* let FuncType (ins, out) = Func.type_of func in
   * if List.map Svalues.type_of vs <> ins then
   *   Crash.error at "wrong number or types of arguments"; *)
  let c = config empty_module_inst (List.rev vs) [Invoke func @@ at] in
  try List.rev (eval c) with Stack_overflow ->
    Exhaustion.error at "call stack exhausted"

                             
(*TODO(Romy): Check this one *)
let eval_const (inst : module_inst) (const : const) : svalue =
  (* let c = config inst [] (List.map plain const.it) in *) 
  match const.it with
  | [v] ->
     (match v.it with
      | Const v -> value_to_svalue v.it
      | GlobalGet x -> Sglobal.load (sglobal inst x)
      | _ -> Crash.error const.at "Evaluation on constants not fully implemented, yet."
     )
  | _ -> Crash.error const.at "wrong number of results on stack"

(* let c = config inst [] (List.map plain const.it) in *)
  (* match eval c with
   * | [v] -> v
   * | vs -> Crash.error const.at "wrong number of results on stack" *)


let i32 (v : svalue) at =
  match v with
  | SI32 i -> Int32.of_int (Si32.to_int_s i)
  | _ -> Crash.error at "type error: i32 value expected"


(* Modules *)

let create_func (inst : module_inst) (f : func) : func_inst =
  Func.alloc (type_ inst f.it.ftype) (ref inst) f

let create_table (inst : module_inst) (tab : table) : table_inst =
  let {ttype} = tab.it in
  Table.alloc ttype

let create_memory (inst : module_inst) (mem : memory) : memory_inst =
  let {mtype} = mem.it in
  Memory.alloc mtype

let create_smemory (inst : module_inst) (mem : smemory) : smemory_inst =
  let {smtype} = mem.it in
  Smemory.alloc smtype


let create_sglobal (inst : module_inst) (glob : global) : sglobal_inst =
  let {gtype; value} = glob.it in
  let sgtype = global_to_sglobal_type gtype in
  let v = eval_const inst value in
  Sglobal.alloc sgtype v

(* let create_global (inst : module_inst) (glob : global) : global_inst =
 *   let {gtype; value} = glob.it in
 *   let v = eval_const inst value in
 *   Global.alloc gtype v *)

let create_export (inst : module_inst) (ex : export) : export_inst =
  let {name; edesc} = ex.it in
  let ext =
    match edesc.it with
    | FuncExport x -> ExternFunc (func inst x)
    | TableExport x -> ExternTable (table inst x)
    | MemoryExport x -> ExternMemory (memory inst x)
    | SmemoryExport x -> ExternSmemory (smemory inst x)
    | GlobalExport x -> ExternSglobal (sglobal inst x)
  in name, ext


let init_func (inst : module_inst) (func : func_inst) =
  match func with
  | Func.AstFunc (_, inst_ref, _) -> inst_ref := inst
  | _ -> assert false

let init_table (inst : module_inst) (seg : table_segment) =
  let {index; offset = const; init} = seg.it in
  let tab = table inst index in
  let offset = i32 (eval_const inst const) const.at in
  let end_ = Int32.(add offset (of_int (List.length init))) in
  let bound = Table.size tab in
  if I32.lt_u bound end_ || I32.lt_u end_ offset then
    Link.error seg.at "elements segment does not fit table";
  fun () ->
    Table.blit tab offset (List.map (fun x -> FuncElem (func inst x)) init)

let init_memory (inst : module_inst) (seg : memory_segment) =
  let {index; offset = const; init} = seg.it in
  let mem = memory inst index in
  let offset' = i32 (eval_const inst const) const.at in
  let offset = I64_convert.extend_i32_u offset' in
  let end_ = Int64.(add offset (of_int (String.length init))) in
  let bound = Memory.bound mem in
  if I64.lt_u bound end_ || I64.lt_u end_ offset then
    Link.error seg.at "data segment does not fit memory";
  fun () -> Memory.store_bytes mem offset init

let init_smemory (secret : bool) (inst : module_inst) (sec : security) = 
  let {index; range = (const_lo,const_hi); value} = sec.it in
  let smem = smemory inst index in
  let lo = i32 (eval_const inst const_lo) const_lo.at in
  let hi = i32 (eval_const inst const_hi) const_hi.at in
  let lo,hi = Int32.to_int lo, Int32.to_int hi in
  let hi_list = List.init (hi-lo+1) (fun x-> x + lo) in
  let stores =
    match secret, value with
    | true, _ -> List.map (Eval_symbolic.create_new_hstore 1) hi_list
    | false, None -> List.map (Eval_symbolic.create_new_lstore 1) hi_list
    | false, Some v ->
       let ev = i32 (eval_const inst v) v.at in
       List.map (Eval_symbolic.create_new_value 1 (Int32.to_int ev)) hi_list
  in
  let smem =
    match secret with
    | true -> Smemory.add_secret smem (lo,hi)
    | false -> Smemory.add_public smem (lo,hi)
  in

  let mem = List.fold_left (Smemory.store_init_value 0) 
              smem stores in  
  update_smemory inst mem  (0l @@ sec.at)

let init_smemory_data (inst : module_inst) (seg : memory_segment) = 
  let store_bytes a bs =
    let list = List.init (String.length bs) (fun x -> x) in
    (* print_endline "init_smemory_data";
     * print_endline (string_of_int (Char.code bs.[0]));
     * print_endline (string_of_int (Char.code bs.[1]));
     * print_endline (string_of_int a); *)
    List.map (fun i ->
        Eval_symbolic.create_new_constant_store 1 (a + i) (Char.code bs.[i])) list
  in
  let {index; offset = const; init} = seg.it in
  let smem = smemory inst index in
  let offset = i32 (eval_const inst const) const.at in
  (* let end_ = Int32.(add offset (of_int (String.length init))) in *)
  let stores = store_bytes (Int32.to_int offset) init in
  let mem = List.fold_left (Smemory.store_init_value 0)
              smem stores in  
  update_smemory inst mem  (0l @@ seg.at)



let add_import (m : module_) (ext : extern) (im : import) (inst : module_inst)
    : module_inst =
  if not (match_extern_type (extern_type_of ext) (import_type m im)) then
    Link.error im.at "incompatible import type";
  match ext with
  | ExternFunc func -> {inst with funcs = func :: inst.funcs}
  | ExternTable tab -> {inst with tables = tab :: inst.tables}
  | ExternMemory mem -> {inst with memories = mem :: inst.memories}
  | ExternSmemory smem -> {inst with smemories = smem :: inst.smemories;
                                     smemlen = 1 + inst.smemlen;
                                     smemnum = Instance.next_num()}
  | ExternGlobal glob -> {inst with globals = glob :: inst.globals}
  | ExternSglobal glob -> {inst with sglobals = glob :: inst.sglobals}

let init (m : module_) (exts : extern list) : module_inst =
  empty_maxloop ();
  let
    { imports; tables; memories; smemories; globals; funcs; types;
      exports; elems; data; start; secrets; public
    } = m.it
  in

  if List.length exts <> List.length imports then
    Link.error m.at "wrong number of imports provided for initialisation";
  let inst0 =
    { (List.fold_right2 (add_import m) exts imports empty_module_inst) with
      types = List.map (fun type_ -> type_.it) types }
  in


  let fs = List.map (create_func inst0) funcs in
  let inst1 =
    { inst0 with
      funcs = inst0.funcs @ fs;
      tables = inst0.tables @ List.map (create_table inst0) tables;
      memories = inst0.memories @ List.map (create_memory inst0) memories;
      smemories = inst0.smemories @ List.map (create_smemory inst0) smemories;
      smemlen = List.length  (inst0.smemories) + List.length(smemories);
      smemnum = Instance.next_num();
      globals = inst0.globals; (* @ List.map (create_global inst0) globals; *)
      sglobals = inst0.sglobals @ List.map (create_sglobal inst0) globals;
      (* msecrets = inst0.msecrets @ List.map (create_secrets inst0) secrets; *)
                  (* @ List.map (create_global inst0) globals; *)
    }
  in

  let inst1 = List.fold_left (init_smemory true) inst1 secrets in
  let inst1 = List.fold_left (init_smemory false) inst1 public in
  let inst1 = List.fold_left init_smemory_data inst1 data in

  let inst = {inst1 with exports = List.map (create_export inst1) exports} in

  List.iter (init_func inst) fs;
  
  let init_elems = List.map (init_table inst) elems in
  let init_datas = List.map (init_memory inst) data in

  List.iter (fun f -> f ()) init_elems;
  List.iter (fun f -> f ()) init_datas;
  Lib.Option.app (fun x -> ignore (invoke (func inst x) [])) start;

  Random.init 1234;

  inst
