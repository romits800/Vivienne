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

let simplify_v frame pc v =
  if svalue_depth v 5 then (
    let mem = (frame.inst.smemories, smemlen frame.inst) in
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
                              let compare = compare
                            end)
let modified_vars = ref ModifiedVarsMap.empty 
                       
module AnalyzedLoopsMap = Map.Make(struct
                              type t = int
                              let compare = compare
                            end)
                        
let analyzed_loops = ref AnalyzedLoopsMap.empty 



module VulnerabilitiesMap = Map.Make(struct
                                type t = int
                                let compare = compare
                              end)
(* Vulnerability types *)
                        
let cond_vuln = ref VulnerabilitiesMap.empty
let noninter_vuln = ref VulnerabilitiesMap.empty
let memindex_vuln = ref VulnerabilitiesMap.empty 

                   
  


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
  let {frame; code = vs, es; pc = pclet, pc; _} = c in
  let e = List.hd es in
  (* print_pc pc |> print_endline; *)
  let vs, (pclet,pc) = 
      match vs with
      | v::vs' ->
         if svalue_depth v 5 then (
           if (!Flags.simplify) then (
             let v, pc' = simplify_v frame (pclet,pc) v in
             v::vs', pc'
           ) else (
             let nl, pc' = add_let (pclet, pc) (Sv v) in
             (* print_endline (string_of_int nl);
              * print_endline (svalue_to_string v); *)
             let nv = svalue_newlet (Sv v) nl in
             nv::vs', pc'
           )
         ) else (
           vs, (pclet,pc)
         )
      | [] -> vs, (pclet,pc)
  in
  (* let pclet,pc = simplify_pc frame (pclet,pc) in *)
  let c = {c with pc = (pclet,pc)} in
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
           let vs', es' = vs, [] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'};]
        | Block (bt, es'), vs ->
           (* print_endline "block"; *)
           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let n2 = Lib.List32.length ts2 in
           let args, vs' = take n1 vs e.at, drop n1 vs e.at in
           let vs', es' = vs', [Label (n2, [], (args, List.map plain es'),
                                       (pclet,pc), c.induction_vars, c.ct_check) @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
        | Loop (bt, es'), vs ->
           if !Flags.debug then 
             print_endline "Entering loop..";
           (* print_endline ("loop: " ^ (Source.string_of_region e.at)); *)
           if !Flags.loop_invar then 
             (
               (* Check if we have already analyzed the loop - have to
                  check if the whole  context is the same *)
               (* try (
                *   let lvs = AnalyzedLoopsMap.find (Obj.magic e') !analyzed_loops in
                *   (\* Droping the input arguments from the value stack *\)
                *   let FuncType (ts1, ts2) = block_type frame.inst bt in
                *   let n1 = Lib.List32.length ts1 in
                *   let vs' = drop n1 vs e.at in
                *   (\* TODO(Romy): Add values to the value stack *\)
                *   let c' = {c with code = vs', List.tl es;} in
                *   let havc = havoc_vars lvs c' in
                *   [havc]
                * )
                * with Not_found -> ( *)
                 let FuncType (ts1, ts2) = block_type frame.inst bt in
                 let n1 = Lib.List32.length ts1 in
                 let args, vs' = take n1 vs e.at, drop n1 vs e.at in

                 (* Normal loop *)
                 (* let vs', es' = vs', [Label (n1, [e' @@ e.at],
                  *                             (args, List.map plain es'), (pclet,pc),
                  *                             c.induction_vars, c.ct_check) @@ e.at] in *)

                 if !Flags.unroll_one then (
                   
                   let second_pass = SecondPass (n1, [Plain e' @@ e.at], (args, List.map plain es')) in

                   let vs'', es'' = vs', [Label (n1, [second_pass @@ e.at],
                                                 (args, List.map plain es'), (pclet,pc),
                                                 c.induction_vars, c.ct_check) @@ e.at] in

                   [{c with code = vs'', es'' @ List.tl es; progc = Obj.magic e'}]

                 ) else (
                 
                   let vs'', es'' = vs', [Label (n1, [Plain e' @@ e.at],
                                                 (args, List.map plain es'), (pclet,pc),
                                                 c.induction_vars, c.ct_check) @@ e.at] in

                   if !Flags.debug then 
                     print_endline "Finding variables modified in loop..";

                   (* print_endline "Finding vars"; *)
                   let lvs, _ = find_modified_vars (Obj.magic e)
                                  {c with code = vs'', es'' @ List.tl es;} in
                   (* print_endline "loop modified variables:";
                    * print_endline (string_of_int (List.length lvs));
                    * List.iter print_loopvar lvs; *)

                   (* print_endline "Merging vars"; *)
                   let lvs = merge_vars lvs in
                   
                   (* print_endline "loop modified variables:"; *)
                   (* print_endline (string_of_int (List.length lvs)); *)
                   (* List.iter print_loopvar lvs; *)
                   
                   (* HAVOC *)
                   let havc = havoc_vars lvs c in
                   let vs'', es'' = vs', [Label (n1, [Plain e' @@ e.at],
                                                 (args, List.map plain es'), (pclet,pc),
                                                 c.induction_vars, c.ct_check) @@ e.at] in
                   
                   let nhavc = {havc with code = vs'', es'' @ List.tl es;} in
                 
                   let havc' =
                     if !Flags.elim_induction_variables then
                       let nc = {c with code = vs'', es'' @ List.tl es;} in
                       let iv, havc' = induction_vars nhavc nc lvs in
                       havc'
                     else
                       nhavc
                   in
                   

                   (* let second_pass = SecondPass (n1, [], (args, List.map plain es')) in *)
                   let assrt = Assert (lvs, e') in
                   let first_pass = FirstPass (n1, [assrt @@ e.at], (args, List.map plain es')) in
                   let vs'', es'' = vs', [
                         (* havoc @@ e.at; *)
                         first_pass @@ e.at; (* first pass *)
                         (* second_pass @@ e.at; *)
                         (* assrt @@ e.at  *)
                       ] in
                   [{havc' with code = vs'', es'' @ List.tl es; progc = Obj.magic e'}]
                 ) (*No unroll_one *)
                 
             (* ) *)               
                        (* let lvs = find_vars [] {c with code = vs'', es'' @ List.tl es;} in *)
             (*   assertX;
                  havocv1; ... ;havocvn;
                  assume X;
                  if(c) {
                        B;
                        assertX;
                        assumefalse;
                  } *)
             (* failwith "Loop invar Not implemented yet"; *)
             )
           else ( (* Not using loop invariants *)
             let FuncType (ts1, ts2) = block_type frame.inst bt in
             let n1 = Lib.List32.length ts1 in
             let args, vs' = take n1 vs e.at, drop n1 vs e.at in
             let vs', es' = vs', [Label (n1, [Plain e' @@ e.at],
                                         (args, List.map plain es'), (pclet,pc),
                                         c.induction_vars, c.ct_check) @@ e.at] in
             [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
           )
        | If (bt, es1, es2), v :: vs' ->
           (* print_endline "if"; *)
           let pc', pc'' = split_condition v pc in (* false, true *)
           let vs'', es'' = vs', [Plain (Block (bt, es1)) @@ e.at] in (* True *)
           let vs', es' = vs', [Plain (Block (bt, es2)) @@ e.at] in (* False *)
           (* Check sat of if *)
           
           let mem = (frame.inst.smemories, smemlen frame.inst) in 
           
           let c = {c with observations = CT_UNSAT((pclet,pc), v, mem, c.observations)} in
           
           let res = if Z3_solver.is_sat (pclet, pc') mem then
                       [{c with code = vs', es' @ List.tl es; pc = (pclet,pc');
                                progc = Obj.magic e'}]
                     else [] in
           let res = if Z3_solver.is_sat (pclet, pc'') mem then
                       {c with code = vs'', es'' @ List.tl es; pc = (pclet,pc'');
                               progc = (Obj.magic e')+ 1}::res
                     else res in
           (match res with
            | [] -> failwith "If: No active path";
               (* let vs', es' = vs, [] in
                * [{c with code = vs', es' @ List.tl es}] *)
            | _::[] -> res
            | _ ->
               if (c.ct_check) then (
                 (try let _ = VulnerabilitiesMap.find (Obj.magic e') !cond_vuln in ()
                 with Not_found ->
                   let solv = Z3_solver.is_ct_unsat (pclet, pc) v mem in
                   cond_vuln := VulnerabilitiesMap.add (Obj.magic e') solv !cond_vuln;
                   if solv then () else
                     ConstantTime.warn e.at "If: Constant-time Violation"
                 );
                 res
                
               ) else res
           )

        | Br x, vs ->
           (* print_endline "br"; *)
           let vs', es' = [], [Breaking (x.it, vs) @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]
           
        | BrIf x, v :: vs' ->
           (* print_endline "br_if"; *)
           (* svalue_to_string v |> print_endline; *)
           let pc', pc'' = split_condition v pc in (* false, true *)
           let vs'', es'' = vs', [Plain (Br x) @@ e.at] in (* true *) 
           let vs', es' = vs', [] in (* false *)
           
           let mem = (frame.inst.smemories, smemlen frame.inst) in

           (* proof obligation *)
           let c = {c with observations = CT_UNSAT((pclet,pc), v, mem, c.observations)} in
           let res = if Z3_solver.is_sat (pclet, pc') mem then (
                       [{c with code = vs', es' @ List.tl es; pc = pclet,pc';
                                progc = Obj.magic e'}])
                     else [] in
           
           let res = if Z3_solver.is_sat (pclet, pc'') mem then (
                       {c with code = vs'', es'' @ List.tl es; pc = pclet,pc'';
                               progc = Obj.magic e' + 1}::res)
                     else res in

           (* print_endline (string_of_int (List.length res)); *)
           (match res with
            | [] ->
               failwith "BrIf: No active path";
               (* let vs', es' = vs, [] in
                * [{c with code = vs', es' @ List.tl es}] *)
            | _::[] -> res
            | _ ->
               if (c.ct_check) then (
                 (try let _ = VulnerabilitiesMap.find (Obj.magic e') !cond_vuln in ()
                  with Not_found ->
                    let solv = Z3_solver.is_ct_unsat (pclet, pc) v mem in
                    cond_vuln := VulnerabilitiesMap.add (Obj.magic e') solv !cond_vuln;
                    if solv then () else
                      ConstantTime.warn e.at "Br_if: Constant-time Violation"
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
           (* print_endline "call";
            * print_endline (string_of_int (Int32.to_int x.it)); *)
           let vs', es' = vs, [Invoke (func frame.inst x) @@ e.at] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]

        | CallIndirect x, SI32 i :: vs ->
           (* print_endline "call indirect"; *)

           (* Check Constant-time violation *)
           let mem = (frame.inst.smemories, smemlen frame.inst) in
           if (Z3_solver.is_v_ct_unsat (pclet, pc) (SI32 i) mem) then ()
           else ConstantTime.warn e.at "CallIndirect: Constant-time Violation";

           (* print_endline "before find_solutions"; *)
           let i_sol = Z3_solver.find_solutions (SI32 i) (pclet, pc) mem  in
           (match i_sol with
            | [] -> failwith "No solution for the symbolic value of the index."
            | _ -> List.map (fun sol ->
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
             let mem = (frame.inst.smemories, smemlen frame.inst) in
             if Z3_solver.is_ct_unsat (pclet, pc) v0 mem then res
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
           (* print_endline ("localset:" ^ (string_of_int c.counter)); *)
           (* print_endline "localset"; *)
           (* let v, c =
            *   if svalue_depth v 5 then (
            *     if (!Flags.simplify) then (
            *       let mem = (frame.inst.smemories, smemlen frame.inst) in
            *       match Z3_solver.simplify v (pclet, pc) mem with
            *       | (false), v 
            *         | (true), (Z3Expr32 _ as v)
            *         | (true), (Z3Expr64 _ as v)-> 
            *          (\* if tf then print_endline "true_expr"; *\)
            *          let nl, pc' = add_let (pclet, pc) v in
            *          let nv = svalue_newlet v nl in
            *        (\* let eq = svalue_eq nv v in *\)
            *          let c = {c with pc = pc'} in 
            *          nv,c
            *       | true, Sv v ->
            *        (\* print_endline "true";
            *         * svalue_to_string v |> print_endline; *\)
            *          v, c
            *     ) else (
            *       let nl, pc' = add_let (pclet, pc) (Sv v) in
            *       let nv = svalue_newlet (Sv v) nl in
            *       (\* let eq = svalue_eq nv v in *\)
            *       let c = {c with pc = pc'} in 
            *       nv,c
            *     )
            *   )
            *   else
            *     v, c
            * in *)
           
           let frame' = update_local c.frame x v in
           let vs', es' = vs', [] in
           [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
        | LocalTee x, v :: vs' ->
           (* print_endline "localtee"; *)

           let frame' = update_local c.frame x v in
           let vs', es' = v :: vs', [] in
           [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
        | GlobalGet x, vs ->
           let vs', es' = Sglobal.load (sglobal frame.inst x) :: vs, [] in
           [{c with code = vs', es' @ List.tl es; progc = Obj.magic e'}]              
           

        | GlobalSet x, v :: vs' ->
           let newg, vs', es' =
             (try Sglobal.store (sglobal frame.inst x) v, vs', []
              with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                 | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
           in
           let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
           [{c with code = vs', es' @ List.tl es; frame = frame'; progc = Obj.magic e'}]
        (* | GlobalSet x, v :: vs' ->
         *    (try Global.store (global frame.inst x) v; vs', []
         *     with Global.NotMutable -> Crash.error e.at "write to immutable global"
         *        | Global.Type -> Crash.error e.at "type mismatch at global write") *)

        | Load {offset; ty; sz; _}, si :: vs' ->
           (* print_endline "load"; *)
           let imem = smemory frame.inst (0l @@ e.at) in

           let frame = {frame with
                         inst = update_smemory frame.inst imem (0l @@ e.at)} in
           
           let addr =
             (match si with
              | SI32 v -> v
              | _ -> failwith "Error: Address should be 32-bit integer"
             ) in (* I64_convert.extend_i32_u i in *)
           let offset = Int32.to_int offset in        
           let mem = (frame.inst.smemories, smemlen frame.inst) in
           let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in



           (* svalue_to_string si |> print_endline;
            * print_endline "printing_test_addr 37356";
            * let test_addr = SI32 (Si32.bv_of_int 37356L 32) in
            * let load = Eval_symbolic.eval_load I32Type test_addr (smemlen frame.inst) (Types.size I32Type) None in
            * let i_sol = Z3_solver.find_solutions load (pclet, pc) mem  in
            * List.iter (fun x-> string_of_int x |> print_endline) i_sol; *)
           if (c.ct_check) then (
             
             let c = {c with observations = CT_V_UNSAT((pclet, pc), final_addr,
                                                       mem, c.observations)} in
             let msec = Smemory.get_secrets imem in
             let mpub = Smemory.get_public imem in
             let pc', pc'' = split_msec final_addr msec mpub pc in
             (* The loaded value consists of the (symbolic) index and the memory
                   index *)
             let nv =
               (* (try *)
               (match sz with
                | None ->
                   Eval_symbolic.eval_load ty final_addr
                     (smemlen frame.inst) (Types.size ty) None
                | Some (sz, ext) ->
                   assert (packed_size sz <= Types.size ty);
                   let n = packed_size sz in 
                   Eval_symbolic.eval_load ty final_addr
                     (smemlen frame.inst) n (Some ext)
               )
             in
             
             let memind, found =
               try VulnerabilitiesMap.find (Obj.magic e') !memindex_vuln, true 
               with Not_found ->
                 let solv = Z3_solver.is_v_ct_unsat (pclet, pc) final_addr mem in
                 memindex_vuln := VulnerabilitiesMap.add (Obj.magic e') solv !memindex_vuln;
                 solv, false
             in

             if memind then
               (
                 (* with exn ->
                  *    let vs', es' = vs', [Trapped (memory_error e.at exn) @@ e.at] in 
                  *    [{c with code = vs', es' @ List.tl es}]
                  * ) *)
                 let vs', es' =  nv :: vs', [] in 
                 let res =
                   match Z3_solver.is_sat (pclet, pc') mem,  Z3_solver.is_sat (pclet, pc'') mem with
                   | true,true ->
                      [{c with code = vs', es' @ List.tl es;
                               frame = frame;
                               pc = pclet, pc;
                               progc = Obj.magic e'}]
                   | true, false ->
                      [{c with code = vs', es' @ List.tl es;
                               frame = frame;
                               pc = pclet, pc';
                               progc = Obj.magic e'}]
                   | false, true ->
                      [{c with code = vs', es' @ List.tl es;
                               frame = frame;
                               pc = pclet, pc'';
                               progc = Obj.magic e'}]
                   | false, false -> failwith "Load No path left";
                 in
                 res)
                 (* let res = if Z3_solver.is_sat (pclet, pc'') mem then
                  *             (\* low values *\)
                  *             {c with code = vs', es' @ List.tl es;
                  *                     frame = frame;
                  *                     pc = pclet,pc''}:: res
                  *           else res in
                  * res) *)
             else (
               if not found then 
                 ConstantTime.warn e.at "Load: Constant-time violation"
               else ();
               
               [{c with code = nv :: vs', [] @ List.tl es;
                        frame = frame;
                        pc = pclet, pc;
                        progc = Obj.magic e'}]
             )
           )
           else (
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
             [{c with code = vs', es' @ List.tl es;
                      progc = Obj.magic e'}]
           )
           
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

           let mems = (frame.inst.smemories, smemlen frame.inst) in

           let final_addr = SI32 (Si32.add addr (Si32.of_int_u offset)) in

           
           
           if (c.ct_check) then (
             
             let c = {c with observations =
                               CT_V_UNSAT((pclet,pc), final_addr, mems, c.observations)} in


             let memind, found =
               try VulnerabilitiesMap.find (Obj.magic e') !memindex_vuln, true 
               with Not_found ->
                 let solv = Z3_solver.is_v_ct_unsat (pclet, pc) final_addr mems in
                 memindex_vuln := VulnerabilitiesMap.add (Obj.magic e') solv !memindex_vuln;
                 solv, false
             in

             
             if memind then
               
               let msec = Smemory.get_secrets mem in
               let mpub = Smemory.get_public mem in
               (* print_endline "c.msecrets";
                * List.length msec |> string_of_int |> print_endline; *)
               let pc', pc'' = split_msec final_addr msec mpub pc in
               (* print_endline "Store:";
                * svalue_to_string sv |> print_endline;
                * svalue_to_string final_addr |> print_endline; *)
               (* print_pc pc' |> print_endline; *)
               (* print_pc pc'' |> print_endline; *)

               let nv =
                 (match sz with
                  | None -> Eval_symbolic.eval_store ty final_addr sv
                              (smemlen frame.inst) (Types.size ty)
                  | Some (sz) ->
                     assert (packed_size sz <= Types.size ty);
                     let n = packed_size sz in
                     Eval_symbolic.eval_store ty final_addr sv
                       (smemlen frame.inst) n
                 )
               in

               (* let nv = Eval_symbolic.eval_store ty final_addr sv
                *            (smemlen frame.inst) 4 in *)
               let mem' = Smemory.store_sind_value mem nv in
               let vs', es' = vs', [] in
               (* Update memory with a store *)
               let nframe = {frame with inst = insert_smemory frame.inst mem'} in

               (* Path1: we store the value in secret memory *)
               let res =
                 (* match Z3_solver.is_sat (pclet, pc') mems, *)
                 match Z3_solver.is_sat (pclet, pc'') mems with
                 | true ->
                    let c =
                      {c with observations =
                                CT_V_UNSAT((pclet,pc''), sv, mems, c.observations)} in
                    
                    let nonv, found =
                      if (!Flags.explicit_leaks) then (
                        try VulnerabilitiesMap.find (Obj.magic e') !noninter_vuln, true 
                        with Not_found ->
                          let solv = Z3_solver.is_v_ct_unsat (pclet, pc'') sv mems in
                          noninter_vuln := VulnerabilitiesMap.add (Obj.magic e') solv !noninter_vuln;
                          solv, false)
                      else true, false
                    in

                    (if nonv then
                       (match Z3_solver.is_sat (pclet, pc') mems with
                        | true -> [{c with code = vs', es' @ List.tl es;
                                           frame = nframe;
                                           pc = pclet, pc;
                                           progc = Obj.magic e'}]
                        | false -> [{c with code = vs', es' @ List.tl es;
                                            frame = nframe;
                                            pc = pclet, pc'';
                                            progc = Obj.magic e'}]
                       )
                     else (
                       if not found then 
                         NonInterference.warn e.at "Trying to write high values in low memory"
                       else ();
                       [{c with code = vs', es' @ List.tl es;
                                           frame = nframe;
                                           pc = pclet, pc;
                                           progc = Obj.magic e'}]
                     )
                    )
                 | false ->
                    (match Z3_solver.is_sat (pclet, pc') mems with
                     | true -> [{c with code = vs', es' @ List.tl es;
                                        frame = nframe;
                                        pc = pclet, pc';
                                        progc = Obj.magic e'}]
                     | false -> failwith "No possible path available"
                    )
               in res
             else (
               if not found then ConstantTime.warn e.at "Store: Constant-time violation"
               else ();
               [{c with code = vs', [] @ List.tl es;
                        frame = frame;
                        pc = pclet, pc;
                        progc = Obj.magic e'}]
             )
           )
           else (
             let nv =
               (match sz with
                | None ->
                   Eval_symbolic.eval_store ty final_addr sv
                     (smemlen frame.inst) (Types.size ty)
                | Some (sz) ->
                   assert (packed_size sz <= Types.size ty);
                   let n = packed_size sz in
                   Eval_symbolic.eval_store ty final_addr sv
                     (smemlen frame.inst) n
               )
             in

             let mem' = Smemory.store_sind_value mem nv in
             let vs', es' = vs', [] in
             (* Update memory with a store *)
             let nframe = {frame with inst = insert_smemory frame.inst mem'} in

             [{c with code = vs', es' @ List.tl es;
                      frame = nframe;
                      progc = Obj.magic e'}]
           )
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

    | Assert (lvs, e), vs ->
       if !Flags.debug then 
         print_endline "Asserting invariant..";
       (* print_endline "assert"; *)
       if assert_invar lvs c then (
         analyzed_loops := AnalyzedLoopsMap.add (Obj.magic e) lvs (!analyzed_loops);
         [{c with code = vs, List.tl es}]
       )
       else failwith "Assertion failed"
       
    | Havoc lvs, vs ->
       (* print_endline "havoc"; *)
       let havc = havoc_vars lvs c in
       [{havc with code = vs, List.tl es}]

    | FirstPass  (n, es0, (vs', code')), vs ->
       (* print_endline "first pass"; *)

       let vs', es' = vs, [Label (n, es0, (vs', code'),
                                  (pclet, pc), c.induction_vars, true) @@ e.at] in
       if (!Flags.elim_induction_variables) then (
           let c' = elim_induction_vars_loop {c with code = vs', es'} in
           List.map (fun ci -> {c with code = vs, List.tl es}) c'
         )
       else (
         [{c with code = vs', es' @ List.tl es}]
       )
    | SecondPass  (n, [{it=Plain ((Loop _) as l); at=loc}], (vs''', code''')), vs ->
       (* print_endline "second pass"; *)
       (* print_endline "Printing induction variables";
        * print_endline (induction_vars_to_string c.induction_vars); *)

       (* let vv = local frame (18l @@ e.at) in
        * let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in
        * let is_low = Z3_solver.is_v_ct_unsat c.pc vv mem in
        * print_endline (string_of_bool is_low); *)


       let lvs = 
         (* try (
          *   ModifiedVarsMap.find (Obj.magic l) !modified_vars
          * ) with Not_found -> ( *)
           (* print_endline "Finding vars"; *)
           let vs'', es'' = vs, [Label (n, [Plain l @@ loc],
                                        (vs''', code'''), (pclet,pc),
                                        c.induction_vars, c.ct_check) @@ e.at] in

           let lvs, _ = find_modified_vars (Obj.magic e) {c with code = vs'', es'' @ List.tl es;} in
           (* print_endline "loop modified variables:";
            * print_endline (string_of_int (List.length lvs));
            * List.iter print_loopvar lvs; *)

           (* print_endline "Merging vars"; *)
           let lvs = merge_vars lvs in

           (* print_endline "loop modified variables:";
            * print_endline (string_of_int (List.length lvs));
            * List.iter print_loopvar lvs; *)

           modified_vars := ModifiedVarsMap.add (Obj.magic l) lvs !modified_vars;
           lvs
         (* ) *)
       in
       
       (* print_endline "loop modified variables:";
        * print_endline (string_of_int (List.length lvs));
        * List.iter print_loopvar lvs; *)

       (* print_endline "Havocing"; *)
       (* HAVOC *)
       let havc = havoc_vars lvs c in
       let assrt = Assert (lvs, l) in
      
       let vs'', es'' = vs, [Label (n, [assrt @@ e.at],
                                     (vs''', code'''), (pclet,pc),
                                     c.induction_vars, c.ct_check) @@ e.at] in

       (* print_endline "Finish second pass"; *)
       let havc = {havc with code = vs'', es'' @ List.tl es;} in
       (* let havc' =
        *   if !Flags.elim_induction_variables then
        *     let nc = {c with code = vs'', es'' @ List.tl es;} in
        *     let iv, havc' = induction_vars nhavc nc lvs in
        *     havc'
        *   else
        *     nhavc
        * in *)
       
       (* let first_pass = FirstPass (n1, [], (args, List.map plain es')) in *)
       (* let second_pass = SecondPass (n1, [], (args, List.map plain es')) in *)
       (* let vs'', es'' = vs, [
        *       (\* havoc @@ e.at; *\)
        *       (\* first_pass @@ e.at; (\\* first pass *\\) *\)
        *       (\* second_pass @@ e.at; *\)
        *       assrt @@ e.at
        *     ] in *)
       [{havc with code = vs'', es'' @ List.tl es; progc = Obj.magic l}]

       (* let vs', es' = vs, [Label (n, es0, (vs', code'),
        *                            (pclet, pc), c.induction_vars, true) @@ e.at] in *)
       
       (* if (!Flags.elim_induction_variables) then (
        *   let c' = elim_induction_vars_loop {c with code = vs', es'} in
        *   List.map (fun ci -> {c with code = vs, List.tl es}) c'
        * )
        * else (
        *   [{c with code = vs', es' @ List.tl es}]
        * ) *)
    | SecondPass  (n, _, (vs''', code''')), vs ->
       Crash.error e.at "Unexpected SecondPass without loop"
      
    | Returning vs', vs ->
       Crash.error e.at "undefined frame"

    | Breaking (k, vs'), vs ->
       Crash.error e.at "undefined label"

    | Label (n, es0, (vs', []), pc', iv', cct), vs ->
       (* print_endline ("lab:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs' @ vs, [] in
       [{c with code = vs', es' @ List.tl es}]
       
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
       (*TODO(Romy): not sure if correct to change the pc *)
       let c' = step {c with code = code'; pc = pc';
                             induction_vars = iv';
                             counter = c.counter + 1;
                             ct_check = cct'} in
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
                                      ci.code, ci.pc, ci.induction_vars) @@ e.at] @ List.tl es;
                   (* pc = ci.pc; *)
                   observations = ci.observations;
                   induction_vars = iv'
                   (* frame = ci.frame *)
         }) c'

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

           let frame' = {inst = inst'; locals = locals'} in
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
  let rec eval_dfs_i (cs : config list) (acc : pc_ext list) =
    (* print_endline "eval_dfs_i"; *)
    match cs with
    | c::cs' ->
       (match c.code with
        | vs, [] -> eval_dfs_i cs' (c.pc::acc)
        | vs, {it = Trapping msg; at} :: _ -> Trap.error at msg
        | vs, es -> (
           let ncs = step {c with counter = c.counter + 1} in
           eval_dfs_i (ncs @ cs') acc
        )
       )
      
    | [] -> List.rev acc
  in
  eval_dfs_i cs []


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
 *     (\* Compare PC *\)
 *     (\* Compare Locals/Globals/Mem *\)
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
 * (\* Eval Merge States *\)
 * let eval_mp (cs : config list) : pc_ext list =
 *   let rec eval_mp_i acc =
 *     (\* print_endline "eval_dfs_i"; *\)
 *     let k, cs = MPMap.find_first (fun k -> true) !mp in
 *     match cs with
 *     | c::cs' ->
 *        (\* add back the rest *\)
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

  let mem = List.fold_left Smemory.store_sind_value smem stores in  
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
  let mem = List.fold_left Smemory.store_sind_value smem stores in  
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
                                     smemlen = 1 + inst.smemlen }
  | ExternGlobal glob -> {inst with globals = glob :: inst.globals}
  | ExternSglobal glob -> {inst with sglobals = glob :: inst.sglobals}

let init (m : module_) (exts : extern list) : module_inst =
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
  inst
