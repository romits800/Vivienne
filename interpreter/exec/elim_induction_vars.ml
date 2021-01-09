open Eval
open Svalues
open Types
open Instance
open Ast
open Source
open Find_induction_vars


let multiply_triple iv b1 b2 =
  match iv, b1, b2 with
    SI32 iv, SI32 b1, SI32 b2 ->
     let add = Si32.add in
     let mul = Si32.mul in
     SI32 (mul iv b1 |> add b2)
  | SI64 iv, SI64 b1, SI64 b2 ->
     let add = Si64.add in
     let mul = Si64.mul in
     SI64 (mul iv b1 |> add b2)
  | _ -> failwith "floating points not supported."


let rec elim_induction_vars_loop (c : config) : config list =
  let {frame; code = vs, es; pc = pclet, pc; _} = c in
  let e = List.hd es in

  let c = {c with pc = (pclet,pc)} in
  let res =
    match e.it, vs with
    | Plain e', vs ->
       (match e', vs with
        | Unreachable, vs ->
           (* print_endline "Unreachable"; *)
           let vs', es' = vs, [Trapping "unreachable executed" @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]
        | Nop, vs ->
           (* print_endline "nop"; *)
           let vs', es' = vs, [] in
           [{c with code = vs', es' @ List.tl es}]
        | Block (bt, es'), vs ->
           (* print_endline "block"; *)
           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let n2 = Lib.List32.length ts2 in
           let args, vs' = take n1 vs e.at, drop n1 vs e.at in
           let vs', es' = vs', [Label (n2, [], (args, List.map plain es'), (pclet,pc)) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]
        | Loop (bt, es'), vs ->
           let FuncType (ts1, ts2) = block_type frame.inst bt in
           let n1 = Lib.List32.length ts1 in
           let args, vs' = take n1 vs e.at, drop n1 vs e.at in
           let vs', es' = vs', [Label (n1, [e' @@ e.at],
                                       (args, List.map plain es'), (pclet,pc)) @@ e.at] in
           [{c with code = vs', es' @ List.tl es;}]

        | If (bt, es1, es2), v :: vs' ->
           (* print_endline "if"; *)
           let pc', pc'' = split_condition v pc in (* false, true *)
           let vs'', es'' = vs', [Plain (Block (bt, es1)) @@ e.at] in (* True *)
           let vs', es' = vs', [Plain (Block (bt, es2)) @@ e.at] in (* False *)
           (* Check sat of if *)
           
           let mem = (frame.inst.smemories, smemlen frame.inst) in 
           
           let c = {c with observations = CT_UNSAT((pclet,pc), v, mem, c.observations)} in
           
           let res = if Z3_solver.is_sat (pclet, pc') mem then
                       [{c with code = vs', es' @ List.tl es; pc = (pclet,pc')}]
                     else [] in
           let res = if Z3_solver.is_sat (pclet, pc'') mem then
                       {c with code = vs'', es'' @ List.tl es; pc = (pclet,pc'')}::res
                     else res in
           (match res with
            | [] -> failwith "If: No active path";
               (* let vs', es' = vs, [] in
                * [{c with code = vs', es' @ List.tl es}] *)
            | _::[] -> res
            | _ ->
               if Z3_solver.is_ct_unsat (pclet, pc) v mem then res
               else (
                 ConstantTime.warn e.at "If: Constant-time Violation";
                 res)
           )

        | Br x, vs ->
           (* print_endline "br"; *)
           let vs', es' = [], [Breaking (x.it, vs) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]
           
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
                       [{c with code = vs', es' @ List.tl es; pc = pclet,pc'}])
                     else [] in
           
           let res = if Z3_solver.is_sat (pclet, pc'') mem then (
                       {c with code = vs'', es'' @ List.tl es; pc = pclet,pc''}::res)
                     else res in

           (match res with
            | [] -> failwith "BrIf: No active path";
               (* let vs', es' = vs, [] in
                * [{c with code = vs', es' @ List.tl es}] *)
            | _::[] -> res
            | _ ->
                 if Z3_solver.is_ct_unsat (pclet, pc) v mem
                 then res
                 else (
                   ConstantTime.warn e.at "BrIf: Constant-time Violation";
                   res)
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
           [{c with code = vs', es' @ List.tl es}]

        | Call x, vs ->
           (* print_endline "call";
            * print_endline (string_of_int (Int32.to_int x.it)); *)
           let vs', es' = vs, [Invoke (func frame.inst x) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]

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
                         {c with code = vs', es' @ List.tl es}
                       else
                         let vs', es' = vs, [Invoke func @@ e.at] in
                         {c with code = vs', es' @ List.tl es}
                     ) i_sol
           )
           
        | Drop, v :: vs' ->
           let vs', es' = vs', [] in
           [{c with code = vs', es' @ List.tl es}]
           
        | Select, v0 :: v2 :: v1 :: vs' ->
           (* print_endline "select"; *)
           let vselect = select_condition v0 v1 v2 in
           let vs', es' = vselect :: vs', [] in
           let res = [{c with code = vs', es' @ List.tl es }] in
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
           [{c with code = vs', es' @ List.tl es}]

        | LocalSet x, v :: vs' ->
           let oldv = local frame x in
           let ivs = match c.induction_vars with Some ivs -> ivs | None -> failwith "No ivs"; in
           (try
              let _, iv, b1, b2 = IndVarMap.find oldv ivs in
              let v = multiply_triple iv b1 b2 in
              let frame' = update_local c.frame x v in
              let vs', es' = vs', [] in
              [{c with code = vs', es' @ List.tl es; frame = frame'}]
           with Not_found ->                 
             let frame' = update_local c.frame x v in
             let vs', es' = vs', [] in
             [{c with code = vs', es' @ List.tl es; frame = frame'}])
        | LocalTee x, v :: vs' ->
           (* print_endline "localtee"; *)
           let oldv = local frame x in
           let ivs = match c.induction_vars with Some ivs -> ivs | None -> failwith "No ivs"; in

           (try
              let _, iv, b1, b2 = IndVarMap.find oldv ivs in
              let v = multiply_triple iv b1 b2 in
              let frame' = update_local c.frame x v in
              let vs', es' = v :: vs', [] in
              [{c with code = vs', es' @ List.tl es; frame = frame'}]
            with Not_found ->
              let frame' = update_local c.frame x v in
              let vs', es' = v :: vs', [] in
              [{c with code = vs', es' @ List.tl es; frame = frame'}])
        | GlobalGet x, vs ->
           let vs', es' = Sglobal.load (sglobal frame.inst x) :: vs, [] in
           [{c with code = vs', es' @ List.tl es}]              
           

        | GlobalSet x, v :: vs' ->

           let oldv = Sglobal.load (sglobal frame.inst x) in
           let ivs = match c.induction_vars with Some ivs -> ivs | None -> failwith "No ivs"; in

           (try
              let _, iv, b1, b2 = IndVarMap.find oldv ivs in
              let v = multiply_triple iv b1 b2 in
              let newg, vs', es' =
                (try Sglobal.store (sglobal frame.inst x) v, vs', []
                 with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                    | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
              in
             let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
             [{c with code = vs', es' @ List.tl es; frame = frame'}]
            with Not_found ->
              let newg, vs', es' =
                (try Sglobal.store (sglobal frame.inst x) v, vs', []
                 with Sglobal.NotMutable -> Crash.error e.at "write to immutable global"
                    | Sglobal.Type -> Crash.error e.at "type mismatch at global write")
              in
              let frame' = {frame with inst = update_sglobal c.frame.inst newg x} in
              [{c with code = vs', es' @ List.tl es; frame = frame'}]
           )
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
           
           if (Z3_solver.is_v_ct_unsat (pclet, pc) final_addr mem) then
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
                             pc = pclet, pc}]
                 | true, false ->
                    [{c with code = vs', es' @ List.tl es;
                             frame = frame;
                             pc = pclet, pc'}]
                 | false, true ->
                    [{c with code = vs', es' @ List.tl es;
                             frame = frame;
                             pc = pclet, pc''}]
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
             ConstantTime.warn e.at "Load: Constant-time violation";
             [{c with code = nv :: vs', [] @ List.tl es;
                      frame = frame;
                      pc = pclet, pc}]
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

           
           
           let c = {c with observations =
                             CT_V_UNSAT((pclet,pc), final_addr, mems, c.observations)} in


           if (Z3_solver.is_v_ct_unsat (pclet, pc) final_addr mems) then
             
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

             (* let nv, lnv =
              *   (match sz with
              *    | None ->
              *       let nv = Eval_symbolic.eval_store ty final_addr sv
              *                  (smemlen frame.inst) (Types.size ty) in
              *       let lvn = (Eval_symbolic.eval_load ty final_addr
              *                    (smemlen frame.inst) (Types.size ty) None) in
              *       nv, lvn
              *    | Some (sz) ->
              *       assert (packed_size sz <= Types.size ty);
              *       let n = packed_size sz in
              *       let nv = Eval_symbolic.eval_store ty final_addr sv
              *                  (smemlen frame.inst) n in
              *       let lvn = Eval_symbolic.eval_load ty final_addr
              *                   (smemlen frame.inst) n None in
              *       nv, lvn
              *   )
              * in *)
             let lnv =
               (match sz with
                | None ->
                   let lvn = (Eval_symbolic.eval_load ty final_addr
                                (smemlen frame.inst) (Types.size ty) None) in
                   lvn
                | Some (sz) ->
                   assert (packed_size sz <= Types.size ty);
                   let n = packed_size sz in
                   let lvn = Eval_symbolic.eval_load ty final_addr
                               (smemlen frame.inst) n None in
                   lvn
               )
             in

             let ivs = match c.induction_vars with Some ivs -> ivs | None -> failwith "No ivs"; in
             let nv = (try
                        let _, iv, b1, b2 = IndVarMap.find lnv ivs in
                        multiply_triple iv b1 b2
                       with Not_found ->                 
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
                  (if Z3_solver.is_v_ct_unsat (pclet, pc'') sv mems then
                     (match Z3_solver.is_sat (pclet, pc') mems with
                      | true -> [{c with code = vs', es' @ List.tl es;
                                         frame = nframe;
                                         pc = pclet, pc}]
                      | false -> [{c with code = vs', es' @ List.tl es;
                                          frame = nframe;
                                          pc = pclet, pc''}]
                     )
                   else (
                     NonInterference.warn e.at "Trying to write high values in low memory";
                     [{c with code = vs', es' @ List.tl es;
                              frame = nframe;
                              pc = pclet, pc}]
                   )
                  )
               | false ->
                  (match Z3_solver.is_sat (pclet, pc') mems with
                   | true -> [{c with code = vs', es' @ List.tl es;
                                      frame = nframe;
                                      pc = pclet, pc'}]
                   | false -> failwith "No possible path available"
                  )
             in res
           else (
             ConstantTime.warn e.at "Store: Constant-time violation";
             [{c with code = vs', [] @ List.tl es;
                      frame = frame;
                      pc = pclet, pc}]

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
           [{c with code = vs', es' @ List.tl es}]
           
        (* | Const v, vs ->
         *    v.it :: vs, [] *)

        | Test testop, v :: vs' ->
           (* print_endline "testop"; *)
           let vs', es' =
             (try (svalue32_of_bool (Eval_symbolic.eval_testop testop v)) :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es}]
           
        | Compare relop, v2 :: v1 :: vs' ->
           (* print_endline "relop"; *)
           let vs', es' =
             (try (svalue32_of_bool (Eval_symbolic.eval_relop relop v1 v2)) :: vs', []
              with exn ->
                vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es}]
        | Unary unop, v :: vs' ->
           (* print_endline "unop"; *)
           let vs', es' = 
             (try Eval_symbolic.eval_unop unop v :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at]) in
           [{c with code = vs', es' @ List.tl es}]
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
           [{c with code = vs', es' @ List.tl es}]
        | Convert cvtop, v :: vs' ->
           let vs', es' = 
             (try Eval_symbolic.eval_cvtop cvtop v :: vs', []
              with exn -> vs', [Trapping (numeric_error e.at exn) @@ e.at])
           in [{c with code = vs', es' @ List.tl es}]
            
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

    | Assert lvs, vs ->
       print_endline "assert";
       if assert_invar lvs c then
         [{c with code = vs, List.tl es}]
       else failwith "Assertion failed"
       
    | Havoc lvs, vs ->
       failwith "Havoc in elim induction vars"
      
    | SecondPass  (n, es0, (vs', code')), vs ->
       failwith "SecondPass in elim induction vars"
    (* failwith "SecondPass: not implemented" *)

    | Returning vs', vs ->
       Crash.error e.at "undefined frame"

    | Breaking (k, vs'), vs ->
       Crash.error e.at "undefined label"

    | Label (n, es0, (vs', []), pc'), vs ->
       (* print_endline ("lab:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs' @ vs, [] in
       [{c with code = vs', es' @ List.tl es}]
       
    | Label (n, es0, (vs', {it = Trapping msg; at} :: es'), pc'), vs ->
       (* print_endline "lab2"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Returning vs0; at} :: es'), pc'), vs ->
       (* print_endline ("lab3:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs, [Returning vs0 @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (0l, vs0); at} :: es'), pc'), vs ->
       (* print_endline ("lab4:" ^ (string_of_int c.counter)); *)
       let vs', es' = take n vs0 e.at @ vs, List.map plain es0 in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, (vs', {it = Breaking (k, vs0); at} :: es'), pc'), vs ->
       (* print_endline ("lab5:" ^ (string_of_int c.counter)); *)
       let vs', es' = vs, [Breaking (Int32.sub k 1l, vs0) @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Label (n, es0, code', pc'), vs ->
       (* print_endline ("lab6:" ^ (string_of_int c.counter)); *)
       (*TODO(Romy): not sure if correct to change the pc *)
       let c' = elim_induction_vars_loop
                  {c with code = code'; pc = pc'; counter = c.counter + 1} in
       (* print_endline ("lab6_end:" ^ (string_of_int c.counter)); *)
       List.map (fun ci -> {c with code = vs,
                                          [Label (n, es0, ci.code, ci.pc) @@ e.at]
                                          @ List.tl es;
                                   pc = ci.pc; (*  *)
                                   observations = ci.observations;
                                   frame = ci.frame
         }) c'

    | Frame (n, frame', (vs', []), pc'), vs ->
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
                pc = pc'
       }]

    | Frame (n, frame', (vs', {it = Trapping msg; at} :: es'), _), vs ->
       (* print_endline "frame trappping"; *)
       let vs', es' = vs, [Trapping msg @@ at] in
       [{c with code = vs', es' @ List.tl es}]

    | Frame (n, frame', (vs', {it = Returning vs0; at} :: es'), pc'), vs ->
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
                pc = pc'}]

    | Frame (n, frame', code', pc'), vs ->
       (* print_endline "frame normal"; *)
       (* print_endline ("frame4:" ^ (string_of_int c.counter)); *)

       let c' = elim_induction_vars_loop
                  {c with frame = frame'; code = code';
                          budget = c.budget - 1; pc = pc';
                          counter = c.counter + 1} in
       (* print_endline ("frame4_end:" ^ (string_of_int c.counter)); *)
       (* TODO(Romy): the pc etc  should probably not be here *)
       List.map (fun ci ->
           {c with code = vs, [Frame (n, ci.frame,
                                      ci.code, ci.pc) @@ e.at] @ List.tl es;
                   (* pc = ci.pc; *)
                   observations = ci.observations;
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
           let instr' = [Label (n2, [], ([], List.map plain f.it.body), c.pc) @@ f.at] in 
           let vs', es' = vs', [Frame (n2, frame', ([], instr'), c.pc) @@ e.at] in
           [{c with code = vs', es' @ List.tl es}]

        (* | Func.HostFunc (t, f) ->
         *   (try List.rev (f (List.rev args)) @ vs', []
         *   with Crash (_, msg) -> Crash.error e.at msg) *)
        | _ -> Crash.error e.at "Func.Hostfunc not implemented yet."
       )
  in
  (* print_endline "end of step";
   * List.length res |> string_of_int |> print_endline;
   * List.iter (fun c -> Pc_type.print_pc c.pc |> print_endline;) res; *)
  res




