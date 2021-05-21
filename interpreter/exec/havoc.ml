open Eval
open Svalues
open Types
open Source
open Pc_type
open Ast
open Loop_stats
  
let havoc_vars (lv: loopvar_t list) (c : config) (stats: stats_t) =
 let has_index (stats: stats_t) loc = 
    let rec has_index_i indexes loc = 
       match indexes with
       | (lv,st,Some nv)::indexes when st.at = loc -> Some nv, true
       | ind::indexes -> has_index_i indexes loc
       | [] -> None, false
    in
    has_index_i (get_store_indexes stats) loc
    
 in

 let rec havoc_vars_i (lv: loopvar_t list) (c : config) (stats: stats_t) =
  if !Flags.debug then (
    print_endline "Havocing Variables..";
    List.iter print_loopvar lv
  );
  match lv with
  | LocalVar (x, is_low, mo, Some (newv,simp)) :: lvs ->
 
     let rec is_store_index indexes nv acc =
       match indexes with
       | ({it = LocalGet x'; at},st,None)::indexes when x'.it = x.it -> 
            let ind = ({it = LocalGet x'; at}, st, Some nv) in 
            ((ind::indexes) @ acc, Some st, true)
       | ({it = LocalTee x'; at},st,None)::indexes when x'.it = x.it ->
            let ind = ({it = LocalTee x'; at}, st, Some nv) in
            ((ind::indexes) @ acc, Some st, true)
       | ind::indexes -> is_store_index indexes nv (ind::acc)
       | [] -> (acc, None, false)
     in

     if !Flags.debug then (
       print_endline "LocalVar constant";
       print_endline (simpl_to_string simp);
     );

     (* let v = local c.frame x in *)
     (* let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in *)
     (* let is_low = Z3_solver.is_v_ct_unsat c.pc v mem in *)

     if !Flags.debug then (
        print_endline ("Local" ^ (string_of_int (Int32.to_int x.it)) ^ " newval:" ^ (simpl_to_string simp));
     );
    
     let indexes = get_store_indexes stats in
     let indexes', st, tf = is_store_index indexes newv [] in
    
     let c' = { c with frame = update_local c.frame x newv } in 

     if !Flags.debug then (
        print_endline "Is index constant";
        print_endline (string_of_bool tf);
     );


     let c'' =
       if !Flags.end_of_ro_data >= 0 then (
           match newv, tf with
           | SI32 nv, true ->
              let data = Si32.of_int_u (!Flags.end_of_ro_data) in
              let pcnum, pclet, pc = c'.pc in
              print_endline "adding constraint";
              { c' with pc = (pcnum, pclet, PCAnd(SI32 (Si32.gt_u nv data), c'.pc)) }
           | _ -> c'
       ) else c'
     in
     havoc_vars_i lvs c'' (set_store_indexes stats indexes')

  | LocalVar (x, is_low, mo, None) :: lvs ->
 
     let rec is_store_index indexes nv acc =
       match indexes with
       | ({it = LocalGet x'; at},st,None)::indexes when x'.it = x.it -> 
            let ind = ({it = LocalGet x'; at}, st, Some nv) in 
            ((ind::indexes) @ acc, Some st, true)
       | ({it = LocalTee x'; at},st,None)::indexes when x'.it = x.it ->
            let ind = ({it = LocalTee x'; at}, st, Some nv) in
            ((ind::indexes) @ acc, Some st, true)
       | ind::indexes -> is_store_index indexes nv (ind::acc)
       | [] -> (acc, None, false)
     in
          
     let v = local c.frame x in
     (* let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in *)
     (* let is_low = Z3_solver.is_v_ct_unsat c.pc v mem in *)
     let newv =
       (match v with
        | SI32 _ -> SI32 (if is_low then Si32.of_low() else Si32.of_high())
        | SI64 _ -> SI64 (if is_low then Si64.of_low() else Si64.of_high())
        | _ -> failwith "not implemented floated numbers"
       )
     in
     if !Flags.debug then (
        print_endline ("Local" ^ (string_of_int (Int32.to_int x.it)) ^ " newval:" ^ (svalue_to_string newv));
     );
    
     let indexes = get_store_indexes stats in
     let indexes', st, tf = is_store_index indexes newv [] in
    
     let c' = { c with frame = update_local c.frame x newv } in 

     if !Flags.debug then (
        print_endline "Is index";
        print_endline (string_of_bool tf);
     );


     let c'' =
       if !Flags.end_of_ro_data >= 0 then (
           match newv, tf with
           | SI32 nv, true ->
              let data = Si32.of_int_u (!Flags.end_of_ro_data) in
              let pcnum, pclet, pc = c'.pc in
              print_endline "adding constraint";
              { c' with pc = (pcnum, pclet, PCAnd(SI32 (Si32.gt_u nv data), c'.pc)) }
           | _ -> c'
       ) else c'
     in
     havoc_vars_i lvs c'' (set_store_indexes stats indexes')
  | GlobalVar (x, is_low, mo, Some (newv,simp)) :: lvs ->
     let rec is_store_index indexes nv acc =
       match indexes with
       | ({it = GlobalGet x'; at},st,None)::indexes when x'.it = x.it -> 
            let ind = ({it = GlobalGet x'; at}, st, Some nv) in
            ((ind::indexes) @ acc, Some st, true)
 
       | ind::indexes -> is_store_index indexes nv (ind::acc)
       | [] -> (acc, None, false)
     in

     let newg = 
       (try Sglobal.store (sglobal c.frame.inst x) newv
        with Sglobal.NotMutable -> Crash.error x.at "write to immutable global"
           | Sglobal.Type -> Crash.error x.at "type mismatch at global write")
     in
     
     let indexes = get_store_indexes stats in
     let indexes', st, tf = is_store_index indexes newv [] in
     let c' = { c with frame = {c.frame with inst = update_sglobal c.frame.inst newg x } } in

     let c'' =
       match newv, tf with
       | SI32 nv, true ->
          let data = Si32.of_int_u (!Flags.end_of_ro_data) in
          let pcnum, pclet, pc = c'.pc in
          { c' with pc = (pcnum, pclet, PCAnd(SI32 (Si32.ge_u nv data), c'.pc)) }
       | _ -> c'
     in
     havoc_vars_i lvs c'' (set_store_indexes stats indexes')

  | GlobalVar (x, is_low, mo, None) :: lvs ->
     let rec is_store_index indexes nv acc =
       match indexes with
       | ({it = GlobalGet x'; at},st,None)::indexes when x'.it = x.it -> 
            let ind = ({it = GlobalGet x'; at}, st, Some nv) in
            ((ind::indexes) @ acc, Some st, true)
 
       | ind::indexes -> is_store_index indexes nv (ind::acc)
       | [] -> (acc, None, false)
     in

     let v = Sglobal.load (sglobal c.frame.inst x) in
     (* let mem = (c..inst.smemories, smemlen c.frame.inst) in *)
     (* let is_low = Z3_solver.is_v_ct_unsat c.pc v mem in *)
     let newv =
       (match v with
        | SI32 _ -> SI32 (if is_low then Si32.of_low() else Si32.of_high())
        | SI64 _ -> SI64 (if is_low then Si64.of_low() else Si64.of_high())
        | _ -> failwith "not implemented floated numbers"
       )
     in
     let newg = 
       (try Sglobal.store (sglobal c.frame.inst x) newv
        with Sglobal.NotMutable -> Crash.error x.at "write to immutable global"
           | Sglobal.Type -> Crash.error x.at "type mismatch at global write")
     in
     
     let indexes = get_store_indexes stats in
     let indexes', st, tf = is_store_index indexes newv [] in
     let c' = { c with frame = {c.frame with inst = update_sglobal c.frame.inst newg x } } in

     let c'' =
       match newv, tf with
       | SI32 nv, true ->
          let data = Si32.of_int_u (!Flags.end_of_ro_data) in
          let pcnum, pclet, pc = c'.pc in
          { c' with pc = (pcnum, pclet, PCAnd(SI32 (Si32.ge_u nv data), c'.pc)) }
       | _ -> c'
     in
     havoc_vars_i lvs c'' (set_store_indexes stats indexes')
  | StoreVar (Some (SI32 addr' as addr), ty, sz, is_low, mo, loc) :: lvs when Si32.is_int addr' ->
     let sv =
       (match ty with
        |Types.I32Type ->
          SI32 (if is_low then Si32.of_low() else Si32.of_high())
        |Types.I64Type ->
          SI64 (if is_low then Si64.of_low() else Si64.of_high())
        | _ -> failwith "not implemented float types"
       )
     in          
     if !Flags.debug then (
        print_endline "New val store:";
        print_loopvar (StoreVar (Some addr, ty, sz, is_low, mo, loc));
        print_endline (svalue_to_string sv);
     );
     let num = Instance.next_num() in
     let nv =
       (match sz with
        | None ->
           Eval_symbolic.eval_store ty addr sv
             (smemlen c.frame.inst) num (Types.size ty)
        | Some (sz) ->
           assert (packed_size sz <= Types.size ty);
           let n = packed_size sz in
           Eval_symbolic.eval_store ty addr sv
             (smemlen c.frame.inst) num n 
       )
     in
     let mem = smemory c.frame.inst (0l @@ Source.no_region) in
     let mem' = Smemory.store_sind_value num mem nv in

     let nframe  = {c.frame with inst = insert_smemory c.frame.inst num mem'} in
     let c' = { c with frame = nframe} in

     havoc_vars_i lvs c' stats
  | StoreVar (_, ty, sz, is_low, mo, loc) :: lvs  ->
    (match has_index stats loc with
     | Some addr, true when not (!Flags.exclude_zero_address && is_int_addr addr && get_int_addr addr = 0)->
          if !Flags.debug then (
            print_endline "Storing constant address..";
            print_endline (svalue_to_string addr);
          );
     
         let sv =
           (match ty with
            |Types.I32Type ->
              SI32 (if is_low then Si32.of_low() else Si32.of_high())
            |Types.I64Type ->
              SI64 (if is_low then Si64.of_low() else Si64.of_high())
            | _ -> failwith "not implemented float types"
           )
         in          
         let num = Instance.next_num() in
         let nv =
           (match sz with
            | None ->
               Eval_symbolic.eval_store ty addr sv
                 (smemlen c.frame.inst) num (Types.size ty)
            | Some (sz) ->
               assert (packed_size sz <= Types.size ty);
               let n = packed_size sz in
               Eval_symbolic.eval_store ty addr sv
                 (smemlen c.frame.inst) num n 
           )
         in
         let mem = smemory c.frame.inst (0l @@ Source.no_region) in
         let mem' = Smemory.store_sind_value num mem nv in

         let nframe  = {c.frame with inst = insert_smemory c.frame.inst num mem'} in
         let c' = { c with frame = nframe} in
         havoc_vars_i lvs c' stats
     | _, _ ->  havoc_vars_i lvs c stats
     ) 

 (* | StoreVar _ :: lvs -> havoc_vars_i lvs c stats*)
  | StoreZeroVar _ :: lvs -> havoc_vars_i lvs c stats
  | [] -> c
 in
 havoc_vars_i lv c stats 
                
