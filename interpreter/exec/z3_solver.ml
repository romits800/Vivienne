open Pc_type
open Z3
open Svalues
open Smt_type
open Sys
(* open Unix *)
open Smtlib
open Stats  
   
let path = ref (getenv "VIV_PATH")

let gl_expr_counter = ref 0
let si_expr_counter = ref 0

  
exception Timeout (*of string*)


(* let compare_tuple v1 v2 =
 *   match v1, v2 with 
 *     (i1,m1), (i2,m2) when i1 = i2 -> m1 - m2
 *   | (i1,m1), (i2,m2) -> i1 - i2 *)
        
(* module ExprMem = Map.Make(struct
 *                      type t = int * int
 *                      let compare = compare_tuple
 *                    end) *)

module ExprMem = Map.Make(struct
                     type t = int 
                     let compare = (-)
                   end)

let memmap = ref ExprMem.empty
           
module LetMap = Map.Make(struct
                    type t = int
                    let compare = (-)
                  end)
let letmap = ref LetMap.empty

module DefMap = Map.Make(struct
                    type t = int
                    let compare = (-)
                  end)
let defmap = ref DefMap.empty

           
type simap_t = PC of (int * int) |
               SI of (int * int)


let num_queries = ref 0


let inc_num_queries () =
  num_queries := !num_queries + 1

let init_num_queries () =
  num_queries := 0

let get_num_queries () =
  !num_queries
  

let compare_simap v1 v2 =
  match v1, v2 with 
    PC (i1,m1), PC (i2,m2) when i1 = i2 -> m1 - m2
  | PC (i1,m1), PC (i2,m2) -> i1 - i2
  | SI (i1,m1), SI (i2,m2) when i1 = i2 -> m1 - m2
  | SI (i1,m1), SI (i2,m2) -> i1 - i2
  | PC (i1,m1), SI (i2,m2) -> -1
  | SI (i1,m1), PC (i2,m2) -> 1

module SiMap = Map.Make(struct
                    type t = simap_t
                    let compare = compare_simap
                  end)
                                                
let simap = ref SiMap.empty

let cfg = [("model", "true"); ("proof", "false"); ("timeout", "200000")]

let ctx = ref (mk_context cfg);;

Params.set_print_mode !ctx Z3enums.PRINT_SMTLIB2_COMPLIANT
          
(* dissable tmp file removal *)
let remove fil = if !Flags.no_clean then () else remove fil
                 
let print_exp exp =
  (match exp with
      | L e ->
         print_endline "print_exp: L e";
         print_endline (Expr.to_string e);
      | H (e1, e2) ->
         print_endline "print_exp: H (e1,e2)";
         print_endline (Expr.to_string e1);
         print_endline "e1";
         print_endline (Expr.to_string e2);
  )


let print_simpl sv = 
  match sv with
  | Z3Expr32 rt -> print_exp rt
  | Z3Expr64 rt -> print_exp rt
  | Sv sv -> print_endline (svalue_to_string sv)


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


let increase_one ctx ind =
  let bv = Expr.get_sort ind in
  let one = Expr.mk_numeral_int ctx 1 bv in
  BitVector.mk_add ctx ind one



let rec split_to_bytes ctx a ind value sz lo hi =
  if (sz == 0) then a
  else 
    (
      let val' = propagate_policy_one (BitVector.mk_extract ctx hi lo) value in
      let a' = propagate_policy_three (Z3Array.mk_store ctx) a ind val' in
      let ind' = propagate_policy_one (increase_one ctx) ind in
      split_to_bytes ctx a' ind' value (sz - 1) (lo+8) (hi+8)
    )

let merge_bytes ctx a ind sz =
  let rec merge_bytes_i ctx a ind sz value =
    if (sz == 0) then value
    else 
      (
        let lv = propagate_policy (Z3Array.mk_select ctx) a ind in
        let ind' = propagate_policy_one (increase_one ctx) ind in
        let value' = propagate_policy (BitVector.mk_concat ctx) lv value in
        merge_bytes_i ctx a ind' (sz - 1) value'
      )
  in  
  let lv = propagate_policy (Z3Array.mk_select ctx) a ind in
  (* print_endline "after_select"; *)
  let ind' = propagate_policy_one (increase_one ctx) ind in
  merge_bytes_i ctx a ind' (sz - 1) lv

let get_ext_size size = function
  | L v -> 
     let bv_size = BitVector.get_size (Expr.get_sort v) in
     size - bv_size
  | H (v1,v2) ->
     let bv_size1 = BitVector.get_size (Expr.get_sort v1) in
     let bv_size2 = BitVector.get_size (Expr.get_sort v2) in
     assert(bv_size1 == bv_size2);
     size - bv_size1

let extend ctx size v' = function
  | None -> v'
  | Some (Types.ZX) ->
     (* propagate_policy_one (BitVector.mk_zero_ext ctx 4) v' *)
     let size' = get_ext_size size v' in
     propagate_policy_one (BitVector.mk_zero_ext ctx  size') v'
  | Some (Types.SX) ->
     let size' = get_ext_size size v' in
     propagate_policy_one (BitVector.mk_sign_ext ctx  size') v'

(* Todo(Romy): remove obj.magic. *)
let simap_index v mem =
  let _, _, num = mem in 
  SI (Obj.magic v, num) (*(Obj.magic v,num)*)

let pcmap_index pc mem =
  let _, _, num = mem in
  let pcnum, _, _ = pc in 
  PC (pcnum, num ) (*pcnum,num)*)
(* let str = Printf.sprintf "%020d%020d" (Obj.magic v) (Obj.magic mem) in
   * str *)

let get_size e =
  match e with
  | L e ->
     let sort = Expr.get_sort e in
     BitVector.get_size sort
  | H (e1,e2) ->
     let sort1 = Expr.get_sort e1 in
     let sort2 = Expr.get_sort e1 in
     let size1 = BitVector.get_size sort1 in
     let size2 = BitVector.get_size sort2 in
     assert(size1 == size2);
     size1


(* let check_if_store_exists m s  =
 *   let s' = Obj.magic s in
 *   try
 *     let _ = ExprMem.find s' m in
 *     (m, false)
 *   with Not_found ->
 *         let m' = ExprMem.add s' true m in
 *         (m', true) *)
        

let to_int rt =
  match rt with
  | L v  when BitVector.is_bv_numeral v ->
       let str = BitVector.numeral_to_string v in
        print_endline str;
       Some (int_of_string str)
  | H (v1,v2) when v1 = v2  && BitVector.is_bv_numeral v1 -> 
       let str = BitVector.numeral_to_string v1 in
       Some (int_of_string str)
  | _ -> None



let rec create_array pc ctx a s =
  (*print_endline "update_mem";*)
  let size, index, value, sz = s in
  split_to_bytes ctx a index value sz 0 7

and mem_get_stores mi pc ctx mem s =
  (*print_endline "update_mem";*)
    (match s with
     | SI32 Store (ad, v, i, num, sz) ->
        let size = 32 in
        let index = si_to_expr pc size ctx mem ad in
        let value = si_to_expr pc size ctx mem v in
        (match to_int index with
         | Some i -> 
            (try
               let _ = ExprMem.find i mi in
               None, mi
             with Not_found ->
               let mi' = ExprMem.add i true mi in
               (Some (size,index, value, sz), mi')
            )
         | None ->
            (Some (size, index, value, sz), mi)
        )
     | SI64 Store (ad, v, i, num, sz) ->
        let size = 64 in
        let index = si_to_expr pc size ctx mem ad in
        let value = si_to_expr pc size ctx mem v in
        (match to_int index with
         | Some i -> 
            (try
               let _ = ExprMem.find i mi in
               None, mi
             with Not_found ->
               let mi' = ExprMem.add i true mi in
               (Some (size,index, value, sz), mi')
            )
         | None ->
            (Some (size, index, value, sz), mi)
        )

     | _ -> failwith "Unexpected store - not implemented f64/32"
    )

and update_mem pc ctx mem a s =
  (*print_endline "update_mem";*)
  match s with
  | SI32 Store (ad, v, i, num, sz) ->
     let size = 32 in
     let index = si_to_expr pc size ctx mem ad in
     let value = si_to_expr pc size ctx mem v in
     split_to_bytes ctx a index value sz 0 7
  | SI64 Store (ad, v, i, num, sz) ->
     let size = 64 in
     let index = si_to_expr pc size ctx mem ad in
     let value = si_to_expr pc size ctx mem v in
     split_to_bytes ctx a index value sz 0 7
   | _ -> failwith "Unexpected store - not implemented f64/32"
        
and si_to_expr pc size ctx mem si: rel_type  = 
  let si' = 
      (match si with
       | BitVec (i,n) ->
          L (BitVector.mk_numeral ctx (Int64.to_string i) n)
       | Const (High i, size) ->
          (try
             DefMap.find i !defmap
           with Not_found -> 
             let def = H (BitVector.mk_const_s ctx ("h1_" ^ string_of_int i) size,
                          BitVector.mk_const_s ctx ("h2_" ^ string_of_int i) size) in
             defmap := DefMap.add i def !defmap;
             def
          )
       | Const (Low i, size) ->
          (try
             DefMap.find i !defmap
           with Not_found -> 
             let def = L (BitVector.mk_const_s ctx ("l_" ^ string_of_int i) size ) in
             defmap := DefMap.add i def !defmap;
             def
          )
       | App (f, ts) ->
          (* print_endline "app"; *)
           (*let index = simap_index si mem in
           (try
             SiMap.find index !simap
            with Not_found -> *)
             let res = app_to_expr pc ts size ctx mem f in
             (*let simp = propagate_policy_one (fun x -> Expr.simplify x None) res in
             (* print_endline "simplify_after"; *)
             (* print_exp simp; *)
             simap := SiMap.add (simap_index si mem) simp !simap;
 
             simp
           ) *)
             res
       | Let (i) ->
          (*print_endline "let z3_solver"; 
                print_endline (string_of_int i);
 *)
          (try
             let f = LetMap.find i !letmap in
             f
           with Not_found -> 
             match Pc_type.find_let pc i with
             | Sv sv' ->
                (*print_endline "not found let";*)
                let sv' = sv_to_expr pc sv' ctx mem in
                letmap := LetMap.add i sv' !letmap;
                sv'
             | Z3Expr32 e
               | Z3Expr64 e ->
                letmap := LetMap.add i e !letmap;
                e
          )
       | Load (i, memi, num, sz, _) ->
          (*print_endline "load z3_solver"; 
          print_endline (string_of_int memi);
          print_endline (term_to_string i);*)
          let rec get_stores tmem newmem mem optstores = 
            let index = Smemory.get_num tmem in
            (*print_endline ("memory: " ^ (string_of_int index)); *)
            (try
               let nm = ExprMem.find index !memmap in
                (*print_endline "Found";*)
               nm
             with Not_found ->
                (*print_endline "Not Found";*)
               let stores = Smemory.get_stores tmem in

                (*  List.iter (fun st -> print_endline (svalue_to_string st)) stores;*)
               (* let optstores', noexists = List.fold_left check_if_store_exists
                *                              optstores stores in *)
               let optstores', stores' =
                 List.fold_left
                   (fun (mi,acc) st ->
                     let si,mi' = mem_get_stores mi pc ctx mem st in
                     match si with
                     | Some si -> (mi', si::acc)
                     | None -> (mi', acc)
                   )
                   (optstores,[]) stores in

            (*print_endline ("memory': " ^ (string_of_int index));*)
                 (* List.iter (fun (s,ind,v,sz) -> print_exp ind) stores';*)

               let prev_mem = Smemory.get_prev_mem tmem in
               
               let mem' =
                 match prev_mem with
                 | Some pmem ->
                    let newmem' = get_stores pmem newmem mem optstores' in
                    List.fold_left (create_array pc ctx)
                      newmem' stores'
                    
                 | None -> 
                    List.fold_left (create_array pc ctx)
                      newmem stores'
               in
(*      let params = Params.mk_params ctx in
      Params.add_bool params (Symbol.mk_string ctx "sort_store") true;

*)
               let simp = propagate_policy_one (fun x -> Expr.simplify x None) mem' in
               memmap := ExprMem.add index simp !memmap;
               simp
            )
          in
          (try
             let index = simap_index si mem in
             (* if !Flags.debug then print_endline ("lloc:" ^ index); *)
             let f = SiMap.find index !simap in
             (* if !Flags.debug then (print_endline "found load";); *)
             f
           with Not_found ->
             (* if !Flags.debug then (print_endline "not found load";); *)
             let smem, memlen, _ = mem in
             (*let index = Obj.magic smem in*)
             (* let index = (num,memi) in *)
             let arr =
               (* (try
                *    let nm = ExprMem.find index !memmap in
                *    (\* if !Flags.debug then (print_endline "found mem";);
                *     * print_endline (term_to_string si);
                *     * print_endline (string_of_int memi);
                *     * print_endline (string_of_int (num)); *\)
                *    (\* raise Not_found; *\)
                *    nm *)
                (* with Not_found -> *)
                  (* if !Flags.debug then (print_endline "not found mem";); *)
                  let bva = BitVector.mk_sort ctx 32 in
                  let bvd = BitVector.mk_sort ctx 8 in
                  let arr1 = Z3Array.mk_const_s ctx "mem1" bva bvd in
                  let arr2 = Z3Array.mk_const_s ctx "mem2" bva bvd in
                  let newmem = H (arr1, arr2) in
                  let tmem = Lib.List32.nth smem (Int32.of_int (memlen - memi)) in
                    (*print_endline "nth_end";*)
                  (*let stores = Smemory.get_stores tmem in*)
                  (*print_endline ("number stores: " ^ (string_of_int (List.length stores)));*)
                  (*List.iter (fun st -> print_endline (svalue_to_string st)) stores;*)
                  (* * if (List.length stores > 0) then (
                   *   print_endline (term_to_string si);
                   *   print_endline (string_of_int memi);
                   *   print_endline (string_of_int (num));
                   * ); *)
                  let fmem = get_stores tmem newmem mem (ExprMem.empty) in
                
                  (* let stores = Smemory.get_stores tmem in
                   * let fmem = List.fold_left (update_mem pc ctx mem)
                   *              newmem (List.rev stores) in
                   * memmap := ExprMem.add index fmem !memmap; *)
                  (* memmap := ExprMem.add (num,memi) fmem !memmap; *)
                  fmem
               (* ) *)
             in
             (*if !Flags.debug then (print_endline "getting index";);*)
             let index = si_to_expr pc size ctx mem i in
             (*if !Flags.debug then (print_endline "after"; print_exp index;);*)
             let v' = merge_bytes ctx arr index sz in
             (* print_endline "simplify"; *)
             let simp = propagate_policy_one (fun x -> Expr.simplify x None) v' in
             (* print_endline "simplify_after"; *)
             (* print_exp simp; *)
             simap := SiMap.add (simap_index si mem) simp !simap;
             simp )
         
       (* let v'' = extend ctx size v' ext in *)
          (* let v''' = (match v'' with
           *             | L v'' 
           *             | H (v'',_) -> v'') in
           * let bv = Expr.get_sort v''' in
           * let s = BitVector.get_size bv in
           * print_endline "z3_solver: load";
           * term_to_string i |> print_endline;
           * print_endline (string_of_int sz);
           * print_endline (string_of_int size);
           * (match ext with
           *  | None -> print_endline "None";
           *  | Some Types.SX -> print_endline "sx";
           *  | Some Types.ZX -> print_endline "zx";
           * );
           * print_endline "final size";
           * print_endline (string_of_int s);
           * v'' *)
       (* propagate_policy (Z3Array.mk_select ctx) fmem index *)
       (* index *)
       | _ -> failwith "String, Int, Float, Let, Multi are not implemented yet."
      ) in
    (* simap := SiMap.add (Obj.magic si) si' !simap; *)
    (* print_endline "end_of_si_expr"; *)
    si'
  
and app_to_expr pc ts size ctx mem f =
  (* print_endline "app_to_expr"; *)
  match f, ts with
  | Ite, t1::t2::t3::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     let e3 = si_to_expr pc size ctx mem t3 in
     propagate_policy_three (Boolean.mk_ite ctx) e1 e2 e3
  | Ite, _ -> failwith "Not valid ite."

  | BvSlt, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_slt ctx) e1 e2
  | BvSlt, _ -> failwith "Not valid slt."

  | BvSle, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_sle ctx) e1 e2
  | BvSle, _ -> failwith "Not valid sle."

  | BvSgt, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_sgt ctx) e1 e2
  | BvSgt, _ -> failwith "Not valid sgt."

  | BvSge, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_sge ctx) e1 e2
  | BvSge, _ -> failwith "Not valid sge."

  | BvUlt, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_ult ctx) e1 e2
  | BvUlt, _ -> failwith "Not valid ult."

  | BvUle, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_ule ctx) e1 e2
  | BvUle, _ -> failwith "Not valid ule."

  | BvUgt, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_ugt ctx) e1 e2
  | BvUgt, _ -> failwith "Not valid ugt."

  | BvUge, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_uge ctx) e1 e2
  | BvUge, _ -> failwith "Not valid uge."

  | BvNot, t::[] ->
     let e = si_to_expr pc size ctx mem t in
     propagate_policy_one (BitVector.mk_not ctx) e
  | BvNot, _ -> failwith "Not valid not."

  | BvNeg, t::[] ->
     let e = si_to_expr pc size ctx mem t in
     propagate_policy_one (BitVector.mk_neg ctx) e
  | BvNeg, _ -> failwith "Not valid neg."

  | BvAnd, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_and ctx) e1 e2
  | BvAnd, _ -> failwith "Not valid bitwise and."

  | BvOr, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_or ctx) e1 e2
  | BvOr, _ -> failwith "Not valid bitwise or."

  | BvNand, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_nand ctx) e1 e2
  | BvNand, _ -> failwith "Not valid bitwise nand."

  | BvNor, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_nor ctx) e1 e2
  | BvNor, _ -> failwith "Not valid bitwise nor."

  | BvXNor, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_xnor ctx) e1 e2
  | BvXNor, _ -> failwith "Not valid bitwise xnor."

  | BvXor, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_xor ctx) e1 e2
  | BvXor, _ -> failwith "Not valid bitwise xor."
               
  | BvAdd, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_add ctx) e1 e2
  | BvAdd, ts ->
     (* List.iter (fun t -> print_endline (Smt_type.term_to_string t)) ts; *) 
     failwith "Not valid bitwise addition." 

  | BvSub, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_sub ctx) e1 e2
  | BvSub, _ -> failwith "Not valid bitwise subtraction."

  | BvMul, t1::t2::[] ->
     (* print_endline "mk_mul"; *)
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     (* let e1' = match e1 with
      *   | L e1' -> e1'
      *   | H (e1',_) -> e1'
      * in
      * let e2' = match e2 with
      *   | L e2' -> e2'
      *   | H (e2',_) -> e2'
      * in
      * (try
      *      let e1s = Expr.get_sort e1' in 
      *      BitVector.get_size e1s |> string_of_int |> print_endline;
      *      let e2s = Expr.get_sort e2' in 
      *      BitVector.get_size e2s |> string_of_int |> print_endline;
      * with _ -> print_endline "try failed"); *)
     (* (try *)
     propagate_policy (BitVector.mk_mul ctx) e1 e2
      (* with _ ->
      *    print_endline "failure";
      *    print_endline (string_of_int size);
      *    term_to_string t1 |> print_endline;
      *    term_to_string t2 |> print_endline;
      *    failwith "failure";
      * ) *)
  | BvMul, _ -> failwith "Not valid bitwise multiplication."

  | BvURem, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_urem ctx) e1 e2
  | BvURem, _ -> failwith "Not valid bitwise uremainder."

  | BvSRem, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_srem ctx) e1 e2
  | BvSRem, _ -> failwith "Not valid bitwise sremainder."

  | BvSMod, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_smod ctx) e1 e2
  | BvSMod, _ -> failwith "Not valid bitwise s modulo."

  | BvShl, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_shl ctx) e1 e2
  | BvShl, _ -> failwith "Not valid bitwise sremainder."

  | BvLShr, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_lshr ctx) e1 e2
  | BvLShr, _ -> failwith "Not valid bitwise sremainder."

  | BvAShr, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_ashr ctx) e1 e2
  | BvAShr, _ -> failwith "Not valid bitwise sremainder."

  (*TODO(Romy): special cases for constant shift *)
  | Rotl, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_ext_rotate_left ctx) e1 e2
  | Rotl, _ -> failwith "Not valid bitwise rotl."

  | Rotr, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_ext_rotate_right ctx) e1 e2
  | Rotr, _ -> failwith "Not valid bitwise rotr."

  | Rotli(i), t::[] ->
     let e = si_to_expr pc size ctx mem t in
     propagate_policy_one (BitVector.mk_rotate_left ctx i) e
  | Rotli _, _ -> failwith "Not valid bitwise rotl."

  | Rotri(i), t::[] ->
     let e = si_to_expr pc size ctx mem t in
     propagate_policy_one (BitVector.mk_rotate_right ctx i) e
  | Rotri _, _ -> failwith "Not valid bitwise rotl."

  | ExtendS(i), t::[] ->
     let e = si_to_expr pc size ctx mem t in
     let size = get_size e in
     propagate_policy_one (BitVector.mk_sign_ext ctx (i-size)) e
  | ExtendS _, _ -> failwith "Not valid bitwise extsl."

  | ExtendU(i), t::[] ->
     let e = si_to_expr pc size ctx mem t in
     let size = get_size e in
     propagate_policy_one (BitVector.mk_zero_ext ctx (i-size)) e
  | ExtendU _, _ -> failwith "Not valid bitwise extul."

  (* Should be *)
  | Wrap(i), t::[] ->
     let e = si_to_expr pc size ctx mem t in
     (* let size = get_size e in   (\*  *\) *)
     propagate_policy_one (BitVector.mk_extract ctx 31 0) e
  | Wrap _, _ -> failwith "Not valid bitwise rotl."

  | BvUDiv, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_udiv ctx) e1 e2
  | BvUDiv, _ -> failwith "Not valid bitwise sremainder."

  | BvSDiv, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (BitVector.mk_sdiv ctx) e1 e2
  | BvSDiv, _ -> failwith "Not valid bitwise sremainder."

  | Eq, t1::t2::[] ->
     let e1 = si_to_expr pc size ctx mem t1 in
     let e2 = si_to_expr pc size ctx mem t2 in
     propagate_policy (Boolean.mk_eq ctx) e1 e2
  | Eq, _ -> failwith "Not valid equation."

  | Not, t::[] ->
     let e = si_to_expr pc size ctx mem t in
     propagate_policy_one (Boolean.mk_not ctx) e
  | Not, _ -> failwith "Not valid boolean not."

  (* | RedOr, t::[] ->
   *    let e = si_to_expr pc size ctx mem t in
   *    propagate_policy_one (Boolean.mk_redor ctx) e
   * | RedOr, _ -> failwith "Not valid boolean redor." *)


  | And, ts ->
     let es = List.map (si_to_expr pc size ctx mem) ts in
     propagate_list (Boolean.mk_and ctx) es 
  | Or, ts ->
     let es = List.map (si_to_expr pc size ctx mem) ts in
     propagate_list (Boolean.mk_or ctx) es 
  | _ -> failwith "App_to_expr: Not implemented yet."

and sv_to_expr pc sv ctx mem =
  (*print_endline "sv_to_expr";
  print_endline (svalue_to_string sv);*)
  let v,n =
    match sv with
    | SI32 si32 -> si32,32
    | SI64 si64 -> si64,64 
  (*TODO(Romy): Not implemented*)
  | _ -> failwith "Float not implemented."
  in
  (* (try
     let index = simap_index v mem in
     (* if !Flags.debug then print_endline ("svloc:" ^ index); *)
     let f =  SiMap.find index !simap in
     (*if !Flags.debug then print_endline "found sv_to_expr"; *)
     (* print_exp f; *)
     (* raise Not_found; *)
     f 
   with Not_found ->
     (*if !Flags.debug then print_endline "not found sv_to_expr"; *)
         (* if !Flags.debug then (
          *   print_endline "notfound sv_to_expr";
          *   (\* print_endline (svalue_to_string sv); *\)
          * ); *)*)
         let v' = si_to_expr pc n ctx mem v in
         (* print_endline "sv_to_expr before simp"; *)
         (*let simp = propagate_policy_one (fun x -> Expr.simplify x None) v' in
         (* print_endline "sv_to_expr after simp"; *)
         simap := SiMap.add (simap_index v mem) simp !simap;
         (* print_endline "sv_to_expr simp end"; *)
         simp)*)
    v'



let rec pc_to_expr pcext ctx mem: rel_type =
  (* print_endline "pc_to_expr"; *)
  (* print_endline (print_pc (snd pcext)); *)
  let pcnum, pclet, pc = pcext in
  let index = pcmap_index pcext mem in
  try

    (* let _, _, num = mem in
     * print_endline ("pcnum" ^ (string_of_int pcnum));
     * print_endline ("memnum" ^ (string_of_int num)); *)
    (* if !Flags.debug then print_endline ("pcloc:" ^ index); *)
    let f = SiMap.find index !simap in
    (* if !Flags.debug then print_endline "found pc_to_expr"; *)
    (* f *)
    (* print_exp f; *)
    f
    (* raise Not_found *)
  with Not_found -> (
    match pc with
    | PCTrue -> L (Boolean.mk_true ctx)
    | PCFalse -> L (Boolean.mk_false ctx)
    | PCExpr e -> e
    | PCAnd (sv, pc') ->
       let ex1 = sv_to_expr (pcnum, pclet,pc) sv ctx mem in
       let ex2 = pc_to_expr pc' ctx mem in
       let pcexp = propagate_list (Boolean.mk_and ctx) [ex1; ex2] in
       let simp = propagate_policy_one (fun x -> Expr.simplify x None) pcexp in
       simap := SiMap.add index simp !simap ; 
       simp
    | PCOr (pc', pc'') ->
       let ex1 = pc_to_expr pc' ctx mem in
       let ex2 = pc_to_expr pc'' ctx mem in
       let pcexp = propagate_list (Boolean.mk_or ctx) [ex1; ex2] in
       let simp = propagate_policy_one (fun x -> Expr.simplify x None) pcexp in
       simap := SiMap.add index simp !simap ; 
       simp

  )

let create_mem ctx size =
  let bv = BitVector.mk_sort ctx size in
  Z3Array.mk_const_s ctx  "mem" bv bv

let clean_solver () =
  ctx := mk_context cfg;
  Params.set_print_mode !ctx Z3enums.PRINT_SMTLIB2_COMPLIANT;
  memmap := ExprMem.empty;
  letmap := LetMap.empty;
  defmap := DefMap.empty;
  simap := SiMap.empty;
  init_num_queries ()

  
  
let init_solver () =
  (*memmap := ExprMem.empty;*)
  if !Flags.stats then
      inc_num_queries ();
  !ctx

let bin_of_string str =
  let len = String.length str in
  if len < 3 then failwith "Bitvector.of_string : too short string" else
    try
      let num = Big_int.big_int_of_string str in
      Big_int.int64_of_big_int num 
    with Failure _ -> raise (Invalid_argument ("of_string : " ^ str))



let find_sv cmds solver =  
  let rec find_command = function
    | h::tl ->
       let cd = h.command_desc in
       (match cd with
        | Smtlib.CmdDefineFun fd ->
           let FunDef (symb, sort_option, sorted_vars, sort, term) = fd.fun_def_desc in
           (* Smtlib_pp.pp_symbol Format.std_formatter symb;
            * Smtlib_pp.pp_term Format.std_formatter term;
            * print_endline "done"; *)

           if (match symb.symbol_desc with
               | SimpleSymbol s when s = "sv" -> true
               | _ -> false)
           then (
             (match term.term_desc with
              | TermSpecConstant cst ->
                    (match cst with 
                     | CstBinary str ->
                         let b64 = bin_of_string ("0b" ^ str) in
                         b64
                     | CstHexadecimal str ->
                         let b64 = bin_of_string ("0x" ^ str) in
                         b64
                     | _ -> 
                         print_endline "unknown constant";
                         failwith "Unknown constant");
 
              | _ -> 
                 print_endline "unknown term desc";
                 Smtlib_pp.pp_symbol Format.std_formatter symb;
                 Smtlib_pp.pp_term Format.std_formatter term;
                 (* print_endline "after prints"; *)
                 failwith "Unknown term desc")
           ) else 
             find_command tl
        | _ ->
           (* print_endline "No assert cmd"; *)
           find_command tl
       );
    | [] -> failwith "Not found"
  in
  (* if !Flags.debug then
   *   print_endline solver; *)
  find_command cmds
        
let read_cvc4 fname =
  (* print_endline "read_cvc4"; *)
  let tmp_file = fname ^ ".cvc4.out" in
  (* let _ = Sys.command @@ "cvc4-1.8-x86_64-linux-opt -m /tmp/out.smt2 > " ^ tmp_file in *)
  let chan = open_in tmp_file in
  (* let ch = input_char chan in *)
  match input_line chan with
  | "unsat" -> 
        close_in chan;
        None
  | "unknown" -> 
        close_in chan;
        None
  | "sat" ->
     let lexbuf = Lexing.from_channel chan in
     let c =
       (try
          let m = Smtlib_parser.model Smtlib_lexer.token lexbuf in
          let mc = m.model_commands in
          close_in chan;
          find_sv mc tmp_file
        with e ->
          close_in chan;
          print_endline "failed cvc4";
          raise e
       ) in
     Some c
    | _ -> failwith @@ "Error output of file " ^ tmp_file

let read_boolector fname =
  (* print_endline "read_boolector"; *)
  let tmp_file = fname ^ ".boolector.out" in
  let chan = open_in tmp_file in
  match input_line chan with
  | "unsat" -> 
        close_in chan;
        None
  | "unknown" -> 
        close_in chan;
        None
  | "sat" ->
     let lexbuf = Lexing.from_channel chan in
     let c =
       (try
          let m = Smtlib_parser.model Smtlib_lexer.token lexbuf in
          let mc = m.model_commands in
          close_in chan;
          find_sv mc tmp_file
        with e ->
          close_in chan;
          print_endline "failed boolector";
          raise e
       ) in
     Some c
    | _ -> failwith @@ "Error output of file " ^ tmp_file

let read_bitwuzla fname =
  (* print_endline "read_boolector"; *)
  let tmp_file = fname ^ ".bitwuzla.out" in
  let chan = open_in tmp_file in
  match input_line chan with
  | "unsat" -> 
        close_in chan;
        None
  | "unknown" -> 
        close_in chan;
        None
  | "sat" ->
     let lexbuf = Lexing.from_channel chan in
     let c =
       (try
          let m = Smtlib_parser.model Smtlib_lexer.token lexbuf in
          let mc = m.model_commands in
          close_in chan;
          find_sv mc tmp_file
        with e ->
          close_in chan;
          print_endline "failed bitwuzla";
          raise e
       ) in
     Some c
    | _ -> failwith @@ "Error output of file " ^ tmp_file

         
         
let read_z3 fname =
  (* print_endline "read_z3"; *)
  let tmp_file = fname ^ ".z3.out" in
  (* let _ = Sys.command @@ "z3 -smt2 MODEL=true /tmp/out.smt2 > " ^ tmp_file in *)
  let chan = open_in tmp_file in
  match input_line chan with
  | "unsat" -> 
    close_in chan;
    None
  | "unknown" -> 
    close_in chan;
    None
  | "sat" ->
     let lexbuf = Lexing.from_channel chan in
     let c =
       (try
          let m = Smtlib_parser.model Smtlib_lexer.token lexbuf in
          (* print_endline "parser"; *)
          let mc = m.model_commands in
          (* print_endline "before close_in"; *)
          close_in chan;
          (* print_endline "after close_in"; *)
          find_sv mc tmp_file
        with e ->
          close_in chan;
          print_endline "failed z3"; 
          raise e
       ) in
     (* close_in chan; *)
     Some c
  | _ -> failwith @@ "Error output of file " ^ tmp_file

let read_yices fname =
  (* print_endline "read_yices"; *)
  let rec find_sv_solution lst =
    match lst with
    | ("sv",v)::lst -> v
    |  _ :: lst -> find_sv_solution lst 
    | [] -> print_endline "Not found";
            failwith "Not foujnd sv"
  in
  let tmp_file = fname ^ ".yices.out" in
  (* let _ = Sys.command @@ "yices-smt2 /tmp/out.smt2 > " ^ tmp_file in *)
  let chan = open_in tmp_file in
  match input_line chan with
  | "unsat" 
    | "unknown" -> 
     close_in chan;
     None
  | "sat" ->
     (*print_endline (input_line chan);*)
     let lexbuf = Lexing.from_channel chan in
     (try
        let parse = Smt2_parser.model Smt2_lexer.token lexbuf in
        match  parse with
        | Smtlib.Sat lst ->
           (* print_endline "test binary to string sat"; *)
           let strnum = find_sv_solution lst in
           let num = bin_of_string ("0b" ^ strnum) in
           (* print_endline "after binary to string sat"; *)
           close_in chan;
           (* print_endline "after close chan"; *)
           Some num
      with e ->
        close_in chan;
        print_endline "Yices error";
        raise e
     )
  | _ -> failwith @@ "Error output of file " ^ tmp_file
  (* print_endline "returning"; *)
  (* exit 0 *)

let read_sat solver_name fname =
  let tmp_file = fname ^ "." ^ solver_name ^ ".out" in
  let chan = open_in tmp_file in
  let result = input_line chan in
  let ret =
    match  result with
    | "unsat" -> false
    | "unknown" -> true
    | "sat" -> true
    | _ ->
       close_in chan;
       failwith @@ "Unknown result from " ^ solver_name ^ " returns: " ^ result 
  in
  close_in chan;
  ret


let run_solvers ?model:(model=true) input_file yices z3 cvc4 boolector bitwuzla timeout =
  (* print_endline ("run_solvers: " ^ input_file); *)
  try
    let out_file = input_file ^ ".run_solvers.out" in
    let err_file = input_file ^ ".run_solvers.err" in

    let start = if !Flags.stats then Unix.gettimeofday () else 0.0 in
    
    (*let timeout_str = if timeout then " timeout -s SIGKILL 10m " else "" in*)
    let timeout_str = if timeout > 0 then " timeout " ^ string_of_int timeout ^ "s " else "" in
    let portfolio_script = if model then  "run_solvers.sh" else "run_solvers_no_model.sh" in
    let rc = Sys.command @@ timeout_str ^ " bash " ^  !path ^ portfolio_script ^ " " ^
                             input_file ^ " 1> " ^ out_file ^ " 2> " ^ err_file in
    (*if (rc == 137) then (*for SIGKILL*) *)
    if (rc == 124) then (
      if !Flags.debug then
          print_endline "Time out";
      raise Timeout;
    );

    let chan = open_in out_file in
    try
      let solver = input_line chan in
      close_in chan;
      remove out_file;
      if solver = "yices" then (
        if (!Flags.stats) then (
          Stats.update_query_time (Unix.gettimeofday () -. start);
          stats := {!stats with yices = !stats.yices + 1 };
          Stats.update_query_str "Yices";
          Stats.print_last();
        );
        yices input_file
      )
      else if solver = "z3" then (
        if (!Flags.stats) then (
          Stats.update_query_time (Unix.gettimeofday () -. start);
          stats := {!stats with z3 = !stats.z3 + 1 };
          Stats.update_query_str "Z3";
          Stats.print_last();
        );
        z3 input_file
      )
      else if solver = "cvc4" then (
        if (!Flags.stats) then (
          Stats.update_query_time (Unix.gettimeofday () -. start);
          stats := {!stats with cvc4 = !stats.cvc4 + 1 };
          Stats.update_query_str "CVC4";
          Stats.print_last();
        );
        cvc4 input_file
      )
      else if solver = "boolector" then (
        if (!Flags.stats) then (
          Stats.update_query_time (Unix.gettimeofday () -. start);
          stats := {!stats with boolector = !stats.boolector + 1 };
          Stats.update_query_str "Boolector";
          Stats.print_last();
        );
        boolector input_file
      )
      else if solver = "bitwuzla" then (
        if (!Flags.stats) then (
          Stats.update_query_time (Unix.gettimeofday () -. start);
          stats := {!stats with bitwuzla = !stats.bitwuzla + 1 };
          Stats.update_query_str "Bitwuzla";
          Stats.print_last();
        );
        bitwuzla input_file
      )

      else
        failwith "No solver returned";
    with e ->
      close_in chan;
      print_endline ("Solver error " ^ input_file);
      let chan = open_in err_file in
      print_endline (input_line chan);
      raise e
  with e ->
    if !Flags.debug then 
        print_endline "failed";
    raise e
  (* match fork() with
   * | 0 -> run_cvc4()
   * | pid_yices ->
   *    (
   *      (\* match fork() with
   *       * | 0 -> run_cvc4()
   *       * | pid_cvc4 -> *\)
   * 
   *         (match fork() with
   *          | 0 -> run_z3()
   *          | pid_z3 ->
   *             (match wait () with
   *              | (pid, WEXITED retcode) when pid = pid_yices->
   *                 print_endline "yices";
   *                 string_of_int retcode |> print_endline;
   *                 print_endline @@ "Killing z3 " ^ string_of_int pid_z3;
   *                 kill_children pid_z3 sigkill;
   *              | (pid, WEXITED retcode) when pid = pid_z3->
   *                 print_endline "z3 terminated";
   *                 string_of_int retcode |> print_endline;
   *                 print_endline "Killing yices";
   *                 kill_children pid_yices sigkill;
   *              | (pid, _) when pid = pid_z3 ->
   *                 print_endline "failed z3";
   *                 kill_children pid_yices sigkill;
   *                 kill_children pid_z3 sigkill;
   *              | (pid, _) when pid = pid_yices ->
   *                 print_endline "failed yices";
   *                 kill_children pid_yices sigkill;
   *                 kill_children pid_z3 sigkill;
   *              | _ ->
   *                 print_endline "failed all";
   *                 kill_children pid_yices sigkill;
   *                 kill_children pid_z3 sigkill;
   *             )
   *         )
   *    ) *)
(*4513*)
let write_formula_to_file ?model:(model=true) solver =
  let filename = Filename.temp_file "wasm_" ".smt2" in
  let oc = open_out filename in
  Printf.fprintf oc "(set-logic QF_ABV)\n";
  (*let _ = Solver.to_string solver in*)
  let st = Solver.to_string solver in
  Printf.fprintf oc "%s\n" st;
  Printf.fprintf oc "(check-sat)\n";
  if model then
    Printf.fprintf oc "(get-model)\n";
  close_out oc;
  filename


  
let find_solutions (sv: svalue) (pc : pc_ext)
      (mem: Smemory.t list * int * int) : int list =
  if !Flags.debug then
    print_endline "Finding solutions...";

  let start_t = if !Flags.debug then Unix.gettimeofday() else 0.0 in
  (* svalue_to_string sv |> print_endline; *)
  let ctx = init_solver() in
  (* print_endline "before sv_to_expr"; *)
  let v = sv_to_expr pc sv ctx mem in
  (* print_endline "after sv_to_expr"; *)

  if !Flags.debug then (
    let dt = Unix.gettimeofday () -. start_t in
    "Finding solutions time: " ^ (string_of_float dt) |> print_endline;
  );

  let size = Svalues.size_of sv in
  let v' = BitVector.mk_const_s ctx "sv" size in
  let vrec = 
      (match v with
       | L v ->  Boolean.mk_eq ctx v' v
       | H (v1,v2) -> Boolean.mk_eq ctx v' v1
      );
  in
  let pcex = pc_to_expr pc ctx mem in
 
  let rec find_solutions_i (sv: svalue) (pc : pc_ext)
            (mem: Smemory.t list * int * int) (acc: int64 list) : int64 list =
    if !Flags.debug then
         print_endline "Finding solutions internal...";

    let g = Goal.mk_goal ctx true false false in

    (* print_endline "find_solutions_i"; *)
    Goal.add g [vrec];
    let previous_values = List.map (fun i ->
                              let bv = Expr.get_sort v'  in
                              let old_val = Expr.mk_numeral_string ctx (Int64.to_string i) bv in
                              let eq = Boolean.mk_eq ctx old_val v' in
                              Boolean.mk_not ctx eq) acc in
    Goal.add g previous_values;
   (* print_endline "find_solutions_i_ after pc_to_expr"; *)
    (match pcex with
     | L v ->
        Goal.add g [v]
     | H (v1,v2) ->
        Goal.add g [v1]
    );

    let num_exprs = Goal.get_num_exprs g in
      
 
    if (!Flags.stats) then
       Stats.add_new_query "Unknown" (num_exprs) 0.0;
 
    (* Printf.printf "Goal: %s\n" (Goal.to_string g); *)
    let solver = Solver.mk_solver ctx None in
    List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);

    (* print_endline "creating filename"; *)
    let filename = write_formula_to_file solver in
    (* print_endline @@ "after writing formula to filename" ^ filename; *)
    let timeout = 0 in
    let ret = match run_solvers filename read_yices read_z3
                      read_cvc4 read_boolector read_bitwuzla timeout with
      | None -> acc
      | Some v -> 
        if !Flags.debug then(
            print_endline "Found_solution";
            print_endline (Int64.to_string v));
        find_solutions_i sv pc mem (v::acc)
    in
    remove filename;            (*  *)
    ret
  in


  let str = find_solutions_i sv pc mem [] in
  List.map (fun v -> Int64.to_int v) str

                            
let simplify (sv: svalue) (pc : pc_ext)
      (mem: Smemory.t list * int * int) : bool * simpl =
  if !Flags.debug then
        print_endline "Simplifying...";
  (* print_endline "simplify"; *)
  (* svalue_to_string sv |> print_endline; *)
  let ctx = init_solver() in

  let v = sv_to_expr pc sv ctx mem in
  (* print_endline (Expr.get_simplify_help ctx); *)
  let params = Params.mk_params ctx in
  (* print_endline (Params.to_string params); *)
  try
    match v with
    | L v ->
       let simp = Expr.simplify v (Some params) in
       (* Expr.to_string simp |> print_endline; *)
       if (BitVector.is_bv simp && Expr.is_numeral simp) then (
         let bvs = Expr.get_sort simp in
         let size = BitVector.get_size bvs in
         let v = Int64.of_string (BitVector.numeral_to_string simp) in
         if (size = 32) then
           true, Sv  (SI32 (Si32.bv_of_int v size))
         else if (size = 64) then
           true, Sv (SI64 (Si64.bv_of_int v size))
         else
           failwith ("Simplify: unknown size" ^ string_of_int size);
       ) else ( 
         (* print_endline "fail simplify L";
          * Expr.to_string v |> print_endline;
          * Expr.to_string simp |> print_endline;
          * svalue_to_string sv |> print_endline; *)
         (match sv with
         | SI32 _ -> (true, Z3Expr32 (L simp))
         | SI64 _ -> (true, Z3Expr64 (L simp))
         | SF32 _ -> failwith "Not implemented fi32"
         | SF64 _ -> failwith "Not implemented fi64"
         )
       )
    | H (v1,v2) ->
       let simp1 = Expr.simplify v1 (Some params) in
       let simp2 = Expr.simplify v2 (Some params) in
       if (BitVector.is_bv simp1 && Expr.is_numeral simp1 && Expr.equal simp1 simp2) then (
         let bvs = Expr.get_sort simp1 in
         let size = BitVector.get_size bvs in
         let v = Int64.of_string (BitVector.numeral_to_string simp1) in
         if (size = 32) then
           true, Sv (SI32 (Si32.bv_of_int v size))
         else if (size = 64) then
           true, Sv (SI64 (Si64.bv_of_int v size))
         else
           failwith ("Simplify: unknown size" ^ string_of_int size);
       ) else (
         (* print_endline "fail simplify H";
          * Expr.to_string v1 |> print_endline;
          * Expr.to_string simp1 |> print_endline;
          * svalue_to_string sv |> print_endline; *)
         (match sv with
         | SI32 _ -> (true, Z3Expr32 (H (simp1,simp2)))
         | SI64 _ -> (true, Z3Expr64 (H (simp1,simp2)))
         | SF32 _ -> failwith "Not implemented fi32"
         | SF64 _ -> failwith "Not implemented fi64"
         )
       )
  with _ -> (false, Sv sv)


let simplify_pc (pc : pc_ext)
      (mem: Smemory.t list * int * int) : bool * pc_ext =
  if !Flags.debug then
        print_endline "Simplifying pc...";
 
  let ctx = init_solver() in
  let pc_exp = pc_to_expr pc ctx mem in
  let params = Params.mk_params ctx in
  let pcnum,pclet, _ = pc in
  (* Params.add_int params (Symbol.mk_string ctx "max_steps") 10000000; *)
  (* print_endline (Params.to_string params); *)
  try
    match pc_exp with
    | L pce ->
       let simp = Expr.simplify pce (Some params) in
       (true, (pcnum, pclet, PCExpr (L simp)))
    | H (v1,v2) ->
       let simp1 = Expr.simplify v1 (Some params) in
       let simp2 = Expr.simplify v2 (Some params) in
       (true, (pcnum, pclet, PCExpr (H (simp1, simp2))))
  with _ -> (false, pc)

          
(* Not Used currently
let is_unsat (pc : pc_ext) (mem: Smemory.t list * int) =
  (* print_endline "is_unsat"; *)
  let ctx = init_solver() in

  let pc = pc_to_expr pc ctx mem in

  let g = Goal.mk_goal ctx true false false in
  
  (match pc with
   | L p ->  Goal.add g [p ]
   | H (pc1,pc2) ->  Goal.add g [pc1 ]
  );
  (* Printf.printf "Goal: %s\n" (Goal.to_string g); *)
  let solver = Solver.mk_solver ctx None in
  List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);

  if !Flags.portfolio_only then (
    let filename = write_formula_to_file solver in
    let res = not (run_solvers filename (read_sat "yices")
                     (read_sat "z3") (read_sat "cvc4")
                     (read_sat "boolector")) in
    remove filename;
    res
  )
  else
    ( match (Solver.check solver []) with
      | Solver.UNSATISFIABLE ->
         true
      | _ ->
         (* let model = Solver.get_model solver in
          * (match model with
          *  | None -> print_endline "None"
          *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
          * ); *)
         false
    )
 *)
  
let is_ct_unsat ?timeout:(timeout=30) ?model:(model=false) (pc : pc_ext) (sv : svalue) (mem: Smemory.t list * int * int) =
  if !Flags.debug then (
       print_endline "Checking if conditional is CT..";
  );
  let start_t = if !Flags.debug then Unix.gettimeofday() else 0.0 in

  let ctx = init_solver() in

  let v = sv_to_expr pc sv ctx mem in
  let pc = pc_to_expr pc ctx mem in
  let g = Goal.mk_goal ctx true false false in

  if !Flags.debug then (
    let dt = Unix.gettimeofday () -. start_t in
    "Checking cond time: " ^ (string_of_float dt) |> print_endline;
  );

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


     
     let solver = Solver.mk_solver ctx None in
     List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);

     let num_exprs = Goal.get_num_exprs g in
     (* Some bug causes seg fault *)
     if (!Flags.stats) then
        Stats.add_new_query "Unknown" (num_exprs) 0.0;
 
     if !Flags.portfolio_only then (
       let filename = write_formula_to_file solver in
       let res = not (run_solvers filename (read_sat "yices")
                        (read_sat "z3") (read_sat "cvc4")
                        (read_sat "boolector") (read_sat "bitwuzla") timeout) in
       remove filename;
       res
     ) else if !Flags.z3_only then (
       (if (!Flags.stats) then
          Stats.update_query_str "Z3_bindings");
       let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in
       
       try 
       match (Solver.check solver []) with
       | Solver.UNSATISFIABLE ->
          (if (!Flags.stats) then (
             Stats.update_query_time (Unix.gettimeofday () -. start);
             Stats.print_last();
           )
          );
          true
       | _ ->
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last()
          );
          (* Printf.printf "Goal v_ct: %s\n" (Goal.to_string g); *)
          (* let model = Solver.get_model solver in *)
          (* (match model with
           *  | None -> print_endline "None"
           *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
           * ); *)
          false
       with _ ->
          if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last()
          );
          false
 
     ) else (
       if num_exprs > !Flags.magic_number_1 then (

         let filename = write_formula_to_file ~model:model solver in
         let timeout = 0 in
         let res = not (run_solvers ~model:model filename (read_sat "yices")
                          (read_sat "z3") (read_sat "cvc4")
                          (read_sat "boolector") (read_sat "bitwuzla") 
                          timeout) in
         remove filename;
         res
       ) else (
         (if (!Flags.stats) then
            Stats.update_query_str "Z3_bindings");
         let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in
         try
         match (Solver.check solver []) with
         | Solver.UNSATISFIABLE ->
          if (!Flags.stats) then (
                 Stats.update_query_time (Unix.gettimeofday () -. start);
                 Stats.print_last ();
               );
          true
         | _ ->
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          false
         with _ ->
          if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          false
 
       )
     )
     
let is_v_ct_unsat ?timeout:(timeout=30) ?model:(model=false) (pc : pc_ext) (sv : svalue)
      (mem: Smemory.t list * int * int) : bool =
   if !Flags.debug then (
      print_endline "Checking if value is CT..";
      print_endline ("Model: " ^ (string_of_bool model));
   );
 
  (* print_endline "is_v_ct_unsat"; *) 
  (* Pc_type.print_pc (snd pc) |> print_endline;
   * svalue_to_string sv |> print_endline; *)
   (* svalue_to_string sv |> print_endline; *)


  let start_t = if !Flags.debug then Unix.gettimeofday() else 0.0 in

  let ctx = init_solver() in

  (* List.iter print_endline (Tactic.get_tactic_names ctx); *)
  (* let tac = Tactic.mk_tactic ctx "default" in *)

  let g = Goal.mk_goal ctx true false false in
  (* print_endline "is_v_ct_unsat before sv"; *)
  let v = sv_to_expr pc sv ctx mem in

  if !Flags.debug then (
    let dt = Unix.gettimeofday () -. start_t in
    "Checking vct time: " ^ (string_of_float dt) |> print_endline;
  );


  (* let _,_,mnum = mem in
   * print_endline "is_v_ct_unsat after  sv";
   * (\* print_exp v; *\)
   * print_endline (string_of_int mnum); *)
 
  match v with
  | L v -> true
  | H (v1, v2) when Expr.equal v1 v2 -> true
  | H (v1, v2) ->
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

      let tac = Tactic.mk_tactic ctx "default" in

      let solver = Solver.mk_solver_t ctx tac in

      let num_exprs = Goal.get_num_exprs g in

      if (!Flags.stats) then (
         Stats.add_new_query "Unknown" (num_exprs) 0.0);
      let params = Params.mk_params ctx in
      (*Params.add_bool params (Symbol.mk_string ctx "sort_store") true;*)
      let s_formulas = (List.map (fun e -> Expr.simplify e (Some params)) (Goal.get_formulas g)) in

      List.iter (fun f -> Solver.add solver [f]) @@ List.rev s_formulas;

      (*Solver.add solver s_formulas;*)

      (* Printf.printf "Solver v_ct: %s\n" (Solver.to_string solver); *)
      if !Flags.portfolio_only then (

        let filename = write_formula_to_file ~model:model solver in
        let res = 
            try (
                not (run_solvers ~model:model filename (read_sat "yices")
                         (read_sat "z3")
                         (read_sat "cvc4") (read_sat "boolector")
                         (read_sat "bitwuzla") timeout)
            ) with Timeout -> (
                false
            )
        in
        remove filename;
        res
      ) else if !Flags.z3_only then (

        (if (!Flags.stats) then
           Stats.update_query_str "Z3_bindings") ;
        let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in
        (* print_endline "is_v_ct_unsat_before_solving"; *) 
        try
        match (Solver.check solver []) with
        | Solver.UNSATISFIABLE ->
           if (!Flags.stats) then (
             Stats.update_query_time (Unix.gettimeofday () -. start);
             Stats.print_last());
           true
        | Solver.SATISFIABLE ->
           if (!Flags.stats) then (
             Stats.update_query_time (Unix.gettimeofday () -. start);
             Stats.print_last()
           );
           (* let model = Solver.get_model solver in
            * (match model with
            *  | None -> print_endline "None"
            *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
            * ); *)
           false
        | _ ->
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          false
        with _ -> 
          if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          false
      ) else (
        if num_exprs > !Flags.magic_number_1 then (
          if !Flags.debug then print_endline "Using portfolio solver..";
 
          let filename = write_formula_to_file ~model:model solver in
          (* print_endline ("is_v_ct_unsat after write formula " ^ filename); *)
          let res = 
            try (
                not (run_solvers ~model:model filename (read_sat "yices") (read_sat "z3")
                           (read_sat "cvc4") (read_sat "boolector")
                           (read_sat "bitwuzla") timeout)
            )
            with Timeout -> false
          in
          remove filename;
          res
        ) else (

          if !Flags.debug then print_endline "Using Z3 solver..";

          (if (!Flags.stats) then 
             Stats.update_query_str "Z3_bindings") ;
          let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in
          (* print_endline "is_v_ct_unsat_before_solving"; *) 
          try
          match (Solver.check solver []) with
          | Solver.UNSATISFIABLE ->
             if (!Flags.stats) then (
               Stats.update_query_time (Unix.gettimeofday () -. start);
               Stats.print_last());
             true
          | Solver.SATISFIABLE ->
             if (!Flags.stats) then (
               Stats.update_query_time (Unix.gettimeofday () -. start);
               Stats.print_last());
             (* let model = Solver.get_model solver in
              * (match model with
              *  | None -> print_endline "None"
              *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
              * ); *)
             false
          | _ ->
             if (!Flags.stats) then (
               Stats.update_query_time (Unix.gettimeofday () -. start);
               Stats.print_last());
             false
          with _ -> 
             if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
             if (!Flags.stats) then (
               Stats.update_query_time (Unix.gettimeofday () -. start);
               Stats.print_last());
             false
        )
        
      )


      


let is_sat ?timeout:(timeout=30) (pc : pc_ext) (mem: Smemory.t list * int * int) : bool =
  if !Flags.debug then 
    print_endline "Checking satisfiability..";


  let start_t = if !Flags.debug then Unix.gettimeofday() else 0.0 in
  
  (* check only satisfiability *)
  (* print_endline "is_sat"; *)
  let ctx = init_solver() in
  let v = pc_to_expr pc ctx mem in

  if !Flags.debug then (
    let dt = Unix.gettimeofday () -. start_t in
    "Checking sat time: " ^ (string_of_float dt) |> print_endline;
  );

  (* print_endline (Expr.get_simplify_help ctx); *)
  (* print_endline "After pc_calc"; *)
  (* print_exp v; *)
  (* (match pc with
   * | (pclet, PCAnd (v',pc)) ->
   *    let sv = sv_to_expr (pclet,pc) v' ctx mem in
   *    print_endline "this";
   *    print_exp sv;              (\*  *\)
   * | _ -> print_endline "other"); *)
  let g = Goal.mk_goal ctx true false false in
  (match v with
   | L v when Boolean.is_true v -> true
   | L v when Boolean.is_false v -> false
   | H (v1,v2) when Boolean.is_false v1 && Boolean.is_false v2 -> false
   | H (v1,v2) when Boolean.is_true v1 && Boolean.is_true v2 -> true
   | _ ->
      let params = Params.mk_params ctx in
      Params.add_bool params (Symbol.mk_string ctx "sort_store") true;
      (match v with
       | L v -> 
            let v' = Expr.simplify v (Some params) in
            Goal.add g [v']
       | H (v1,v2) -> 
            let v1' = Expr.simplify v1 (Some params) in
            let v2' = Expr.simplify v2 (Some params) in
            Goal.add g [v1';v2']
      );
      (* Printf.printf "Goal: %s\n" (Goal.to_string g); *)
      (* if !Flags.debug then
       *   Printf.printf "Solver is_sat: %s\n" (Solver.to_string solver); *)
      (*let s_formulas = (List.map (fun e -> Expr.simplify e (Some params)) (Goal.get_formulas g)) in*)

      let solver = Solver.mk_solver ctx None in
      List.iter (fun f -> Solver.add solver [f]) (Goal.get_formulas g);

      let num_exprs = Goal.get_num_exprs g in
      
      (if (!Flags.stats) then
         Stats.add_new_query "Unknown" num_exprs 0.0);


      if !Flags.portfolio_only then (
        let filename = write_formula_to_file ~model:false solver in
        (* let timeout = 0 in *)
        let res =
          try ( 
            run_solvers ~model:false filename (read_sat "yices") (read_sat "z3")
              (read_sat "cvc4") (read_sat "boolector") 
              (read_sat "bitwuzla") timeout
          )
          with Timeout -> true
        in

        remove filename;
        res
      ) else if !Flags.z3_only then ( 

        (if (!Flags.stats) then
           Stats.update_query_str "Z3_bindings") ;
        let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in

        try    
        let check_solver = Solver.check solver [] in
        match check_solver with
        | Solver.SATISFIABLE ->
           if (!Flags.stats) then (
             Stats.update_query_time (Unix.gettimeofday () -. start);
             Stats.print_last()
           );
           (* let model = Solver.get_model solver in
            * (match model with
            *  | None -> print_endline "None"
            *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
            * ); *)
           true
        | _ ->
           if (!Flags.stats) then (
             Stats.update_query_time (Unix.gettimeofday () -. start);
             Stats.print_last()
           );
           false
        with _ -> 
          if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last()
          );
          false
 
      ) else (
        if  num_exprs > !Flags.magic_number_2  then (
          let filename = write_formula_to_file ~model:false solver in
          if !Flags.debug then
            print_endline ("is_sat after write formula " ^ filename); 
          
          (* print_endline ("mnumber" ^ (string_of_int num_exprs) ^ "," ^ filename); *)
          (* let timeout = 0 in *)
          let res = 
            try ( 
              run_solvers ~model:false filename (read_sat "yices") (read_sat "z3")
                (read_sat "cvc4") (read_sat "boolector") 
                (read_sat "bitwuzla") timeout
            )
            with Timeout -> true
          in
          (* let res = run_solvers filename (read_sat "yices") (read_sat "z3")
           *             (read_sat "cvc4") (read_sat "boolector") (read_sat "bitwuzla") timeout in *)
          remove filename;
          res
        ) else (
          (* print_endline ("Z3 bindings" ^ (string_of_int num_exprs)); *)
          (if (!Flags.stats) then
             Stats.update_query_str "Z3_bindings") ;
          let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in

          try
          let check_solver = Solver.check solver [] in
          match check_solver with
          | Solver.SATISFIABLE ->
             if (!Flags.stats) then (
               Stats.update_query_time (Unix.gettimeofday () -. start);
               Stats.print_last());
             true
          | _ ->
             if (!Flags.stats) then (
               Stats.update_query_time (Unix.gettimeofday () -. start);
               Stats.print_last());
             false
          with _ -> 
             if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
             if (!Flags.stats) then (
               Stats.update_query_time (Unix.gettimeofday () -. start);
               Stats.print_last());
             false
 
        )
      )
  )
  (* )
   * else (
   *   if num_exprs > magic_number then (
   *     let filename = write_formula_to_file solver in
   *     let res = run_solvers filename (read_sat "yices") (read_sat "z3")
   *                 (read_sat "cvc4") (read_sat "boolector") in
   *     remove filename;
   *     res
   *   ) else  (
   *     (if (!Flags.stats) then
   *        Stats.update_query_str "Z3_bindings") ;
   * 
   *     let check_solver = Solver.check solver [] in
   *     match check_solver with
   *     | Solver.SATISFIABLE -> true
   *     | _ -> false
   *   )
   * ) *)

       


              
let max = Optimize.maximize
let min = Optimize.minimize


let optimize (f : Z3.Optimize.optimize -> Z3.Expr.expr -> Z3.Optimize.handle)
      (pc : pc_ext) (mem: Smemory.t list * int * int) (sv : svalue)  =
  if !Flags.debug then
        print_endline "Optimizing...";
  (* print_endline "optimize"; *)
  (* svalue_to_string sv |> print_endline; *)
  (* let cfg = [("model", "true"); ("proof", "false")] in
   * let ctx = mk_context cfg in *)
  let ctx = init_solver() in
  let g1 = Goal.mk_goal ctx true false false in

  let opt1 = Optimize.mk_opt ctx in
  
  let pcexp = pc_to_expr pc ctx mem in

  (match pcexp with
   | L pcv -> Goal.add g1 [pcv] 
   | H (pcv1, pcv2) -> Goal.add g1 [pcv1]
                       (* Goal.add g2 [pcv2] *) 
  );
  
  List.iter (fun f -> Optimize.add opt1 [f]) (Goal.get_formulas g1);

  let v = sv_to_expr pc sv ctx mem in
  (* TODO(Romy): Fix for two paths *)
  let h =
    (match v with
     | L v ->
        let bv = Expr.get_sort v  in
        (* half max int *)
        let hmi = Expr.mk_numeral_int ctx 0x80000000 bv in
        let v' =
          match Sort.get_sort_kind bv with
          | Z3enums.BV_SORT ->  BitVector.mk_add ctx v hmi
          | _ -> failwith ("Wrong type of sort " ^ (Sort.to_string bv))
        in
        f opt1 v'
     | H (v1,v2) ->
        let bv = Expr.get_sort v1  in
        (* half max int *)
        let hmi = Expr.mk_numeral_int ctx 0x80000000 bv in
        let v' =
          match Sort.get_sort_kind bv with
          | Z3enums.BV_SORT ->  BitVector.mk_add ctx v1 hmi
          | _ -> failwith ("Wrong type of sort " ^ (Sort.to_string bv))
        in
        f opt1 v'
    ) in

  (* List.iter (fun f -> Optimize.add opt2 [f]) (Goal.get_formulas g2); *)
  try
  match (Optimize.check opt1) with
   | Solver.SATISFIABLE ->
      let ex1 = Optimize.get_lower h in
      let ex2 = Optimize.get_upper h in
      (*print_endline ("Maxl" ^ (Expr.to_string ex1) ^ "upper:" ^ (Expr.to_string ex2));*)
      if Expr.equal ex1 ex2 then
        (* let i = Arithmetic.Integer.mk_const_s ctx "2147483648" in *)
        let bi = BitVector.mk_numeral ctx "2147483648" 64 in
        (* let sb = Expr.mk_sub ctx ex1 i in
         * let exp' = Expr.mk_sub *)
        let istr = Arithmetic.Integer.numeral_to_string ex1 in
        let bi1 = BitVector.mk_numeral ctx istr 64 in
        let sb = BitVector.mk_sub ctx bi1 bi in
        let si = Expr.simplify sb None in
        let i = int_of_string (BitVector.numeral_to_string si) in
        (*print_endline (string_of_int i);*) 
        
        (* print_endline (Arithmetic.Integer.numeral_to_string ex1); *)
        (* let bi = Big_int.sub_big_int i (Big_int.big_int_of_int64 2147483648L) in *)
        (* let i = Big_int.int_of_big_int bi in *)
        (* print_endline "max/min sat"; *)
        (* Printf.printf "Optimize: %s\n" (Optimize.to_string opt1); *)
        (* string_of_int i |> print_endline; *)
        Some (i)
      else None
   | _ ->  None
   with _ -> 
        if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
        None





let get_num_exprs (pc : pc_ext) (sv : svalue) (mem: Smemory.t list * int * int) : int =
   if !Flags.debug then 
      print_endline "Getting number of expressions..";
 
  let ctx = init_solver() in
  
  let g = Goal.mk_goal ctx true false false in
  (* print_endline "is_v_ct_unsat before sv"; *)
  let v = sv_to_expr pc sv ctx mem in
  (* print_endline "is_v_ct_unsat after  sv"; *)
  (* print_exp v; *)
  match v with
  | L v -> 0
  | H (v1, v2) ->
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

      let num_exprs = Goal.get_num_exprs g in
      num_exprs


let get_num_exprs_pc (pc : pc_ext) (mem: Smemory.t list * int * int) : int =
   if !Flags.debug then 
      print_endline "Getting number of expressions..";
 
  let ctx = init_solver() in
  
  let g = Goal.mk_goal ctx true false false in
  (* print_endline "is_v_ct_unsat before sv"; *)
  let pcexp = pc_to_expr pc ctx mem in
  let pcexp' = 
    match pcexp with
    | L pcv -> pcv 
    | H (pcv1, pcv2) -> Boolean.mk_and ctx [pcv1; pcv2]
  in
  Goal.add g [pcexp'];

  let num_exprs = Goal.get_num_exprs g in
  num_exprs


let are_same ?timeout:(timeout=30) ?model:(model=false) (sv1 : svalue) (sv2 : svalue)
      (pc : pc_ext) (mem: Smemory.t list * int * int) : bool =
  if !Flags.debug then (
    print_endline "Checking if values are same..";
  );
  let start_t = if !Flags.debug then Unix.gettimeofday() else 0.0 in
  
  (* print_endline "is_v_ct_unsat"; *) 
  (* Pc_type.print_pc (snd pc) |> print_endline;
   * svalue_to_string sv |> print_endline; *)
  (* svalue_to_string sv |> print_endline; *)

  let ctx = init_solver() in
  
  let g = Goal.mk_goal ctx true false false in
  (* print_endline "is_v_ct_unsat before sv"; *)
  let v1 = sv_to_expr pc sv1 ctx mem in
  let v2 = sv_to_expr pc sv2 ctx mem in


  if !Flags.debug then (
    let dt = Unix.gettimeofday () -. start_t in
    "Checking same time: " ^ (string_of_float dt) |> print_endline;
  );
  
  match v1,v2 with
  | L v1, L v2 when Expr.equal v1 v2 -> true
  | H (v11, v12), H (v21, v22) when Expr.equal v11 v21 && Expr.equal v12 v22 -> true
  | _, _ -> 
     let v' = 
       match v1,v2 with 
       | L v1, L v2 -> 
          let v' = Boolean.mk_eq ctx v1 v2 in
          let v' = Boolean.mk_not ctx v' in
          v'
       | H (v11, v12), H (v21, v22) ->
          let v' = Boolean.mk_eq ctx v11 v21 in
          let v' = Boolean.mk_not ctx v' in
          let v'' = Boolean.mk_eq ctx v12 v22 in
          let v'' = Boolean.mk_not ctx v'' in
          Boolean.mk_or ctx [v'; v'']
       | H (v11, v12), L (v2)
         | L (v2), H (v11, v12) ->
          let v' = Boolean.mk_eq ctx v11 v2 in
          let v' = Boolean.mk_not ctx v' in
          let v'' = Boolean.mk_eq ctx v12 v2 in
          let v'' = Boolean.mk_not ctx v'' in
          Boolean.mk_or ctx [v'; v'']
     in
     
     let pcexp = pc_to_expr pc ctx mem in
     let pcexp' = 
       match pcexp with
       | L pcv -> pcv 
       | H (pcv1, pcv2) -> Boolean.mk_and ctx [pcv1; pcv2]
     in
     Goal.add g [v'];
     Goal.add g [pcexp'];
     let solver = Solver.mk_solver ctx None in

     let num_exprs = Goal.get_num_exprs g in

     if (!Flags.stats) then (
       Stats.add_new_query "Unknown" (num_exprs) 0.0);
     
     let params = Params.mk_params ctx in
     (*Params.add_bool params (Symbol.mk_string ctx "sort_store") true;*)

     let s_formulas = (List.map (fun e -> Expr.simplify e (Some params)) (Goal.get_formulas g)) in

     List.iter (fun f -> Solver.add solver [f]) s_formulas;

     (* let stats = Solver.get_statistics solver in
      * print_endline (Statistics.to_string stats); *)     

     (* Printf.printf "Solver v_ct: %s\n" (Solver.to_string solver); *)
     if !Flags.portfolio_only then (
       let filename = write_formula_to_file ~model:model solver in
       if !Flags.debug then
         print_endline ("is_v_ct_unsat after write formula " ^ filename); 
       let res = 
         try (
           not (run_solvers ~model:model filename (read_sat "yices")
                  (read_sat "z3")
                  (read_sat "cvc4") (read_sat "boolector")
                  (read_sat "bitwuzla") timeout)
         ) with Timeout -> (
           false
         )
       in
       remove filename;
       res
     ) else if !Flags.z3_only then (

       (if (!Flags.stats) then
          Stats.update_query_str "Z3_bindings") ;
       let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in
       (* print_endline "is_v_ct_unsat_before_solving"; *) 
       try
       match (Solver.check solver []) with
       | Solver.UNSATISFIABLE ->
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          true
       | Solver.SATISFIABLE ->
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          (* let model = Solver.get_model solver in
           * (match model with
           *  | None -> print_endline "None"
           *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
           * ); *)
          false
       | _ ->
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          false
       with _ -> 
          if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
          if (!Flags.stats) then (
            Stats.update_query_time (Unix.gettimeofday () -. start);
            Stats.print_last());
          false
 
     ) else (
       if num_exprs > !Flags.magic_number_1 then (
         if !Flags.debug then print_endline "Using portfolio solver..";
         
         let filename = write_formula_to_file ~model:model solver in
         (* print_endline ("is_v_ct_unsat after write formula " ^ filename); *)
         let res = 
           try (
             not (run_solvers ~model:model filename (read_sat "yices") (read_sat "z3")
                    (read_sat "cvc4") (read_sat "boolector")
                    (read_sat "bitwuzla") timeout)
           )
           with Timeout -> false
         in
         remove filename;
         res
       ) else (

         if !Flags.debug then print_endline "Using Z3 solver..";

         (if (!Flags.stats) then
            Stats.update_query_str "Z3_bindings") ;
         let start = if !Flags.stats then Unix.gettimeofday() else 0.0 in
         (* print_endline "is_v_ct_unsat_before_solving"; *) 
         try
         match (Solver.check solver []) with
         | Solver.UNSATISFIABLE ->
            if (!Flags.stats) then (
              Stats.update_query_time (Unix.gettimeofday () -. start);
              Stats.print_last());
            true
         | Solver.SATISFIABLE ->
            if (!Flags.stats) then (
              Stats.update_query_time (Unix.gettimeofday () -. start);
              Stats.print_last());
            (* let model = Solver.get_model solver in
             * (match model with
             *  | None -> print_endline "None"
             *  | Some m -> print_endline "Model"; print_endline (Model.to_string m)
             * ); *)
            false
         | _ ->
            if (!Flags.stats) then (
              Stats.update_query_time (Unix.gettimeofday () -. start);
              Stats.print_last());
            false
         with _ ->
            if !Flags.debug then print_endline "Z3 solver failed - Maybe timeout";
            if (!Flags.stats) then (
              Stats.update_query_time (Unix.gettimeofday () -. start);
              Stats.print_last());
            false
 
       )
     
     )

