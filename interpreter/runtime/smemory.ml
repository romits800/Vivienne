open Types
open Svalues

type size = int32  (* number of pages *)
type address = int64
type offset = int32

               

exception Type
exception Bounds
exception SizeOverflow
exception SizeLimit
exception OutOfMemory

        
(* module StoresMap = Map.Make(struct
 *                        type t = int
 *                        let compare = (-)
 *                      end)
 * 
 * type stores_map_t = int StoresMap.t
 * let stores_map = ref StoresMap.empty *)
            

module Smem = Map.Make(struct
                  type t = int
                  let compare = (-)
                end)

type memory' = Si8.t Smem.t
type memory = {content : memory';
               current: size;
               max : size option;
               stores: svalue list;
               secrets: (int * int) list;
               nonsecrets: (int * int) list;
               prev_mem : memory option}
type t = memory

let get_secrets mem =
  mem.secrets

let get_public mem =
  mem.nonsecrets

let get_stores mem =
  (* let create_hstores (lo,hi) =
   *   let lo,hi = Int32.to_int lo, Int32.to_int hi in
   *   let hi_list = (List.init (hi-lo+1) (fun x-> x + lo)) in
   *   (\* List.iter (fun x -> print_endline (string_of_int x)) hi_list; *\)
   *   let stores = List.map Eval_symbolic.create_new_hstore hi_list in
   *   stores
   * in
   * let create_lstores (lo,hi) =
   *   let lo,hi = Int32.to_int lo, Int32.to_int hi in
   *   let lo_list = (List.init (hi-lo+1) (fun x-> x + lo)) in
   *   (\* List.iter (fun x -> print_endline (string_of_int x)) lo_list; *\)
   *   let stores = List.map Eval_symbolic.create_new_lstore lo_list in
   *   stores
   * in
   * let nsec = (Int32.of_int 16, Int32.of_int 32) in
   * let mem = {mem with nonsecrets = [nsec]} in
   * let all_stores = 
   *   List.fold_left (fun l sec -> l @ create_lstores sec) [] mem.nonsecrets @
   *     List.fold_left (fun l sec -> l @ create_hstores sec) [] mem.secrets @ mem.stores
   * in
   * print_endline "get_stores";
   * print_endline (string_of_int (List.length all_stores)); *)
  mem.stores

let get_prev_mem mem =
  mem.prev_mem
  
let create_mem () =  Smem.empty 
  (* Smem.add 1 Si32.zero m *)
            
let page_size = 0x10000L (* 64 KiB *)

let within_limits n = function
  | None -> true
  | Some max -> I32.le_u n max

let create n =
  if I32.gt_u n 0x10000l
  then
    raise SizeOverflow
  else
    (* let size = Int64.(mul (of_int32 n) page_size) in *)
    create_mem()
    (* try
   *   (\* let size = Int64.(mul (of_int32 n) page_size) in *\)
   * 
   *                 (\* Array1_64.create Int8_unsigned C_layout size in
   *    * Array1.fill mem Si32.zero; *\)
   *   mem
   * with Out_of_memory -> raise OutOfMemory *)

let alloc2 min =
  assert (within_limits min None);
  {content = create min;
   current = min;
   max = None;
   stores = [];
   secrets = [] ;
   nonsecrets = [];
   prev_mem = None}

  
let alloc (SmemoryType {min; max}) =
  assert (within_limits min max);
  {content = create min; current = min; max;
   stores = []; secrets = []; nonsecrets = [];
  prev_mem = None}

let bound mem =
  failwith "bound: Not implemented"
  (* Array1_64.dim mem.content *)

let size mem =
  mem.current
  (* Int64.(to_int32 (div (bound mem) page_size)) *)

let type_of mem =
  SmemoryType {min = size mem; max = mem.max}

let grow mem delta =
  let old_size = size mem in
  let new_size = I32.add old_size delta in
  if not (within_limits new_size mem.max)
  then raise SizeLimit
  else { mem with current = new_size}
  
  (* let old_size = size mem in
   * let new_size = Int32.add old_size delta in
   * if I32.gt_u old_size new_size then raise SizeOverflow else
   * if not (within_limits new_size mem.max) then raise SizeLimit else
   * let after = create new_size in
   * let dim = Array1_64.dim mem.content in
   * Array1.blit (Array1_64.sub mem.content 0L dim) (Array1_64.sub after 0L dim);
   * mem.content <- after *)

(* fix to create high values *)

(* let rec is_high a = function
 *   | [] -> false
 *   | (lo, hi)::_ when a >= lo && a <= hi -> true
 *   | h::tl -> is_high a tl *) 

         
(* let load_byte (mem: memory) (a:int) =
 *   try
 *     (mem, Smem.find a mem.content)
 *   with Not_found ->
 *     let nval =
 *       if (is_high a mem.secrets) then
 *         Si8.of_high()
 *       else
 *         Si8.of_low()
 *     in
 *     let mem = {mem with content = Smem.add a nval mem.content} in
 *     (mem, nval)
 *   (\* try Array1_64.get mem.content a with Invalid_argument _ -> raise Bounds *\) *)

let store_byte (mem: memory) a b =
  {mem with content = Smem.add a b mem.content }
  (* try Array1_64.set mem.content a b with Invalid_argument _ -> raise Bounds *)

(* let apply_policy buf a =
 *   let parse_h h a =
 *     match h with
 *     | Int (i) -> (a, h)
 *     | BitVec (i, n) -> (a, h)
 *     | Const (
 *     | _ -> failwith "String in mem: Not possible"
 *   in
 *     let rec apply_policy_i buf ns acc ad =
 *     match buf with
 *     | h::tl ->
 *        let (i,j) = parse_h h ad in
 *        apply_policy_i tl (i::ns) (j::acc) (ad+1)
 *     | [] -> (acc,ns)
 *   in
 *   apply_policy_i buf [] [] a *)

          
(* let load_bytes mem a n =
 *   let ind = List.init n (fun i -> i) in
 *   (\* let buf = List.map (fun i -> load_byte mem (a+ i)) ind in *\)
 *   let (mem,buf) = List.fold_left
 *               (fun (memi,lst) i ->
 *                 let memn, v = load_byte memi (a + i) in
 *                 (memn,v::lst)
 *               ) (mem,[]) ind in
 *   (mem,buf)
 *   (\* let buf = Buffer.create n in *\) *)

(* let store_bytes mem a bs =
 *   let mem,_ = List.fold_left
 *               (fun (memi,i) bi ->
 *                 let memn = store_byte memi (a + i) bi in
 *                 (memn, i+1)
 *               ) (mem,0) bs
 *   in mem *)
  

let effective_address a o =
  let ea = a + o in
  if ea < a then raise Bounds;
  ea

(* let loadn mem a o n =
 *   assert (n > 0 && n <= 8);
 *   load_bytes mem (effective_address a o) n *)
  

  (* let rec loop a n =
   *   if n = 0 then 0L else begin
   *     let x = Int64.(shift_left (loop (add a 1L) (n - 1)) 8) in
   *     Int64.logor (Int64.of_int (load_byte mem a)) x
   *   end
   * in loop (effective_address a o) n *)

let storen mem a o n x =
  assert (n > 0 && n <= 8);
  match x with
  (* | Smt_type.Multi (ts, id, n) ->
   *    store_bytes mem (effective_address a o) ts *)
  | Smt_type.BitVec (i, bn) ->
     assert (n == bn);
     let sz = n/8 in
     let rec store_i a sz i mem =
       (match sz with
        | 0 -> mem
        | _ ->
           let v =  Smt_type.BitVec(Int64.(logand i  0xffL), 8) in
           let mem' = store_byte mem a v  in
           store_i (a+1) (sz-1) (Int64.shift_right i 8) mem'
       ) in
     store_i (effective_address a o) sz i mem
  (* | Smt_type.Const (Smt_type.High i ) as v ->
   *    let rec store_i a n mem res =
   *      (match n with
   *       | 0 -> res,mem
   *       | _ ->
   *          let v8 =  Smt_type.high_to_term() in
   *          let mem' = store_byte mem a v8  in
   *          let res = v8::res in
   *          store_i (a+1) (n-1) mem' res
   *      ) in
   *    let res, mem = 
   *      store_i (effective_address a o) n mem [] in
   *    let id = Smt_type.get_high() in
   *    (\* TODO(Romy) : return this + some relation to the old one, v *\)
   *    let _ = Smt_type.App(Smt_type.Eq, [Smt_type.Multi (res, id, List.length res); v]) in
   *    mem *)
  | _ -> mem

(*TODO(Romy): add other types *)
     (* store_bytes mem (effective_address a o) ts *)
(* let rec loop a n x =
   *   if n > 0 then begin
   *     Int64.(loop (add a 1L) (n - 1) (shift_right x 8));
   *     store_byte mem a (Int64.to_int x land 0xff)
   *   end
   * in loop (effective_address a o) n x *)

let load_value mem a o t =
  failwith "not implemented"
  
let store_value mem a o v =
    match v with
    | SI32 x ->
       let mem' = storen mem a o (Types.ssize (Svalues.type_of v)) x in
       mem'
    | SI64 x -> 
       let mem' = storen mem a o (Types.ssize (Svalues.type_of v)) x in
       mem'
    | _ -> failwith "Floats not implemented."
  (* | SF32 x -> Int64.of_int32 (F32.to_bits x)
     * | SF64 x -> F64.to_bits x *)
(* let remove_old_stores stores store = *)

         
(* Stores needs to be reversed *)
let store_sind_value mem store = 
  (* let newstores = remove_old_stores mem.stores store in *)
  {mem with stores = [store]; (*::mem.stores;*)
            prev_mem = Some mem}

let add_secret mem sec = 
  {mem with secrets = sec::mem.secrets }

let add_public mem sec = 
  {mem with nonsecrets = sec::mem.nonsecrets }

let replace_stores mem stores =
  {mem with stores = stores}

(* let init_secrets mem sec =
 *   {mem with secrets = sec } *)

(* let extend x n = function
 *   | ZX -> x
 *   | SX -> let sh = 64 - 8 * n in Int64.(shift_right (shift_left x sh) sh)
 * 
 * let load_packed sz ext mem a o t =
 *   assert (packed_size sz <= Types.size t);
 *   let n = packed_size sz in
 *   let x = extend (loadn mem a o n) n ext in
 *   match t with
 *   | I32Type -> I32 (Int64.to_int32 x)
 *   | I64Type -> I64 x
 *   | _ -> raise Type
 * 
 * let store_packed sz mem a o v =
 *   assert (packed_size sz <= Types.size (Values.type_of v));
 *   let n = packed_size sz in
 *   let x =
 *     match v with
 *     | I32 x -> Int64.of_int32 x
 *     | I64 x -> x
 *     | _ -> raise Type
 *   in storen mem a o n x *)
