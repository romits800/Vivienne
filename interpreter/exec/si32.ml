(* WebAssembly-compatible i32 implementation *)

   
include Sym_int.Make
  (struct
    include Smt_type
    let size = 32
    (* let to_hex_string = Printf.sprintf "%lx" *)
  end)


(* include Sym_int_under_construction.Make
 *   (struct
 *     include Int32
 *     let size = 32
 *     let zero = 0l
 *     let one = 1l
 *     (\* let to_hex_string = Printf.sprintf "%lx" *\)
 *   end) *)
