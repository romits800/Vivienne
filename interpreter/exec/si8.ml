(* WebAssembly-compatible i32 implementation *)

   
include Sym_int.Make
  (struct
    include Smt_type
    let size = 8
    (* let to_hex_string = Printf.sprintf "%lx" *)
  end)
