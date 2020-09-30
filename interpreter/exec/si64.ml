(* WebAssembly-compatible i64 implementation *)

include Sym_int.Make
  (struct
    include Smt_type
    let size = 64
    (* let to_hex_string = Printf.sprintf "%lx" *)
  end)
