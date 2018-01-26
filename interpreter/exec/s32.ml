(* WebAssembly-compatible s32 implementation *)

include Int.Make
  (struct
    include Int32
    let bitwidth = 32
  end)
