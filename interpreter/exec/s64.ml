(* WebAssembly-compatible s64 implementation *)

include Int.Make
  (struct
    include Int64
    let bitwidth = 64
  end)
