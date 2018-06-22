let name = "ctrewrite"
let version = "1.0"

let banner () =
  print_endline (name ^ " " ^ version ^ " ct stipping tool")

let usage = "Usage: " ^ name ^ " [option] [file ...]"

let args = ref []
let add_arg source = args := !args @ [source]

let quote s = "\"" ^ String.escaped s ^ "\""

let validate s = if (Filename.check_suffix s "wat" || Filename.check_suffix s "wasm")
                 then s
                 else raise (Arg.Bad ("File " ^ (quote s) ^ " unsupported. Accepted formats: .wat .wasm"))

let argspec = Arg.align
[
  "-e", Arg.String add_arg, " evaluate string";
  "-i", Arg.String (fun file -> add_arg ("(input " ^ quote (validate file) ^ ")")),
    " read script from file";
  "-o", Arg.String (fun file -> add_arg ("(output " ^ quote (validate file) ^ ")")),
    " write module to file";
  "-w", Arg.Int (fun n -> Flags.width := n),
    " configure output width (default is 80)";
  "-strip", Arg.Set Flags.strip_ct, " rewrite: strip ct annotations";
  "-s", Arg.Set Flags.print_sig, " show pre-transform module signatures";
  "-u", Arg.Set Flags.unchecked, " unchecked, do not perform validation";
(*  "-d", Arg.Set Flags.dry, " dry, do not run program"; *)
  "-v", Arg.Unit banner, " show version"
]

let () =
  Printexc.record_backtrace true;
  try
    Arg.parse argspec
      (fun file -> add_arg ("(input " ^ quote (validate file) ^ ")")) usage;
    Flags.dry := true;
    List.iter (fun arg -> if not (Run.run_string arg) then exit 1) !args;
    if !args = [] then Flags.interactive := true;
    if !Flags.interactive then begin
      Flags.print_sig := true;
      banner ();
      Run.run_stdin ()
    end
  with exn ->
    flush_all ();
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
