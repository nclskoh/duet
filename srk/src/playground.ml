open Core
open Srk

(** Preamble stolen from bigtop.ml *)

module Ctx = LiraQuantifier.Ctx
let srk = Ctx.context

(* From bigtop.ml *)
let file_contents filename =
  let chan = In_channel.create filename in
  let len = Option.value ~default:0 (Int64.to_int (In_channel.length chan)) in
  let buf = Buffer.create len in
  ignore (In_channel.input_buffer ~len:len chan buf);
  In_channel.close chan;
  Buffer.contents_bytes buf

let load_smtlib2 filename =
  SrkZ3.load_smtlib2 srk (Bytes.to_string (file_contents filename))

let do_qe sort file =
  load_smtlib2 file
  |> (fun phi -> match sort with
                 | `Std -> LiraQuantifier.qe phi
                 | `TyIntQe -> LiraQuantifier.Test.qe_as `TyIntQe phi
                 | `TyFracQe -> LiraQuantifier.Test.qe_as `TyFracQe phi
     )
  |> Format.printf "@[Result of QE: %a@]@;" (Syntax.Expr.pp srk)

let sort_of_string s =
  if String.equal s "std" then `Std
  else if String.equal s "int" then `TyIntQe
  else if String.equal s "frac" then `TyFracQe
  else invalid_arg "Invalid elimination type"

(* [lib/core_kernel/command_intf.ml] *)
let () =
  let open Command.Let_syntax in
  Command.basic
    ~summary:"Weipsfenning's quantifier elimination"
    [%map_open
     let formula_file = flag "qe" (required string)
                          ~doc:"smtlib2 file containing quantified formula"
     and elim_sort = flag "elim" (optional string)
                       ~doc:"eliminate all variables as if they are [int | frac | std]"
     and debug = flag "debug" (optional string)
                   ~doc:"debug at level [trace | debug | none]"
         in
         fun () ->
         Log.my_verbosity_level := (match debug with
                                    | None -> `info
                                    | Some s -> Log.level_of_string s);
         do_qe (match elim_sort with | None -> `Std | Some s -> sort_of_string s)
           formula_file
    ]
  |> Command.run
