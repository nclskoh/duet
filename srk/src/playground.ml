open Core
open Srk

(** Preamble stolen from bigtop.ml *)

module Ctx = SrkAst.Ctx
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

let () =
  let open Command.Let_syntax in
  Command.basic
    ~summary:"Weipsfenning's quantifier elimination"
    [%map_open
     let formula_file =
       flag "qe" (required string) ~doc:"smtlib2 file containing quantified formula"
         in
         fun () ->
         (* TODO: Figure out how to write your own parser... *)
         let formula = load_smtlib2 formula_file in
         (* Normalization turns all negated formulas into positive formulas by using < and <= *)
         let (prefix, qf) = Quantifier.normalize srk formula in
         let qf_cleaned = Syntax.eliminate_ite srk qf in
         Format.printf "@[Input formula is: %a@]@;" (Syntax.Expr.pp srk) formula;
         Format.printf "@[Quantifier-free part before ITE elim is: %a@]@;" (Syntax.Expr.pp srk) qf;
         Format.printf "@[Quantifier-free part after ITE elim is: %a@]@;" (Syntax.Expr.pp srk) qf_cleaned;
         let answer = LiraQuantifier.quantifier_elimination ~how:`Substitution prefix qf in
         Format.printf "@[Result of QE: %a@]@;" (Syntax.Expr.pp srk) answer;
         ()
    ]
  |> Command.run
