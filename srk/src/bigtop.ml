open Srk
open Syntax

module Ctx = SrkAst.Ctx
module Infix = Syntax.Infix(Ctx)
let srk = Ctx.context

let generator_rep = ref false

let file_contents filename =
  let chan = open_in filename in
  let len = in_channel_length chan in
  let buf = Bytes.create len in
  really_input chan buf 0 len;
  close_in chan;
  buf

let load_math_formula filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try SrkParse.math_main SrkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let load_smtlib2 filename =
  SrkZ3.load_smtlib2 srk (Bytes.to_string (file_contents filename))

let load_chc fp filename = Chc.ChcSrkZ3.parse_file srk fp filename

let load_formula filename =
  let formula =
    if Filename.check_suffix filename "m" then load_math_formula filename
    else if Filename.check_suffix filename "smt2" then load_smtlib2 filename
    else Log.fatalf "Unrecognized file extension for %s" filename
  in
  Nonlinear.ensure_symbols srk;
  let subst f =
    match typ_symbol srk f with
    | `TyReal | `TyInt | `TyBool | `TyArr -> mk_const srk f
    | `TyFun (args, _) ->
      let f =
        try get_named_symbol srk (show_symbol srk f)
        with Not_found -> f
      in
      mk_app srk f (List.mapi (fun i typ -> mk_var srk i typ) args)
  in
  substitute_sym srk subst formula

let load_math_opt filename =
  let open Lexing in
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try SrkParse.math_opt_main SrkLex.math_token lexbuf with
  | _ ->
    let open Lexing in
    let pos = lexbuf.lex_curr_p in
    failwith (Printf.sprintf "Parse error: %s:%d:%d"
                filename
                pos.pos_lnum
                (pos.pos_cnum - pos.pos_bol + 1))

let print_result = function
  | `Sat -> Format.printf "sat@\n"
  | `Unsat -> Format.printf "unsat@\n"
  | `Unknown -> Format.printf "unknown@\n"

module ConvHull : sig

  val ignore_quantifiers_in_convhull: unit -> unit

  val dd_subset: DD.closed DD.t -> DD.closed DD.t -> bool

  val acceleration_window: int ref

  val convex_hull:
    'a context ->
    ?filter:(Quantifier.quantifier_prefix -> Syntax.Symbol.Set.t -> Syntax.Symbol.Set.t) ->
    [ `SubspaceCone
    | `SubspaceConeAccelerated
    | `SubspaceConePrecondAccelerate
    | `SclwAccelerated
    | `Subspace
    | `Subspace
    | `IntFrac
    | `IntFracAccelerated
    | `LwCooper of
        [ `IntRealHullAfterProjection
        | `IntHullAfterProjection
        | `NoIntHullAfterProjection]
    | `Lw
    | `RelaxToRealLw
    | `RelaxToRealProjectThenHull
    | `RunOnlyForPureInt
    | `GcThenElim
    | `GcImplicantThenProjectTerms
    | `NormalizThenElim
    ] ->
    'a formula -> DD.closed DD.t * [`RealSymbolDimensions of symbol -> symbol
                                   | `SyntaxDimensions
                                   | `TermDimensions of 'a ArithTerm.t array]

  val compare:
    'a context ->
    (DD.closed DD.t -> DD.closed DD.t -> bool) ->
    [ `SubspaceCone
    | `SubspaceConeAccelerated
    | `SubspaceConePrecondAccelerate
    | `SclwAccelerated
    | `Subspace
    | `IntFrac
    | `IntFracAccelerated
    | `LwCooper of
        [ `IntRealHullAfterProjection
        | `IntHullAfterProjection
        | `NoIntHullAfterProjection]
    | `Lw
    | `RelaxToRealLw
    | `RelaxToRealProjectThenHull
    | `RunOnlyForPureInt
    | `GcThenElim
    | `GcImplicantThenProjectTerms
    | `NormalizThenElim
    ] ->
    [ `SubspaceCone
    | `SubspaceConeAccelerated
    | `SubspaceConePrecondAccelerate
    | `SclwAccelerated
    | `Subspace
    | `IntFrac
    | `IntFracAccelerated
    | `LwCooper of
        [ `IntRealHullAfterProjection
        | `IntHullAfterProjection
        | `NoIntHullAfterProjection]
    | `Lw
    | `RelaxToRealLw
    | `RelaxToRealProjectThenHull
    | `RunOnlyForPureInt
    | `GcThenElim
    | `GcImplicantThenProjectTerms
    | `NormalizThenElim
    ] ->
    'a formula -> unit

  val retype_formula:
    'a context ->
    [ `TyInt | `TyReal ] -> 'a formula -> 'a formula * bool * (symbol -> symbol)

end = struct

  module S = Syntax.Symbol.Set

  let ignore_quantifiers = ref false

  let ignore_quantifiers_in_convhull () = ignore_quantifiers := true

  let pp_dim fmt dim = Format.fprintf fmt "(dim %d)" dim

  let is_int_of_symbols srk symbols =
    Syntax.Symbol.Set.fold
      (fun sym l -> Syntax.mk_is_int srk (Syntax.mk_const srk sym) :: l
      )
      symbols
      []

  let dd_subset dd1 dd2 =
    BatEnum.for_all
      (fun cnstrnt ->
        DD.implies dd1 cnstrnt)
      (DD.enum_constraints dd2)

  let elim_quantifiers quantifiers symbols =
    S.filter
      (fun s -> not (List.exists (fun (_, elim) -> s = elim) quantifiers))
      symbols

  let pp_symbols fmt set =
    Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "@\n")
      (fun fmt sym ->
        Format.fprintf fmt "%a: %a"
          (Syntax.pp_symbol srk) sym pp_typ (typ_symbol srk sym))
      fmt (S.to_list set)

  let acceleration_window = ref 1

  let pp_alg fmt = function
    | `SubspaceCone -> Format.fprintf fmt "SubspaceCone"
    | `SubspaceConeAccelerated ->
       Format.fprintf fmt "SubspaceConeAccelerated(window=%d)" !acceleration_window
    | `SubspaceConePrecondAccelerate -> Format.fprintf fmt "SubspaceConePrecondAccelerated"
    | `SclwAccelerated ->
       Format.fprintf fmt "(SubspaceCone + LW + Mixed Cooper)-accelerated(window=%d)"
         !acceleration_window
    | `Subspace -> Format.fprintf fmt "Subspace"
    | `IntFrac -> Format.fprintf fmt "IntFrac"
    | `IntFracAccelerated ->
       Format.fprintf fmt "IntFracAccelerated(window=%d)" !acceleration_window
    | `LwCooper `IntRealHullAfterProjection ->
       Format.fprintf fmt "LW + Cooper with mixed hull after projection"
    | `LwCooper `IntHullAfterProjection ->
       Format.fprintf fmt "LW + Cooper with integer hull after projection"
    | `LwCooper `NoIntHullAfterProjection ->
       Format.fprintf fmt "LW + Cooper"
    | `Lw ->
       Format.fprintf fmt
         "LW only (ignore integrality constraints on all symbols when projecting)"
    | `RelaxToRealLw ->
       Format.fprintf fmt "LW (all symbols in formula are first turned to real)"
    | `RelaxToRealProjectThenHull ->
       Format.fprintf fmt "Full-projection-of-implicant-then-hull (all symbols in formula are first turned to real)"
    | `GcThenElim ->
       Format.fprintf fmt
         "Compute integer hull using Gomory-Chvatal closure and DD projection
          directly onto free symbols (i.e., eliminate existentially quantified symbols)"
    | `GcImplicantThenProjectTerms ->
       Format.fprintf fmt
         "Compute integer hull using Gomory-Chvatal closure on each implicant and DD projection
          onto term dimensions (with each term being a free symbol)"
    | `NormalizThenElim ->
       Format.fprintf fmt "Compute integer hull using Normaliz and DD projection"
    | `RunOnlyForPureInt ->
       Format.fprintf fmt "SubspaceConeAccelerated (running on pure integer tasks only)"

  let standard_option = function
    | `RunOnlyForPureInt -> `SubspaceConeAccelerated !acceleration_window
    | `SubspaceCone -> `SubspaceCone
    | `SubspaceConeAccelerated -> `SubspaceConeAccelerated !acceleration_window
    | `SubspaceConePrecondAccelerate -> `SubspaceConePrecondAccelerate !acceleration_window
    | `SclwAccelerated -> `SclwAccelerated !acceleration_window
    | `Subspace -> `Subspace
    | `IntFrac -> `IntFrac
    | `IntFracAccelerated -> `IntFracAccelerated !acceleration_window
    | `LwCooper `IntRealHullAfterProjection ->
       `LwCooper `IntRealHullAfterProjection
    | `LwCooper `IntHullAfterProjection ->
       `LwCooper `IntHullAfterProjection
    | `LwCooper `NoIntHullAfterProjection ->
       `LwCooper `NoIntHullAfterProjection
    | `Lw -> `Lw
    | `RelaxToRealLw -> invalid_arg "Non-standard"
    | `RelaxToRealProjectThenHull -> invalid_arg "Non-standard"
    | `GcThenElim -> invalid_arg "Non-standard"
    | `GcImplicantThenProjectTerms -> invalid_arg "Non-standard"
    | `NormalizThenElim -> invalid_arg "Non-standard"

  let hull_then_project_option = function
    | `GcThenElim -> `GomoryChvatal
    | `GcImplicantThenProjectTerms -> `GomoryChvatal
    | `NormalizThenElim -> `Normaliz
    | _ -> invalid_arg "Not hull-then-project"

  let requantify srk quantifiers phi =
    List.fold_left
      (fun phi sym ->
        mk_exists_const srk sym phi)
      phi
      (List.rev quantifiers)

  let retype_formula srk typ phi =
    let (qf, phi) = Quantifier.normalize srk phi in
    if List.exists (fun (q, _) -> q = `Forall) qf then
      failwith "universal quantification not supported"
    else
      let module PLT = PolyhedronLatticeTiling.PolyhedralFormula in
      let (psi, map) = PLT.retype_as srk typ phi in
      let equivalent = (Symbol.Map.is_empty map) in
      let new_symbols =
        let symbols_in_retyped_phi =
          Symbol.Set.fold
            (fun sym set ->
              match Symbol.Map.find_opt sym map with
              | None -> Symbol.Set.add sym set
              | Some casted -> Symbol.Set.add casted set
            )
            (symbols phi)
            Symbol.Set.empty
        in
        Symbol.Set.diff (symbols psi) symbols_in_retyped_phi
      in
      let new_quantified_symbols =
        List.map
          (fun (_, sym) -> match Symbol.Map.find_opt sym map with
                           | Some new_sym -> new_sym
                           | None -> sym)
          qf
      in
      let remap_symbols s =
        match Symbol.Map.find_opt s map with
        | Some new_sym -> new_sym
        | None -> s
      in
      ( requantify srk
          (new_quantified_symbols @ Symbol.Set.to_list new_symbols)
          psi
      , equivalent
      , remap_symbols )

  let convex_hull_ srk how
        ?(filter=elim_quantifiers)
        phi =
    let relax_to_real =
      match how with
      | `RelaxToRealLw
        | `RelaxToRealProjectThenHull -> true
      | _ -> false
    in
    let (qf, phi) = Quantifier.normalize srk phi in
    if List.exists (fun (q, _) -> q = `Forall) qf then
      failwith "universal quantification not supported";
    let module PLT = PolyhedronLatticeTiling in
    let symbols = Syntax.symbols phi in
    let symbols_to_keep = filter qf symbols in
    let terms =
      symbols_to_keep
      |> (fun set -> S.fold (fun sym terms -> mk_const srk sym :: terms) set [])
      |> List.rev
      |> Array.of_list
    in
    let (phi, retyped_symbols) =
      if relax_to_real then
        PLT.PolyhedralFormula.retype_as srk `TyReal phi
      else
        (phi, Symbol.Map.empty)
    in
    let symbols_to_eliminate =
      S.filter (fun sym -> not (S.mem sym symbols_to_keep)) symbols
    in
    let (terms, symbols_to_keep, symbols_to_eliminate) =
      if relax_to_real then
        let lookup s = match Symbol.Map.find_opt s retyped_symbols with
          | Some s' ->  s'
          | None -> s
        in
        ( Array.map
            (fun term ->
              Syntax.substitute_const srk
                (fun sym -> Syntax.mk_const srk (lookup sym))
                term)
            terms
        , S.map lookup symbols_to_keep
        , S.map lookup symbols_to_eliminate
        )
      else
        (terms, symbols_to_keep, symbols_to_eliminate)
    in
    let (int_symbols, _real_symbols) =
      let is_int sym =
        match Syntax.typ_symbol srk sym with
        | `TyInt -> true
        | _ -> false
      in
      let is_real sym =
        match Syntax.typ_symbol srk sym with
        | `TyReal -> true
        | _ -> false
      in
      let symbols = Syntax.symbols phi in
      (S.filter is_int symbols, S.filter is_real symbols)
    in
    let integer_constraints = is_int_of_symbols srk int_symbols
    in
    Format.printf "Taking convex hull of formula: @[%a@]@;"
      (Syntax.Formula.pp srk) phi;
    Format.printf "Symbols to keep: @[%a@]@;" pp_symbols symbols_to_keep;
    Format.printf "Symbols to eliminate: @[%a@]@;" pp_symbols symbols_to_eliminate;
    Format.printf "Integer constraints: @[%a@]@;"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         (Syntax.Formula.pp srk))
      integer_constraints;
    let result =
      match how with
      | `GcThenElim
        | `NormalizThenElim ->
         (* All variables in input formula should be integer-typed for this to be sound *)
         PLT.full_integer_hull_then_project (hull_then_project_option how)
           ~to_keep:symbols_to_keep srk phi
      | `GcImplicantThenProjectTerms ->
         PLT.hull_by_integer_hull_of_implicant_then_project
           (hull_then_project_option how)
           srk phi terms
      | `RelaxToRealLw -> PLT.convex_hull `Lw srk phi terms
      | `RelaxToRealProjectThenHull ->
         PLT.hull_by_projecting_implicant srk phi terms
      | _ ->
         PLT.convex_hull (standard_option how) srk
           (Syntax.mk_and srk (phi :: integer_constraints)) terms
    in
    Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
      (Syntax.Formula.pp srk)
      (PLT.formula_of_dd srk (fun dim -> terms.(dim)) result);
    let dimension_data =
      match how with
      | `GcThenElim -> `SyntaxDimensions
      | _ -> `TermDimensions terms
    in
    (result, dimension_data)

  let convex_hull srk ?(filter=elim_quantifiers) how phi =
    let filter =
      if !ignore_quantifiers then (fun _ s -> s)
      else if how = `RunOnlyForPureInt then
        (fun quantifiers symbols ->
          if Symbol.Set.for_all (fun s -> Syntax.typ_symbol srk s = `TyInt) symbols
          then filter quantifiers symbols
          else
            begin
              failwith "Result: failure (non-integer symbols exist)";
            end
        )
      else filter
    in
    convex_hull_ srk
      (match how with
       | `RunOnlyForPureInt -> `SubspaceConeAccelerated
       | `SubspaceCone -> `SubspaceCone
       | `SubspaceConeAccelerated -> `SubspaceConeAccelerated
       | `SubspaceConePrecondAccelerate -> `SubspaceConePrecondAccelerate
       | `SclwAccelerated -> `SclwAccelerated
       | `Subspace -> `Subspace
       | `IntFrac -> `IntFrac
       | `IntFracAccelerated -> `IntFracAccelerated
       | `LwCooper `IntRealHullAfterProjection ->
          `LwCooper `IntRealHullAfterProjection
       | `LwCooper `IntHullAfterProjection ->
          `LwCooper `IntHullAfterProjection
       | `LwCooper `NoIntHullAfterProjection ->
          `LwCooper `NoIntHullAfterProjection
       | `Lw -> `Lw
       | `RelaxToRealLw -> `RelaxToRealLw
       | `RelaxToRealProjectThenHull -> `RelaxToRealProjectThenHull
       | `GcThenElim -> `GcThenElim
       | `GcImplicantThenProjectTerms -> `GcImplicantThenProjectTerms
       | `NormalizThenElim -> `NormalizThenElim
      )
      ~filter phi

  let remap_term_dimensions_to_symbol_dimensions
        srk terms dim_of_symbol ambient_dim term_dd =
    let remapped_constraints = BatEnum.empty () in
    BatEnum.iter
      (fun (kind, v) ->
        let v' =
          Linear.QQVector.fold
            (fun dim coeff v' ->
              try
                match Syntax.ArithTerm.destruct srk terms.(dim) with
                | `App (sym, []) ->
                   Linear.QQVector.add_term coeff (dim_of_symbol sym) v'
                | _ -> failwith (Format.asprintf "term %a is not symbol"
                                   (Syntax.ArithTerm.pp srk) terms.(dim))
              with
              | Invalid_argument _ ->
                 failwith (Format.asprintf "index %d is out of bounds" dim)
            )
            Linear.QQVector.zero
            v
        in
        BatEnum.push remapped_constraints (kind, v')
      )
      (DD.enum_constraints term_dd);
    let remapped_dd = DD.of_constraints_closed ambient_dim remapped_constraints in
    remapped_dd

  let compare srk test alg1 alg2 phi =
    Format.printf "Comparing convex hulls computed by %a and by %a@\n"
      pp_alg alg1 pp_alg alg2;
    let (hull1, dimension_data1) = convex_hull srk alg1 phi in
    let () =
      Format.printf "%a hull: @[%a@]@\n@\n" pp_alg alg1 (DD.pp pp_dim) hull1 in
    let (hull2, dimension_data2) = convex_hull srk alg2 phi in
    let () =
      Format.printf "%a hull: @[%a@]@\n@\n" pp_alg alg2 (DD.pp pp_dim) hull2 in
    let (hull1', hull2') =
      match dimension_data1, dimension_data2 with
      | `TermDimensions _, `TermDimensions _ -> (hull1, hull2)
      | `SyntaxDimensions, `SyntaxDimensions -> (hull1, hull2)
      | `SyntaxDimensions, `TermDimensions terms2 ->
         ( hull1
         , remap_term_dimensions_to_symbol_dimensions srk
             terms2 Syntax.int_of_symbol (DD.ambient_dimension hull1) hull2)
      | `TermDimensions terms1, `SyntaxDimensions ->
         ( remap_term_dimensions_to_symbol_dimensions srk
             terms1 Syntax.int_of_symbol (DD.ambient_dimension hull2) hull1
         , hull2)
      (*
      | `RealSymbolDimensions _, `RealSymbolDimensions _ ->
         failwith "Only one relaxation for now"
      | `TermDimensions terms1, `SyntaxDimensions ->
         ( remap_term_dimensions_to_symbol_dimensions srk
             terms1 Syntax.int_of_symbol (DD.ambient_dimension hull2) hull1
         , hull2)
      | `SyntaxDimensions, `TermDimensions terms2 ->
         ( hull1
         , remap_term_dimensions_to_symbol_dimensions srk
             terms2 Syntax.int_of_symbol (DD.ambient_dimension hull1) hull2)
      | `TermDimensions terms1, `RealSymbolDimensions remap ->
         ( remap_term_dimensions_to_symbol_dimensions srk
             terms1 (fun sym -> int_of_symbol (remap sym))
             (DD.ambient_dimension hull2) hull1
         , hull2)
      | `RealSymbolDimensions remap, `TermDimensions terms2 ->
         ( hull1
         , remap_term_dimensions_to_symbol_dimensions srk
             terms2 (fun sym -> int_of_symbol (remap sym))
             (DD.ambient_dimension hull1) hull2
         )
      | `SyntaxDimensions, `RealSymbolDimensions _
        | `RealSymbolDimensions _, `SyntaxDimensions ->
         failwith "not supported yet"
       *)
    in
    if test hull1' hull2' then
      Format.printf "Result: success"
    else
      if dd_subset hull1' hull2' then
        Format.printf "Result: failure (%a hull is more precise)"
          pp_alg alg1
      else if dd_subset hull2' hull1' then
        Format.printf "Result: failure (%a hull is more precise)"
          pp_alg alg2
      else
        Format.printf "Result: failure (%a and %a hull incomparable)"
          pp_alg alg1 pp_alg alg2

end


let spec_list = [
  ("-simsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Quantifier.simsat srk phi)),
   " Test satisfiability of an LRA or LIA formula (IJCAI'16)");

  ("-nlsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Wedge.is_sat srk (snd (Quantifier.normalize srk phi)))),
   " Test satisfiability of a non-linear ground formula (POPL'18)");

  ("-lirrsat",
   Arg.String (fun file ->
       let phi = load_formula file in
       print_result (Lirr.is_sat srk (snd (Quantifier.normalize srk phi)))),
   " Test satisfiability of a non-linear ground formula using theory of linear integer real rings");

  ("-normaliz",
   Arg.Unit (fun () -> PolynomialConeCpClosure.set_cutting_plane_method `Normaliz),
   "Set weak theory solver to use Normaliz's integer hull computation (instead of Gomory-Chvatal");

  ("-generator",
   Arg.Set generator_rep,
   " Print generator representation of convex hull");

  ("-no-projection",
   Arg.Unit (fun () -> ConvHull.ignore_quantifiers_in_convhull ()),
   "Ignore existential quantifiers when computing convex hull"
  );

  ("-lira-convex-hull-sc"
  , Arg.String
      (fun file ->
          ignore (ConvHull.convex_hull srk `SubspaceCone (load_formula file));
          Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction"
  );

  ("-lira-acceleration-window"
  , Arg.Int (fun n -> Format.printf "Setting window size to %d" n;
                      ConvHull.acceleration_window := n)
  , "Set the window size of models that accelerated convex hull methods use"
  );

  ("-lira-convex-hull-sc-accelerated"
  , Arg.String
      (fun file ->
          ignore (ConvHull.convex_hull srk `SubspaceConeAccelerated (load_formula file));
          Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction"
  );

  ("-lira-convex-hull-sc-precond-accelerate"
  , Arg.String
      (fun file ->
          ignore (ConvHull.convex_hull srk `SubspaceConePrecondAccelerate (load_formula file));
          Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction"
  );

  ("-lira-convex-hull-sclw-accelerated"
  , Arg.String
      (fun file ->
          ignore (ConvHull.convex_hull srk `SclwAccelerated (load_formula file));
          Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone + LW Cooper abstraction"
  );

  ("-lira-convex-hull-intfrac"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `IntFrac (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using integer-fractional polyhedra-lattice-tilings"
  );

  ("-lira-convex-hull-intfrac-accelerated"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `IntFracAccelerated (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using integer-fractional polyhedra-lattice-tilings"
  );

  ("-lira-convex-hull-lw"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `Lw (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real
     arithmetic with all integrality constraints ignored, i.e., LRA."
  );

  ("-lira-convex-hull-lwcooper"
  , Arg.String
      (fun file ->
        ignore
          (ConvHull.convex_hull srk (`LwCooper `NoIntHullAfterProjection)
             (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real
     arithmetic by projection using Loos-Weispfenning elimination for variables not
     occurring in integrality constraints and sound Cooper elimination for variables
     that occur in integrality constraints."
  );

  ("-lira-convex-hull-lwcooper-inthull"
  , Arg.String
      (fun file ->
        ignore
          (ConvHull.convex_hull srk (`LwCooper `IntHullAfterProjection) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real
     arithmetic by projection using Loos-Weispfenning elimination for variables not
     occurring in integrality constraints and sound Cooper elimination for variables
     that occur in integrality constraints, and taking the integer hull at the end.
     This is sound if all variables remaining are integral."
  );

  ("-lira-convex-hull-lwcooper-mixedhull"
  , Arg.String
      (fun file ->
        ignore
          (ConvHull.convex_hull srk (`LwCooper `IntRealHullAfterProjection) (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real
     arithmetic by projection using Loos-Weispfenning elimination for variables not
     occurring in integrality constraints and sound Cooper elimination for variables
     that occur in integrality constraints, and taking the mixed hull at the end."
  );

  ("-compare-convex-hull-sc-vs-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk
          DD.equal `SubspaceCone `Lw
          (load_formula file))
  , "Test subspace-cone convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning.
     Integrality constraints are tracked by SMT but ignored in elimination."
  );

  ("-compare-convex-hull-sc-accelerated-vs-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk (* ConvHull.dd_subset *)
          DD.equal
          `SubspaceConeAccelerated `Lw
          (load_formula file))
  , "Test subspace-cone convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning.
     Integrality constraints are tracked by SMT but ignored in elimination."
  );

  ("-compare-convex-hull-intfrac-vs-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `IntFrac `Lw (load_formula file))
  , "Test integer-fractional convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning.
     Integrality constraints are tracked by SMT but ignored in elimination."
  );

  ("-compare-convex-hull-intfrac-accelerated-vs-lw"
  , Arg.String (fun file ->
        ConvHull.compare srk ConvHull.dd_subset `IntFracAccelerated `Lw
          (load_formula file))
  , "Test integer-fractional convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning.
     Integrality constraints are tracked by SMT but ignored in elimination."
  );

  ("-compare-convex-hull-sc-vs-intfrac"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `SubspaceCone `IntFrac (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection in
     integer-fractional space."
  );

  ("-compare-convex-hull-sc-accelerated"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `SubspaceCone `SubspaceConeAccelerated (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the accelerated version."
  );

  ("-compare-convex-hull-sc-vs-precond-accelerate"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `SubspaceCone `SubspaceConePrecondAccelerate
          (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the precond + accelerated version."
  );

  ("-compare-convex-hull-intfrac-accelerated"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `IntFrac `IntFracAccelerated (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the integer-fractional projection against the accelerated version."
  );

  ("-compare-convex-hull-sc-accelerated-vs-intfrac-accelerated"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal
          `SubspaceConeAccelerated `IntFracAccelerated (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection in
     integer-fractional space."
  );

  ("-compare-convex-hull-sc-accelerated-vs-intfrac"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `SubspaceConeAccelerated `IntFrac (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection in
     integer-fractional space."
  );

  ("-compare-convex-hull-sc-accelerated-vs-lwcooper"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal
          `SubspaceConeAccelerated
          (`LwCooper `NoIntHullAfterProjection)
          (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection using
     Loos-Weispfenning elimination for variables not occurring in integrality constraints
     and sound Cooper elimination for variables that occur in integrality constraints."
  );

  ("-compare-convex-hull-sc-accelerated-vs-lwcooper-inthull"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal
          `SubspaceConeAccelerated
          (`LwCooper `IntHullAfterProjection) (load_formula file))
  , ""
  );

  ("-compare-convex-hull-sc-accelerated-vs-lwcooper-mixedhull"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal
          `SubspaceConeAccelerated
          (`LwCooper `IntRealHullAfterProjection)
          (load_formula file))
  , ""
  );

  ("-compare-convex-hull-sc-vs-lwcooper"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal
          `SubspaceCone
          (`LwCooper `NoIntHullAfterProjection)
          (load_formula file))
  , ""
  );

  ("-compare-convex-hull-sc-accelerated-vs-subspace"
  , Arg.String (fun file ->
        ConvHull.compare srk DD.equal `SubspaceConeAccelerated `Subspace (load_formula file))
  , ""
  );

  ("-lira-convex-hull-run-only-for-pure-int"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `RunOnlyForPureInt (load_formula file));
        Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction only on inputs where all symbols are integer."
  );

  ("-convex-hull-by-gc"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `GcThenElim (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     by computing the integer hull using iterated Gomory-Chvatal closure and then projecting it.
     Only existentially quantified symbols are eliminated. This is sound only when the formula
     is pure LIA."
  );

  ("-convex-hull-by-gc-implicant"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `GcImplicantThenProjectTerms (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     by computing the integer hull using iterated Gomory-Chvatal closure on each implicant
     and then projecting it.
     A new symbol for each symbol that is not existentially quantified is introduced, and all
     original symbols are eliminated. This is sound only when the formula is pure LIA."
  );

  ("-convex-hull-by-normaliz"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `NormalizThenElim (load_formula file));
        Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     by computing the integer hull using Normaliz and then projecting it. This is sound
     only when the formula is pure LIA."
  );

  ("-convex-hull-by-relax-real-lw"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `RelaxToRealLw (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of the real relaxation of an existential formula in
     linear integer-real arithmetic using Loos-Weispfenning."
  );

  ("-convex-hull-by-relax-real-project-implicant-then-hull"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull srk `RelaxToRealProjectThenHull (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of the real relaxation of an existential formula in
     linear integer-real arithmetic by doing full projection of each implicant
     and then taking the convex hull."
  );

  ("-compare-convex-hull-sc-accelerated-vs-gc"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal `SubspaceConeAccelerated `GcThenElim
          (load_formula file)
      )
  ,
    "Compare the convex hull computed by subspace-cone abstraction vs
     iterated Gomory-Chvatal + projection (eliminating only unwanted symbols)."
  );

  ("-compare-convex-hull-sc-precond-accelerate-vs-gc"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal `SubspaceConePrecondAccelerate `GcThenElim
          (load_formula file)
      )
  ,
    "Compare the convex hull computed by subspace-cone abstraction vs
     iterated Gomory-Chvatal + projection."
  );

  ("-compare-convex-hull-sc-accelerated-vs-relax-real-lw"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal `SubspaceConeAccelerated `RelaxToRealLw
          (load_formula file)
      )
  , "Compute the convex hull computed by subspace-cone abstraction vs the real relaxation
     of the formula.
     For the latter, the SMT solver sees all variables as real, as does elimination."
  );

  ("-compare-convex-hull-sc-precond-accelerate-vs-relax-real-lw"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal `SubspaceConePrecondAccelerate `RelaxToRealLw
          (load_formula file)
      )
  , "Compute the convex hull computed by subspace-cone abstraction vs the real relaxation
     of the formula.
     For the latter, the SMT solver sees all variables as real, as does elimination."
  );

  ("-compare-convex-hull-sc-accelerated-vs-normaliz"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal `SubspaceConeAccelerated `NormalizThenElim
          (load_formula file)
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     by computing the integer hull using iterated Gomory-Chvatal closure and then projecting it."
  );

  ("-compare-convex-hull-cooper-vs-gc"
  , Arg.String
      (fun file ->
        ConvHull.compare srk DD.equal (`LwCooper `IntHullAfterProjection) `GcThenElim
          (load_formula file)
      )
  , "Compare the integer hulls of LIA formulas computed by Cooper and GC to see if they are equal."
  );

  ("-integralize-smt-file"
  , Arg.String (fun file ->
        let () =
          if not (Filename.check_suffix file ".smt2") then failwith "not an SMT file"
          else ()
        in
        let phi = load_smtlib2 file in
        let (phi', equivalent, _) =
          try ConvHull.retype_formula srk `TyInt phi
          with
          | _ -> Format.printf "Fail at file: %s" file;
                 failwith "Failed"
        in
        let suffix = if equivalent then "_equivalent.smt2" else "_integralized.smt2" in
        let outfilename = (Filename.remove_extension file) ^ suffix in
        Format.printf "Writing to file %s@;" outfilename;
        let fmt = Format.formatter_of_out_channel (open_out outfilename) in
        pp_smtlib2 srk fmt phi'
      )
  , "Make a copy of an SMT file with all real variables re-declared as integer"
  );

  ("-realify-smt-file"
  , Arg.String (fun file ->
        let () =
          if not (Filename.check_suffix file ".smt2") then failwith "not an SMT file"
          else ()
        in
        let phi = load_smtlib2 file in
        let (phi', equivalent, _) =
          try ConvHull.retype_formula srk `TyReal phi
          with
          | _ -> Format.printf "Fail at file: %s" file;
                 failwith "Failed"
        in
        let suffix = if equivalent then "_equivalent.smt2" else "_realified.smt2" in
        let outfilename = (Filename.remove_extension file) ^ suffix in
        Format.printf "Writing to file %s@;" outfilename;
        let fmt = Format.formatter_of_out_channel (open_out outfilename) in
        pp_smtlib2 srk fmt phi'
      )
  , "Make a copy of an SMT file with all integer variables re-declared as real"
  );

  ("-convex-hull",
   Arg.String (fun file ->
       let (qf, phi) = Quantifier.normalize srk (load_formula file) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let exists v =
         not (List.exists (fun (_, x) -> x = v) qf)
       in
       let polka = Polka.manager_alloc_strict () in
       let pp_hull formatter hull =
         if !generator_rep then begin
           let env = SrkApron.get_env hull in
           let dim = SrkApron.Env.dimension env in
           Format.printf "Symbols:   [%a]@\n@[<v 0>"
             (SrkUtil.pp_print_enum (Syntax.pp_symbol srk)) (SrkApron.Env.vars env);
           SrkApron.generators hull
           |> List.iter (fun (generator, typ) ->
               Format.printf "%s [@[<hov 1>"
                 (match typ with
                  | `Line    -> "line:     "
                  | `Vertex  -> "vertex:   "
                  | `Ray     -> "ray:      "
                  | `LineMod -> "line mod: "
                  | `RayMod  -> "ray mod:  ");
               for i = 0 to dim - 2 do
                 Format.printf "%a@;" QQ.pp (Linear.QQVector.coeff i generator)
               done;
               Format.printf "%a]@]@;" QQ.pp (Linear.QQVector.coeff (dim - 1) generator));
           Format.printf "@]"
         end else
           SrkApron.pp formatter hull
       in
       Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
         pp_hull (Abstract.abstract ~exists srk polka phi)),
   " Compute the convex hull of an existential linear arithmetic formula");

  ("-wedge-hull",
   Arg.String (fun file ->
       let (qf, phi) = Quantifier.normalize srk (load_formula file) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let exists v =
         not (List.exists (fun (_, x) -> x = v) qf)
       in
       let wedge = Wedge.abstract ~exists srk phi in
       Format.printf "Wedge hull:@\n @[<v 0>%a@]@\n" Wedge.pp wedge),
   " Compute the wedge hull of an existential non-linear arithmetic formula");

  ("-affine-hull",
   Arg.String (fun file ->
       let phi = load_formula file in
       let qf = fst (Quantifier.normalize srk phi) in
       if List.exists (fun (q, _) -> q = `Forall) qf then
         failwith "universal quantification not supported";
       let symbols = (* omits skolem constants *)
         Symbol.Set.elements (symbols phi)
       in
       let aff_hull = Abstract.affine_hull srk phi symbols in
       Format.printf "Affine hull:@\n %a@\n"
         (SrkUtil.pp_print_enum (ArithTerm.pp srk)) (BatList.enum aff_hull)),
   " Compute the affine hull of an existential linear arithmetic formula");

  ("-qe",
   Arg.String (fun file ->
       let open Syntax in
       let phi = load_formula file in
       let result =
         Quantifier.qe_mbp srk phi
         |> SrkSimplify.simplify_dda srk
       in
       Format.printf "%a@\n" (pp_smtlib2 srk) result),
   " Eliminate quantifiers");

  ("-stats",
   Arg.String (fun file ->
       let open Syntax in
       let phi = load_formula file in
       let phi = Formula.prenex srk phi in
       let constants = fold_constants Symbol.Set.add phi Symbol.Set.empty in
       let rec go phi =
         match Formula.destruct srk phi with
         | `Quantify (`Exists, _, _, psi) -> "E" ^ (go psi)
         | `Quantify (`Forall, _, _, psi) -> "A" ^ (go psi)
         | _ -> ""
       in
       let qf_pre =
         (String.concat ""
            (List.map (fun _ -> "E") (Symbol.Set.elements constants)))
         ^ (go phi)
       in
       Format.printf "Quantifier prefix: %s" qf_pre;
       Format.printf "Variables: %d" (String.length qf_pre);
       Format.printf "Matrix size: %d" (size phi)),
   " Print formula statistics");

  ("-random",
   Arg.Tuple [
     Arg.String (fun arg ->
         let qf_pre = ref [] in
         String.iter (function
             | 'E' -> qf_pre := `Exists::(!qf_pre)
             | 'A' -> qf_pre := `Forall::(!qf_pre)
             | _ -> assert false)
           arg;
         RandomFormula.quantifier_prefix := List.rev (!qf_pre));
     Arg.Set_int RandomFormula.formula_uq_depth;
     Arg.String (fun arg ->
         begin match arg with
         | "dense" -> RandomFormula.dense := true
         | "sparse" -> RandomFormula.dense := false
         | x -> Log.fatalf "unknown argument: %s" x;
         end;
         Random.self_init ();
         let z3 = Z3.mk_context [] in
         Z3.SMT.benchmark_to_smtstring
           z3
           "random"
           ""
           "unknown"
           ""
           []
           (SrkZ3.z3_of_formula srk z3 (RandomFormula.mk_random_formula srk))
         |> print_endline)
   ],
   " Generate a random formula");

  ("-chc",
   Arg.String (fun file ->
       let open Iteration in
       let fp = Chc.Fp.create () in
       let fp = load_chc fp file in
       let pd =
         (module Product(LossyTranslation)(PolyhedronGuard) : PreDomain)
       in (*TODO: let user pick iter operation*)
       let rels = Chc.Fp.get_relations_used fp in
       let sln = Chc.Fp.solve srk fp pd in
       Format.printf "(Solution is:\n@[";
       SrkUtil.pp_print_enum
         ~pp_sep:(fun formatter () -> Format.fprintf formatter "@ \n ")
         (fun formatter rel ->
            let syms, phi = sln rel in
            let syms = BatArray.to_list syms in
            Format.fprintf formatter "@%a : %a@"
            (Chc.pp_rel_atom srk fp)
            (Chc.mk_rel_atom srk fp rel syms)
            (Formula.pp srk)
            phi)
         Format.std_formatter
         (Chc.Relation.Set.enum rels)),
   " Output solution to system of constrained horn clauses");

  ("-verbosity",
   Arg.String (fun v -> Log.verbosity_level := (Log.level_of_string v)),
   " Set verbosity level (higher = more verbose; defaults to 0)");

  ("-verbose",
   Arg.String (fun v -> Log.set_verbosity_level v `info),
   " Raise verbosity for a particular module");

  ("-verbose-list",
   Arg.Unit (fun () ->
       print_endline "Available modules for setting verbosity:";
       Hashtbl.iter (fun k _ ->
           print_endline (" - " ^ k);
         ) Log.loggers;
       exit 0;
     ),
   " List modules which can be used with -verbose")
]

let usage_msg = "bigtop: command line interface to srk \n\
  Usage:\n\
  \tbigtop [options] [-simsat|-nlsat] formula.smt2\n\
  \tbigtop [-generator] -convex-hull formula.smt2\n\
  \tbigtop -affine-hull formula.smt2\n\
  \tbigtop -wedge-hull formula.smt2\n\
  \tbigtop -qe formula.smt2\n\
  \tbigtop -stats formula.smt2\n\
  \tbigtop -random (A|E)* depth [dense|sparse]\n\
  \tbigtop -reachable-goal chc.smt2\n"

let anon_fun s = failwith ("Unknown option: " ^ s)

let () =
  if Array.length Sys.argv == 1 then
    Arg.usage (Arg.align spec_list) usage_msg
  else
    Arg.parse (Arg.align spec_list) anon_fun usage_msg
