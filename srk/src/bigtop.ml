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

  val convex_hull:
    ?filter:(Quantifier.quantifier_prefix -> Syntax.Symbol.Set.t -> Syntax.Symbol.Set.t) ->
    [ `SubspaceCone
    | `SubspaceConeAccelerated
    | `Subspace
    | `Subspace
    | `IntFrac
    | `IntFracAccelerated
    | `LwCooperIntRealHull
    | `LwCooperIntHull
    | `LwCooperNoIntHull
    | `LwOnly ] ->
    Ctx.t formula -> DD.closed DD.t

  val compare:
    (DD.closed DD.t -> DD.closed DD.t -> bool) ->
    [`SubspaceCone | `SubspaceConeAccelerated | `Subspace
     | `IntFrac | `IntFracAccelerated
     | `LwCooperIntRealHull | `LwCooperIntHull | `LwCooperNoIntHull | `LwOnly] ->
    [`SubspaceCone | `SubspaceConeAccelerated | `Subspace
     | `IntFrac | `IntFracAccelerated
     | `LwCooperIntRealHull | `LwCooperIntHull | `LwCooperNoIntHull | `LwOnly] ->
    Ctx.t formula -> unit

end = struct

  module S = Syntax.Symbol.Set

  let ignore_quantifiers = ref false

  let ignore_quantifiers_in_convhull () = ignore_quantifiers := true

  let pp_dim fmt dim = Format.fprintf fmt "(dim %d)" dim

  let is_int_of_symbols symbols =
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

  let pp_alg fmt = function
    | `SubspaceCone -> Format.fprintf fmt "SubspaceCone"
    | `SubspaceConeAccelerated -> Format.fprintf fmt "SubspaceConeAccelerated"
    | `Subspace -> Format.fprintf fmt "Subspace"
    | `IntFrac -> Format.fprintf fmt "IntFrac"
    | `IntFracAccelerated -> Format.fprintf fmt "IntFracAccelerated"
    | `LwCooperIntRealHull ->
       Format.fprintf fmt "LW + Cooper with mixed hull after projection"
    | `LwCooperIntHull ->
       Format.fprintf fmt "LW + Cooper with integer hull after projection"
    | `LwCooperNoIntHull ->
       Format.fprintf fmt "LW + Cooper"
    | `LwOnly ->
       Format.fprintf fmt "LW (eliminating real variables only)"

  let convex_hull_ how
        ?(filter=elim_quantifiers)
        ?(int_constraints_of = (fun int_symbols _real_symbols ->
            is_int_of_symbols int_symbols))
        phi =
    let (qf, phi) = Quantifier.normalize srk phi in
    if List.exists (fun (q, _) -> q = `Forall) qf then
      failwith "universal quantification not supported";
    let module PLT = PolyhedronLatticeTiling in
    let symbols = Syntax.symbols phi in
    let symbols_to_keep = filter qf symbols in
    let terms =
      symbols_to_keep
      |> (fun set -> S.fold (fun sym terms -> Ctx.mk_const sym :: terms) set [])
      |> List.rev
      |> Array.of_list
    in
    let (int_symbols, real_symbols) =
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
    let integer_constraints = int_constraints_of int_symbols real_symbols
    in
    let symbols_to_eliminate =
      S.filter (fun sym -> not (S.mem sym symbols_to_keep)) symbols
    in
    Format.printf "Taking convex hull of formula: @[%a@]@;"
      (Syntax.Formula.pp srk) phi;
    Format.printf "Symbols to keep: @[%a@]@;" pp_symbols symbols_to_keep;
    Format.printf "Symbols to eliminate: @[%a@]@;" pp_symbols symbols_to_eliminate;
    Format.printf "Integer constraints: @[%a@]@;"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         (Syntax.Formula.pp srk))
      integer_constraints;
    let how =
      match how with
      | `SubspaceCone -> `SubspaceCone
      | `SubspaceConeAccelerated -> `SubspaceConeAccelerated
      | `Subspace -> `Subspace
      | `IntFrac -> `IntFrac
      | `IntFracAccelerated -> `IntFracAccelerated
      | `LwCooperIntRealHull -> `LwCooper `IntRealHullAfterProjection
      | `LwCooperIntHull -> `LwCooper `IntHullAfterProjection
      | `LwCooperNoIntHull -> `LwCooper `NoIntHullAfterProjection
    in
    let result =
      PLT.convex_hull how srk (Syntax.mk_and srk (phi :: integer_constraints)) terms in
    Format.printf "Convex hull:@\n @[<v 0>%a@]@\n"
      (Syntax.Formula.pp srk)
      (PLT.formula_of_dd srk (fun dim -> terms.(dim)) result);
    result

  let convex_hull ?(filter=elim_quantifiers) how phi =
    let translate_int_type_into_constraints how int_symbols _real_symbols =
      match how with
      | `LwOnly -> []
      (* Lw is the real relaxation of the convex hull;
       note that the result is not the exact convex hull of
       (exists x. phi) even if x is real, because
       the standard PLT abstraction makes a copy of the variables to keep
       and eliminates all original variables, including the integral ones.
       *)
      | `SubspaceCone
        | `SubspaceConeAccelerated
        | `Subspace
        | `IntFrac
        | `IntFracAccelerated
        | `LwCooperIntRealHull
        | `LwCooperIntHull
        | `LwCooperNoIntHull -> is_int_of_symbols int_symbols
    in
    let int_constraints_of = translate_int_type_into_constraints how in
    let filter =
        if !ignore_quantifiers then (fun _ s -> s) else filter
    in
    convex_hull_
      (match how with
       | `LwOnly -> `LwCooperNoIntHull
       | `SubspaceCone -> `SubspaceCone
       | `SubspaceConeAccelerated -> `SubspaceConeAccelerated
       | `Subspace -> `Subspace
       | `IntFrac -> `IntFrac
       | `IntFracAccelerated -> `IntFracAccelerated
       | `LwCooperIntRealHull -> `LwCooperIntRealHull
       | `LwCooperIntHull -> `LwCooperIntHull
       | `LwCooperNoIntHull -> `LwCooperNoIntHull
      )
      ~int_constraints_of ~filter phi

  let compare test alg1 alg2 phi =
    Format.printf "Comparing convex hulls computed by %a and by %a@\n"
      pp_alg alg1 pp_alg alg2;
    let hull1 = convex_hull alg1 phi in
    let () =
      Format.printf "%a hull: @[%a@]@\n@\n" pp_alg alg1 (DD.pp pp_dim) hull1 in
    let hull2 = convex_hull alg2 phi in
    let () =
      Format.printf "%a hull: @[%a@]@\n@\n" pp_alg alg2 (DD.pp pp_dim) hull2 in
    if test hull1 hull2 then
      Format.printf "Result: success"
    else
      if dd_subset hull1 hull2 then
        Format.printf "Result: failure (%a hull is more precise)"
          pp_alg alg1
      else if dd_subset hull2 hull2 then
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
          ignore (ConvHull.convex_hull `SubspaceCone (load_formula file));
          Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction"
  );

  ("-lira-convex-hull-sc-accelerated"
  , Arg.String
      (fun file ->
          ignore (ConvHull.convex_hull `SubspaceConeAccelerated (load_formula file));
          Format.printf "Result: success"
      )
  ,
    "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using the subspace-and-cone abstraction"
  );

  ("-lira-convex-hull-intfrac"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull `IntFrac (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using integer-fractional polyhedra-lattice-tilings"
  );

  ("-lira-convex-hull-intfrac-accelerated"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull `IntFracAccelerated (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real arithmetic
     using integer-fractional polyhedra-lattice-tilings"
  );

  ("-lira-convex-hull-lw"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull `LwOnly (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real
     arithmetic with all integrality constraints ignored, i.e., LRA."
  );

  ("-lira-convex-hull-lwcooper"
  , Arg.String
      (fun file ->
        ignore (ConvHull.convex_hull `LwCooperNoIntHull (load_formula file));
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
        ignore (ConvHull.convex_hull `LwCooperIntHull (load_formula file));
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
        ignore (ConvHull.convex_hull `LwCooperIntRealHull (load_formula file));
        Format.printf "Result: success"
      )
  , "Compute the convex hull of an existential formula in linear integer-real
     arithmetic by projection using Loos-Weispfenning elimination for variables not
     occurring in integrality constraints and sound Cooper elimination for variables
     that occur in integrality constraints, and taking the mixed hull at the end."
  );

  ("-compare-convex-hull-sc-vs-real"
  , Arg.String (fun file ->
        ConvHull.compare
          DD.equal
          `SubspaceCone `LwOnly
          (load_formula file))
  , "Test subspace-cone convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning."
  );

  ("-compare-convex-hull-sc-accelerated-vs-real"
  , Arg.String (fun file ->
        ConvHull.compare (* ConvHull.dd_subset *)
          DD.equal
          `SubspaceConeAccelerated `LwOnly
          (load_formula file))
  , "Test subspace-cone convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning."
  );

  ("-compare-convex-hull-intfrac-vs-real"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `IntFrac `LwOnly (load_formula file))
  , "Test integer-fractional convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning."
  );

  ("-compare-convex-hull-intfrac-accelerated-vs-real"
  , Arg.String (fun file ->
        ConvHull.compare ConvHull.dd_subset `IntFracAccelerated `LwOnly
          (load_formula file))
  , "Test integer-fractional convex hull of an existential formula in LIRA against
     the convex hull computed by Loos-Weispfenning."
  );

  ("-compare-convex-hull-sc-vs-intfrac"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceCone `IntFrac (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection in
     integer-fractional space."
  );

  ("-compare-convex-hull-sc-accelerated"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceCone `SubspaceConeAccelerated (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the accelerated version."
  );

  ("-compare-convex-hull-intfrac-accelerated"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `IntFrac `IntFracAccelerated (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the integer-fractional projection against the accelerated version."
  );

  ("-compare-convex-hull-sc-accelerated-vs-intfrac-accelerated"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceConeAccelerated `IntFracAccelerated (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection in
     integer-fractional space."
  );

  ("-compare-convex-hull-sc-accelerated-vs-intfrac"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceConeAccelerated `IntFrac (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection in
     integer-fractional space."
  );

  ("-compare-convex-hull-sc-accelerated-vs-lwcooper"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceConeAccelerated `LwCooperNoIntHull (load_formula file))
  , "Test the convex hull of an existential formula in LIRA computed by
     the subspace-cone abstraction against the one computed by projection using
     Loos-Weispfenning elimination for variables not occurring in integrality constraints
     and sound Cooper elimination for variables that occur in integrality constraints."
  );

  ("-compare-convex-hull-sc-accelerated-vs-lwcooper-inthull"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceConeAccelerated `LwCooperIntHull (load_formula file))
  , ""
  );

  ("-compare-convex-hull-sc-accelerated-vs-lwcooper-mixedhull"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceConeAccelerated `LwCooperIntRealHull (load_formula file))
  , ""
  );

  ("-compare-convex-hull-sc-vs-lwcooper"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceCone `LwCooperNoIntHull (load_formula file))
  , ""
  );

  ("-compare-convex-hull-sc-accelerated-vs-subspace"
  , Arg.String (fun file ->
        ConvHull.compare DD.equal `SubspaceConeAccelerated `Subspace (load_formula file))
  , ""
  );

  ("-disable-lira"
  , Arg.Clear ConvexHull.enable_lira
  , "Use real relaxation when computing convex hulls"
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
