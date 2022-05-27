open Syntax
open BatPervasives

module V = Linear.QQVector
module Monomial = Polynomial.Monomial
module P = Polynomial.QQXs
module Scalar = Apron.Scalar
module Coeff = Apron.Coeff
module Abstract0 = Apron.Abstract0
module Linexpr0 = Apron.Linexpr0
module Lincons0 = Apron.Lincons0
module Dim = Apron.Dim

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "srk.weaksolver" end)

let pp_dim srk = (fun formatter i -> pp_symbol srk formatter (symbol_of_int i))

let rec get_quantifiers srk env phi =
  let phi = Formula.prenex srk phi in
  let lookup env i =
    try Env.find env i
    with Not_found -> assert false
  in
  match Formula.destruct srk phi with
  | `Quantify (qt, name, typ, psi) ->
    let k = mk_const srk (mk_symbol srk ~name (typ :> Syntax.typ)) in
    let (qf_pre, psi) = get_quantifiers srk (Env.push k env) psi in
    ((qt,k)::qf_pre, psi)
  | _ -> ([], substitute srk (fun (i, _) -> lookup env i) phi)

let destruct_literal srk phi =
  let sub a b = P.sub (P.of_term srk a) (P.of_term srk b) in
  match Formula.destruct srk phi with
  | `Atom (`Arith (`Eq, s, t)) -> `Zero (sub t s)
  | `Atom (`Arith (`Lt, s, t)) -> `Neg (sub s t) (* x < y <=> !(0 <= x - y) *)
  | `Atom (`Arith (`Leq, s, t)) -> `Nonneg (sub t s)
  | `Atom (`IsInt s) -> `IsInt (P.of_term srk s)
  | `Proposition (`App (k, [])) -> `True k
  | `Not psi ->
    begin match Formula.destruct srk psi with
      | `Proposition (`App (k, [])) -> `False k
      | `Atom (`Arith (`Eq, s, t)) -> `Nonzero (sub s t)
      | `Atom (`Arith (`Leq, s, t)) -> `Neg (sub t s)   (* !(x <= y) <=> y - x < 0 *)
      | `Atom (`Arith (`Lt, s, t)) -> `Nonneg (sub s t) (*  !(x < y) <=> 0 <= x - y *)
      | `Atom (`IsInt s) -> `NonInt (P.of_term srk s)
      | _ -> invalid_arg (Format.asprintf "destruct_literal: %a? is not recognized"
                            (Formula.pp srk) phi)
    end
  | `Tru -> `Zero P.zero
  | `Fls -> `Zero P.one
  | _ ->
    invalid_arg (Format.asprintf "destruct_literal: %a~ is not recognized"
                   (Formula.pp srk) phi)


(* Conjuctive formulas in the language of ordered rings + integer predicate +
   booleans propositions.  *)
type cube =
  { nonneg : P.t list
  ; zero : P.t list
  ; int : P.t list
  ; pos :  Symbol.Set.t
  ; neg :  Symbol.Set.t
  ; not_nonneg : P.t list
  ; not_zero : P.t list
  ; not_int : P.t list }

let add_literal_to_cube srk lit cube =
  match destruct_literal srk lit with
  | `Zero z -> { cube with zero = z::cube.zero  }
  | `Nonneg p -> { cube with nonneg = p::cube.nonneg  }
  | `Neg n -> { cube with not_nonneg = n::cube.not_nonneg }
  | `Nonzero q -> { cube with not_zero = q::cube.not_zero }
  | `IsInt m -> { cube with int = m::cube.int }
  | `NonInt m -> { cube with not_int = m::cube.not_int }
  | `True k -> { cube with pos = Symbol.Set.add k cube.pos }
  | `False k -> { cube with neg = Symbol.Set.add k cube.neg }

let empty_cube =
  { nonneg = []
  ; zero = []
  ; int = []
  ; pos = Symbol.Set.empty
  ; not_nonneg = []
  ; not_zero = []
  ; not_int = []
  ; neg = Symbol.Set.empty}

module Model = struct
  type t =
    {
      (* Regular, consistent cone containing 1, and closed under cutting plane
         w.r.t. lattice *)
      cone : PolynomialCone.t
    (* Lattice of integers *)
    ; lattice : PolynomialConeCpClosure.polylattice
    (* Positive propositional variables *)
    ; pos : Symbol.Set.t (* Positive propositional variables *) }

  let nonnegative_cone m = m.cone

  let is_int m p =
    PolynomialConeCpClosure.in_polylattice p m.lattice

  let is_nonneg m p = PolynomialCone.mem p m.cone

  let is_zero m p =
    Polynomial.Rewrite.reduce (PolynomialCone.get_ideal m.cone) p
    |> P.equal P.zero

  let is_true_prop m k = Symbol.Set.mem k m.pos

  (* Find the minimal model of a cube, should one exist *)
  let get_model srk (cube : cube) =
    if Symbol.Set.exists (fun s -> Symbol.Set.mem s cube.pos) cube.neg then
      None
    else
      let initial_ideal =
        Polynomial.Rewrite.mk_rewrite Polynomial.Monomial.degrevlex cube.zero
        |> Polynomial.Rewrite.grobner_basis
      in
      logf ~level:`trace
        "weakSolver: Start making enclosing cone of: ideal: @[%a@] @; geqs: @[%a@]"
        (Polynomial.Rewrite.pp (pp_dim srk))
        initial_ideal
        (PolynomialUtil.PrettyPrint.pp_poly_list (pp_dim srk))
        cube.nonneg;

      let pc =
        PolynomialCone.make_enclosing_cone initial_ideal cube.nonneg
      in

      let lattice =
        PolynomialConeCpClosure.polylattice_spanned_by cube.int
      in

      (* NK: TODO: This triggers a bug that corrupts memory, e.g., the lattice. *)
      (*
      logf ~level:`trace
        "weakSolver: lattice: @[%a@],@;  initially generated by @[%a@]@;"
        (PolynomialConeCpClosure.pp_polylattice (pp_dim srk))
        lattice
        (PolynomialUtil.PrettyPrint.pp_poly_list (pp_dim srk))
        cube.int;
       *)

      logf "Enclosing cone: @[%a@]" (PolynomialCone.pp (pp_dim srk)) pc;

      let contradict_int =
        (* The IsInt relation is not closed under equality, so this is all we have
           to check. *)
        List.exists
          (fun p -> PolynomialConeCpClosure.in_polylattice p lattice)
          cube.not_int
      in
      if contradict_int then
        None
      else
        let cut_pc =
          PolynomialConeCpClosure.regular_cutting_plane_closure lattice pc
        in
        (* Provided that cut_pc is proper, model is least Z-model that satisfies
           all positive atoms. *)
        let model = { cone = cut_pc; lattice; pos = cube.pos } in
        if (PolynomialCone.is_proper cut_pc
            && (BatList.for_all (not % is_zero model) cube.not_zero)
            && (BatList.for_all (not % is_int model) cube.not_int)
            && (BatList.for_all (not % is_nonneg model) cube.not_nonneg))
        then Some model
        else None

  (* Determine whether a formula holds in a given model *)
  let evaluate_formula srk m phi =
    let f = function
      | `And xs -> List.for_all (fun x -> x) xs
      | `Or xs -> List.exists (fun x -> x) xs
      | `Tru -> true
      | `Fls -> false
      | `Not v -> not v
      | `Ite (cond, bthen, belse) -> if cond then bthen else belse
      | `Proposition (`App (k, [])) -> Symbol.Set.mem k m.pos
      | `Proposition _ -> invalid_arg "evaluate_formula: proposition"
      | `Quantify (_, _, _, _) -> invalid_arg "evaluate_formula: quantifier"
      | `Atom atom ->
        let atom = Formula.construct srk (`Atom atom) in
        match destruct_literal srk atom with
        | `Zero z -> is_zero m z
        | `Nonzero p -> not (is_zero m p)
        | `Nonneg p -> is_nonneg m p
        | `Neg n -> not (is_nonneg m n)
        | `IsInt q -> is_int m q
        | `NonInt q -> not (is_int m q)
        | `True k -> is_true_prop m k
        | `False k -> not (is_true_prop m k)
  in
  Formula.eval srk f phi

end

module Solver = struct
  type 'a t =
    {
      (* (Propositional) sat solver *)
      sat : 'a Smt.Solver.t
    ; srk : 'a context

    (* Map atomic formulae to propositional variables *)
    ; prop : ('a, typ_bool, 'a formula) Expr.HT.t

    (* Inverse of prop *)
    ; unprop : (symbol, 'a formula) Hashtbl.t

    (* Propositional skeletons of asserted formulae.  Not necessarily in same
       order they are asserted. *)
    ; mutable asserts : 'a formula list }

  let mk_solver srk =
    { sat = Smt.mk_solver srk
    ; srk = srk
    ; prop = Expr.HT.create 991
    ; unprop = Hashtbl.create 991
    ; asserts = [] }

  let prop_rewriter solver expr =
    let srk = solver.srk in
    match Expr.refine srk expr with
    | `ArithTerm _ | `ArrTerm _ -> expr
    | `Formula phi ->
      match Formula.destruct srk phi with
      | `Atom _ ->
        let atom =
          try
            Expr.HT.find solver.prop phi
          with Not_found ->
            let prop =
              mk_symbol
                srk
                ~name:(Format.asprintf "{%a}" (Expr.pp srk) expr)
                (expr_typ srk expr)
            in
            let atom = mk_const srk prop in
            Expr.HT.add solver.prop phi atom;
            Hashtbl.add solver.unprop prop phi;
            atom
        in
        (atom :> ('a, typ_fo) expr)
      | _ -> expr

  let propositionalize solver phi =
    let srk = solver.srk in
    rewrite srk ~down:(nnf_rewriter srk) phi
    |> eliminate_ite srk
    |> Nonlinear.eliminate_floor_mod_div srk
    |> (rewrite
          srk
          ~up:(SrkSimplify.simplify_terms_rewriter srk % prop_rewriter solver))

  let unpropositionalize solver phi =
    substitute_const solver.srk (Hashtbl.find solver.unprop) phi

  let add solver phis =
    let propped = List.map (propositionalize solver) phis in
    Smt.Solver.add solver.sat propped;
    solver.asserts <- List.rev_append propped solver.asserts

  let get_model solver =
    let srk = solver.srk in
    let rec go () =
      match Smt.Solver.get_model solver.sat with
      | `Unsat -> `Unsat
      | `Unknown -> `Unknown
      | `Sat model ->
        (* Select a cube of the propositional skeleton *)
        let prop_implicant =
          List.fold_left
            (fun implicant phi ->
               match Interpretation.select_implicant model phi with
               | Some xs -> List.rev_append xs implicant
               | None -> assert false)
            []
            solver.asserts
        in
        (* Depropositionalize propositional cube, and add explicit integrality
           propositions for int-sorted symbols *)
        let cube =
          let (cube, ints) =
            List.fold_left (fun (cube, ints) prop_atom ->
                let atom = unpropositionalize solver prop_atom in
                let ints =
                  Symbol.Set.fold (fun sym ints ->
                      if Syntax.typ_symbol srk sym == `TyInt then
                        Symbol.Set.add sym ints
                      else
                        ints)
                    (symbols atom)
                    ints
                in
                (add_literal_to_cube srk atom cube, ints))
              (empty_cube, Symbol.Set.empty)
              prop_implicant
          in
          { cube with int =
                        Symbol.Set.fold (fun sym xs ->
                            (P.of_dim (int_of_symbol sym))::xs)
                          ints
                          cube.int }
        in
        match Model.get_model srk cube with
        | Some m -> `Sat m
        | None ->
          (* Block propositional implicant *)
          Smt.Solver.add solver.sat [mk_not srk (mk_and srk prop_implicant)];
          go ()
    in
    go ()
end

let get_model srk phi =
  let solver = Solver.mk_solver srk in
  Solver.add solver [phi];
  Solver.get_model solver

let is_sat srk phi =
  match get_model srk phi with
    `Sat _ -> `Sat
  | `Unsat -> `Unsat
  | `Unknown -> `Unknown

(* Given a operator cl mapping cones to cones such that (1) cl distributes
   over intersection and projection, (2) cl is extensive, find the closure of
   the non-negative cone of phi *)
let abstract cl srk phi = 
  let project =
    let phi_symbols = Syntax.symbols phi in
    fun i -> Syntax.Symbol.Set.mem (Syntax.symbol_of_int i) phi_symbols
  in
  let quantifiers, phi = get_quantifiers srk Env.empty phi in
  let term_of_dim dim = mk_const srk (symbol_of_int dim) in
  assert (BatList.for_all (fun (quant, _) -> quant == `Exists) quantifiers);
  let solver = Solver.mk_solver srk in
  let block pc =
    let blocking_clause =PolynomialCone.to_formula srk term_of_dim pc |> mk_not srk in
    logf "Block: %a" (Formula.pp srk) blocking_clause;
    Solver.add solver [blocking_clause]
  in
  let rec go current_pc =
    match Solver.get_model solver with
    | `Unsat -> current_pc
    | `Unknown -> assert false
    | `Sat m ->
      let poly_cone = cl (Model.nonnegative_cone m) in
      let projected_pc = PolynomialCone.project poly_cone project in
      let new_pc = PolynomialCone.intersection current_pc projected_pc in
      block new_pc;
      go new_pc
  in
  Solver.add solver [phi];
  go PolynomialCone.trivial

let find_consequences srk phi = abstract (fun x -> x) srk phi

let filter_polys_linear_in_dims dims polys =
  let polys_linear_in_dx = BatList.filter_map
      (fun poly -> let lin, higher = P.split_linear poly in
        let higher_contains_dx =
          BatEnum.exists
            (fun (_, mono) ->
               BatEnum.exists
                 (fun (dim, _) -> BatSet.Int.mem dim dims)
                 (Polynomial.Monomial.enum mono)
            )
            (P.enum higher)
        in
        if higher_contains_dx then None else Some (lin, higher)
      )
      polys
  in
  BatList.filter_map (fun (lin, higher) ->
      let linterm_of_only_dx_enum = BatEnum.filter_map (fun (coeff, dim) ->
          if BatSet.Int.mem dim dims then Some (coeff, dim) else None
        )
          (V.enum lin)
      in
      let linterm_of_only_dx = V.of_enum linterm_of_only_dx_enum in
      let p = P.of_vec linterm_of_only_dx in
      let other_linterm = V.sub lin linterm_of_only_dx in
      let other_poly = P.of_vec other_linterm in
      if V.is_zero linterm_of_only_dx then None else Some (P.add p (P.add other_poly higher))
    )
    polys_linear_in_dx

let project_down_to_linear pc lin_dims =
  let ideal = PolynomialCone.get_ideal pc in
  let ideal_gen = Polynomial.Rewrite.generators ideal in
  let lin_ideal = filter_polys_linear_in_dims lin_dims ideal_gen in
  (* let cone_gen = PolynomialCone.get_cone_generators pc in *)
  (* let lin_cone = filter_polys_linear_in_dims lin_dims cone_gen in *)
  let lin_cone = [] in
  let new_ideal = Polynomial.Rewrite.mk_rewrite (Polynomial.Rewrite.get_monomial_ordering ideal) lin_ideal in
  PolynomialCone.make_enclosing_cone new_ideal lin_cone

let find_linear_consequences srk phi lin_dims =
  abstract (fun cone -> project_down_to_linear cone lin_dims) srk phi
