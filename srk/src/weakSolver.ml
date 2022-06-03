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

module PVCTX = PolynomialUtil.PolyVectorContext
module PV = PolynomialUtil.PolyVectorConversion

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
      | `Atom (`Arith (`Eq, s, t)) -> `Nonzero (sub t s)
      | `Atom (`Arith (`Leq, s, t)) -> `Neg (sub t s)   (* !(x <= y) <=> y - x < 0 *)
      | `Atom (`Arith (`Lt, s, t)) -> `Nonneg (sub s t) (*  !(x < y) <=> 0 <= x - y *)
      | `Atom (`IsInt s) -> `NonInt (P.of_term srk s)
      | _ -> invalid_arg (Format.asprintf "destruct_literal: %a is not recognized"
                            (Formula.pp srk) phi)
    end
  | `Tru -> `Zero P.zero
  | `Fls -> `Zero P.one
  | _ ->
    invalid_arg (Format.asprintf "destruct_literal: %a is not recognized"
                   (Formula.pp srk) phi)

(* Polynomial combination of proposition identifiers *)
module W = Polynomial.Witness

(* List of propositions that appear with a non-zero coefficient in witness *)
let core_of_witness srk witness =
  BatEnum.fold
    (fun core (_, id) -> (mk_const srk (symbol_of_int id)::core))
    []
    (W.enum witness)

let destruct_prop_literal srk lit =
  match Formula.destruct srk lit with
  | `Proposition (`App (k, [])) -> (false, k)
  | `Not phi ->
    begin match Formula.destruct srk phi with
      | `Proposition (`App (k, [])) -> (true, k)
      | _ -> invalid_arg "destruct_prop_literal: not a propositional literal"
    end
  | _ -> invalid_arg "destruct_prop_literal: not a propositional literal"


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

  let make ~cone ~lattice ~pos = { cone; lattice; pos }

  let nonnegative_cone m = m.cone

  let is_int m p =
    PolynomialConeCpClosure.in_polylattice p m.lattice

  let is_nonneg m p = PolynomialCone.mem p m.cone

  let is_zero m p =
    Polynomial.Rewrite.reduce (PolynomialCone.get_ideal m.cone) p
    |> P.equal P.zero

  let is_true_prop m k = Symbol.Set.mem k m.pos

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

  (* Replace atoms with boolean proposition.  If an atom is *already* an
     boolean proposition, do nothing.  *)
  let prop_rewriter solver expr =
    let srk = solver.srk in
    let zero = mk_zero solver.srk in
    let prop_of_atom phi =
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
    match Expr.refine srk expr with
    | `ArithTerm _ | `ArrTerm _ -> expr
    | `Formula phi ->
      let term_of_dim dim = mk_const srk (symbol_of_int dim) in
      let term_of = P.term_of srk term_of_dim in
      match Formula.destruct srk phi with
      | `Atom _ ->
        let prop =
          match destruct_literal srk phi with
          | `Zero p -> prop_of_atom (mk_eq srk zero (term_of p))
          | `Nonneg p -> prop_of_atom (mk_leq srk zero (term_of p))
          | `Neg p -> mk_not srk (prop_of_atom (mk_leq srk zero (term_of p)))
          | `Nonzero p -> mk_not srk (prop_of_atom (mk_leq srk zero (term_of p)))
          | `IsInt p -> prop_of_atom (mk_is_int srk (term_of p))
          | `NonInt p -> mk_not srk (prop_of_atom (mk_is_int srk (term_of p)))
          | `True k -> mk_const srk k
          | `False k -> mk_not srk (mk_const srk k)
        in
        (prop :> ('a, typ_fo) expr)
      | _ -> expr

  let propositionalize solver phi =
    let srk = solver.srk in
    eliminate_ite srk phi
    |> Nonlinear.eliminate_floor_mod_div srk
    |> rewrite srk ~down:(nnf_rewriter srk) ~up:(prop_rewriter solver)

  let propositionalize_atom solver phi =
    match Expr.refine solver.srk (prop_rewriter solver (phi :> ('a, typ_fo) expr)) with
    | `Formula phi -> phi
    | _ -> assert false

  let unpropositionalize solver phi =
    let unprop symbol =
      try Hashtbl.find solver.unprop symbol
      with Not_found -> mk_const solver.srk symbol
    in
    substitute_const solver.srk unprop phi

  let add solver phis =
    let propped = List.map (propositionalize solver) phis in
    Smt.Solver.add solver.sat propped;
    solver.asserts <- List.rev_append propped solver.asserts

  let ( let* ) o f =
    match o with
    | `Unsat core -> `Unsat core
    | `Sat r -> f r

  let ok = `Sat ()

  let check_all f array =
    let len = BatDynArray.length array in
    let rec loop i =
      if i < len then
        let* _ = f (BatDynArray.get array i) in
        loop (i + 1)
      else
        ok
    in
    loop 0

  let rev_mapm f xs =
    let rec loop acc = function
      | [] -> `Sat acc
      | (x::xs) ->
        let* y = f x in
        loop (y::acc) xs
    in
    loop [] xs

  module RR = Polynomial.RewriteWitness

  let vectorize positive =
    let ctx =
      BatDynArray.fold_left (fun xs p -> (fst p)::xs) [] positive
      |> PVCTX.mk_context Monomial.degrevlex
    in
    let rays =
      Array.init
        (BatDynArray.length positive)
        (fun i -> PV.poly_to_vector ctx (fst (BatDynArray.get positive i)))
    in
    (ctx, rays)

  (* arr is an array of (polynomial, witness) pairs and u is a linear
     combination of the indices of arr.  Compute the corresponding linear
     combination of witnesses *)
  let combine_witness arr u =
    BatEnum.fold
      (fun w (coeff, i) ->
         W.add w (W.scalar_mul (P.scalar coeff) (snd (BatDynArray.get arr i))))
      W.zero
      (V.enum u)

  (* Compute proper ideal generated by the given set of polynomials.  Returns
     unsat core if the ideal is not proper. *)
  let proper_ideal srk zero =
    let rewrite =
      RR.mk_rewrite Polynomial.Monomial.degrevlex zero
      |> RR.grobner_basis
    in
    (* Test if equations are feasible *)
    match RR.zero_witness rewrite P.one with
    | Some witness -> `Unsat (core_of_witness srk witness)
    | None -> `Sat rewrite

  (* Compute smallest regular cone containing positive and the ideal generated
     by zero.  Returns an unsat core if the resulting regular cone is trivial.
     This procedure may allocate additional propositions that represent
     discovered equalities -- if it does, a supporting propositional lemma is
     added to the solver.  *)
  let regularize solver zero positive =
    let srk = solver.srk in
    let* rewrite = proper_ideal srk zero in
    let term_of_dim dim = mk_const srk (symbol_of_int dim) in
    let term_of = P.term_of srk term_of_dim in
    let lineality positive =
      let (ctx, rays) = vectorize positive in
      let dim = PVCTX.num_dimensions ctx in
      let linear_cone = Cone.make ~lines:[] ~rays:(Array.to_list rays) dim in
      Cone.normalize linear_cone;
      Cone.lines linear_cone
      |> rev_mapm (fun line ->
          match Cone.simplex rays line, Cone.simplex rays (V.negate line) with
          | Some u, Some v ->
            let line_poly = PV.vector_to_poly ctx line in
            let witness =
              W.add (combine_witness positive u) (combine_witness positive v)
            in
            (* If line is a non-zero constant, the cone is trivial. *)
            if not (P.equal P.zero line_poly) && P.degree line_poly == 0 then
              `Unsat (core_of_witness srk witness)
            else
              (* Allocate an new proposition for line: it is supported by the
                 propositions that witness line and its negation line.  *)
              let line_prop =
                propositionalize_atom solver
                  (mk_eq srk (mk_zero srk) (term_of line_poly))
              in
              let line_prop_id =
                int_of_symbol (snd (destruct_prop_literal srk line_prop))
              in
              Smt.Solver.add solver.sat [mk_if srk
                                           (mk_and srk (core_of_witness srk witness))
                                           line_prop];
              `Sat (PV.vector_to_poly ctx line, W.of_list [(P.one, line_prop_id)])
          | _, _ -> assert false)
    in
    let rec loop zero positive =
      let* lines = lineality positive in
      if lines == [] then `Sat (zero, positive)
      else
        let zero =
          BatList.fold_left
            (fun zero (z,w) -> RR.add_saturate zero z w)
            zero
            lines
        in
        BatDynArray.modify (RR.reducew zero) positive;
        BatDynArray.keep (fun (p, _) -> not (P.equal P.zero p)) positive;
        loop zero positive
    in

    BatDynArray.modify (RR.reducew rewrite) positive;
    BatDynArray.keep (fun (p, _) -> not (P.equal P.zero p)) positive;

    let* (zero, positive) = loop rewrite positive in
    match RR.zero_witness zero P.one with
    | Some w -> `Unsat (core_of_witness srk w)
    | None -> `Sat (zero, positive)

  (* Depropositionalize a propositional cube and compute a minimal model, if
     possible.  Assumes prop_cube is propositionally satisfiable. *)
  let model_of_prop_cube solver prop_cube =
    let zero = BatDynArray.create () in
    let nonneg = BatDynArray.create () in
    let int = BatDynArray.create () in
    let pos = ref Symbol.Set.empty in
    let not_int = BatDynArray.create () in
    let not_zero = BatDynArray.create () in
    let not_nonneg = BatDynArray.create () in
    let int_symbols = ref Symbol.Set.empty in
    let srk = solver.srk in

    (* 1 is nonnegative without need for a witness *)
    BatDynArray.add nonneg (P.one, W.zero);

    prop_cube |> List.iter (fun prop_lit ->
        let lit = unpropositionalize solver prop_lit in
        let (_, sym) = destruct_prop_literal srk prop_lit in
        symbols lit |> Symbol.Set.iter (fun sym ->
            if Syntax.typ_symbol srk sym == `TyInt then
              int_symbols := Symbol.Set.add sym (!int_symbols));

        let w = W.of_list [(P.one, int_of_symbol sym)] in
        match destruct_literal srk lit with
        | `Zero z -> BatDynArray.add zero (z, w)
        | `Nonneg p -> BatDynArray.add nonneg (p, w)
        | `IsInt m -> BatDynArray.add int (m, w)
        | `Neg n -> BatDynArray.add not_nonneg (n, prop_lit)
        | `Nonzero q -> BatDynArray.add not_zero (q, prop_lit)
        | `NonInt m -> BatDynArray.add not_int (m, prop_lit)
        | `True k -> pos := Symbol.Set.add k (!pos)
        | `False _ ->
          (* Since prop_cube is propositionally satisfiable, we can simply
             ignore negative propositions *)
          ());

    (* Add integrality constraints for int-sorted symbols *)
    (!int_symbols) |> Symbol.Set.iter (fun sym ->
        (* No witness required, since int constraint is implicit *)
        BatDynArray.add int (P.of_dim (int_of_symbol sym), W.zero));

    let* (rewrite, positive) = regularize solver (BatDynArray.to_list zero) nonneg in
    let* _ =
      (* Test for unsatisfied disequality *)
      not_zero |> check_all (fun (p, lit) ->
          match RR.zero_witness rewrite p with
          | Some w -> `Unsat (lit :: (core_of_witness srk w))
          | None -> ok)
    in
    let* _ =
      (* Test for unsatisfied negative inequality *)
      let (ctx, rays) = vectorize positive in
      not_nonneg |> check_all (fun (p, lit) ->
          try
            let (p', w) = RR.reduce rewrite p in
            match Cone.simplex rays (PV.poly_to_vector ctx p') with
            | Some u ->
              let w = W.add w (combine_witness positive u) in
              `Unsat (lit :: (core_of_witness srk w))
            | None -> ok
          with PVCTX.Not_in_context ->
            (* p' is not in the span of the monomials that appear in the
               positive cone, and so does not belong to the cone *)
            ok)
    in
    let pc =
      PolynomialCone.make_cone
        (RR.forget rewrite)
        (BatDynArray.fold_left (fun xs p -> (fst p)::xs) [] positive)
    in
    logf ~level:`trace "Enclosing regular cone: @[%a@]"
      (PolynomialCone.pp (pp_dim srk)) pc;

    (* All positive atoms.  Unsat cores extend positive atoms with an
       unsatisfied negative atom. *)
    let positive_atoms =
      let add array xs =
        BatDynArray.fold_left (fun atoms (_, w) ->
            List.rev_append (core_of_witness srk w) atoms)
          xs
          array
      in
      add int [] |> add zero |> add nonneg
    in
    let (cut_pc, lattice) =
      PolynomialConeCpClosure.regular_cutting_plane_closure
        pc (List.map fst (BatDynArray.to_list int))
    in
    if PolynomialCone.is_proper cut_pc then
      (* Model is least Z-model that satisfies all positive atoms. *)
      let model = Model.make ~cone:cut_pc ~lattice ~pos:(!pos) in

      (* Check all negative literals.  If they are not satisfied by the model,
         we get an unsat core by adding it to the set of postive atoms. *)
      let* _ =
        not_zero |> check_all (fun (p, lit) ->
            if Model.is_zero model p then `Unsat (lit::positive_atoms)
            else ok)
      in
      let* _ =
        not_int |> check_all (fun (p, lit) ->
            if Model.is_int model p then `Unsat (lit::positive_atoms)
            else ok)
      in
      let* _ =
        not_nonneg |> check_all (fun (p, lit) ->
            if Model.is_nonneg model p then `Unsat (lit::positive_atoms)
            else ok)
      in
      `Sat model
    else
      `Unsat positive_atoms

  let get_model solver =
    let srk = solver.srk in
    let rec go () =
      match Log.time "SAT solving" Smt.Solver.get_model solver.sat with
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
        match model_of_prop_cube solver prop_implicant with
        | `Sat m -> `Sat m
        | `Unsat cube ->
          Smt.Solver.add solver.sat [mk_not srk (mk_and srk cube)];
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
    let blocking_clause =
      PolynomialCone.to_formula srk term_of_dim pc
      |> mk_not srk
    in
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
      block (Model.nonnegative_cone m);
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