open Syntax
open BatPervasives

include Log.Make (struct let name = "ConvexHull" end)

module Solver = Abstract.Solver
module V = Linear.QQVector
module LM = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(V)(V)
module QQXs = Polynomial.QQXs
module I = Polynomial.Rewrite
module Plt = PolyhedronLatticeTiling

type t = DD.closed DD.t

let enable_lira = ref true

let nb_hulls = ref 0
let dump_hull = ref false
let dump_hull_prefix = ref ""

(** Low-level interface that assumes formula is in the right form for Plt.convex_hull:
    for LIRA, this means integrality constraints for the integer-typed variables in the
    formula are explicitly present in the formula,
    and for LRA relaxation, this means the formula is in LRA with no LIA terms like
    [mod], no [Int] literals, and all variables are of type [`TyReal].
 *)
let of_model_lira solver man terms model =
  match !enable_lira with
  | true ->
     Plt.convex_hull_of_lira_model (SubspaceCone `Standard) ~man
       solver terms model
  | false ->
     Plt.convex_hull_of_lira_model (ProjectImplicant (`AssumeReal `Lw)) ~man
       solver terms model
     (*
     let srk = Solver.get_context solver in
     let phi = Solver.get_formula solver in
     (* Map linear terms over the symbols in phi to the range [-1, n], such that
     -1 -> -1, 0 -> term(0), ... n -> term(n).
     dim_constraints is the set of linear relations among -1, term(0), ..., term(n)
      *)
     let basis = BatDynArray.create () in
     let dim_constraints = BatEnum.empty () in
     let map =
       let neg_one = V.of_term QQ.one Linear.const_dim in
       BatArray.fold_lefti (fun map i t ->
           let vec = Linear.linterm_of srk t in
           BatDynArray.add basis vec;
           match LM.add vec (V.of_term QQ.one i) map with
           | Some map -> map
           | None ->
              (* vec already belongs to the domain of map.  Add a constraint that
             i = map(vec) *)
              let v = match LM.apply map vec with
                | Some v -> v
                | None -> assert false
              in
              BatEnum.push dim_constraints (`Zero, V.add_term (QQ.of_int (-1)) i v);
              map)
         (LM.add_exn neg_one neg_one LM.empty)
         terms
       |> Symbol.Set.fold (fun symbol map ->
              let symbol_vec = V.of_term QQ.one (Linear.dim_of_sym symbol) in
              let ambient_dim = BatDynArray.length basis in
              match LM.add symbol_vec (V.of_term QQ.one ambient_dim) map with
              | Some map' ->
                 BatDynArray.add basis symbol_vec;
                 map'
              | None -> map)
            (symbols phi)
     in
     let dim = Array.length terms in
     let elim_dims = BatList.of_enum (dim -- (BatDynArray.length basis)) in
     let dim_constraint_polyhedron = Polyhedron.of_constraints dim_constraints in
     function
     | `LIRR _ -> assert false
     | `LIRA interp ->
        let cube =
          match Interpretation.select_implicant interp phi with
          | Some cube ->
             let constraints = BatEnum.empty () in
             BatList.iter (fun atom ->
                 match Interpretation.destruct_atom srk atom with
                 | `ArithComparison (p, x, y) ->
                    let t =
                      V.sub (Linear.linterm_of srk y) (Linear.linterm_of srk x)
                      |> LM.apply map
                      |> BatOption.get
                    in
                    let p = match p with `Eq -> `Zero | `Leq -> `Nonneg | `Lt -> `Pos in
                    BatEnum.push constraints (p, t)
                 | _ -> ())
               cube;
             Polyhedron.of_constraints constraints
          | None -> assert false
        in
        let valuation i =
          Linear.evaluate_linterm
            (Interpretation.real interp)
            (BatDynArray.get basis i)
        in
        Polyhedron.local_project valuation elim_dims cube
        |> Polyhedron.meet dim_constraint_polyhedron
        (* NK: Shouldn't the meet be before projection? *)
        |> Polyhedron.dd_of ~man dim
      *)

let of_model_lirr solver man terms =
  let srk = Solver.get_context solver in
  let poly_terms = Array.map (QQXs.of_term srk) terms in
  let dim = Array.length terms in
  function
  | `LIRA _ -> assert false
  | `LIRR m ->
    let cone = Lirr.Model.nonnegative_cone m in
    let map_cone = PolynomialCone.inverse_image cone poly_terms in
    let constraints = BatEnum.empty () in
    I.generators (PolynomialCone.get_ideal map_cone)
    |> List.iter (fun p ->
        match QQXs.vec_of p with
        | Some vec -> BatEnum.push constraints (`Zero, vec)
        | None -> ());
    PolynomialCone.get_cone_generators map_cone
    |> List.iter (fun p ->
        match QQXs.vec_of p with
        | Some vec -> BatEnum.push constraints (`Nonneg, vec)
        | None -> ());
    DD.of_constraints_closed ~man dim constraints

let abstract solver ?(man=Polka.manager_alloc_loose ()) ?(bottom=None) terms =
  if !dump_hull then begin
      let phi = Abstract.Solver.get_formula solver in
      let srk = Abstract.Solver.get_context solver in
      let query =
        List.fold_left (fun definitions term ->
            let s = mk_symbol srk ?name:(Some "term_to_project_onto") `TyReal
            in
            (Syntax.mk_eq srk (Syntax.mk_const srk s) term :: definitions)
          )
          []
          (Array.to_list terms)
        |> Syntax.mk_and srk
        |> (fun phi' -> Syntax.mk_and srk [phi ; phi'])
      in
      let query =
        Symbol.Set.fold (fun s psi -> Syntax.mk_exists_const srk s psi)
          (symbols phi)
          query
      in
      let filename =
        Format.sprintf "%shull%d.smt2" (!dump_hull_prefix) (!nb_hulls)
      in
      let chan = Stdlib.open_out filename in
      let formatter = Format.formatter_of_out_channel chan in
      logf ~level:`always "Writing convex hull query to %s" filename;
      Syntax.pp_smtlib2 srk formatter query;
      Format.pp_print_newline formatter ();
      Stdlib.close_out chan;
      incr nb_hulls
    end;

  match Solver.get_theory solver with
  | `LIRR ->
     let join = DD.join in
     let dim = Array.length terms in
     let srk = Solver.get_context solver in
     let top = DD.of_constraints_closed ~man dim (BatEnum.empty ()) in
     let bottom = match bottom with
       | Some bot -> bot
       | None ->
          let inconsistent = (* 0 = 1 *)
            BatEnum.singleton (`Zero, V.of_term QQ.one Linear.const_dim)
          in
          DD.of_constraints_closed ~man dim inconsistent
     in
     let term_of_dim i =
       if i == Linear.const_dim then mk_one srk else terms.(i)
     in
     let formula_of prop =
       DD.enum_constraints_closed prop
       /@ (fun (kind, v) ->
         let t = Linear.term_of_vec srk term_of_dim v in
         match kind with
         | `Zero -> mk_eq srk (mk_zero srk) t
         | `Nonneg -> mk_leq srk (mk_zero srk) t)
       |> BatList.of_enum
       |> mk_and srk
     in
     let of_model = of_model_lirr solver man terms in
     let domain =
       Abstract.{ join; top; of_model; bottom; formula_of }
     in
     Solver.abstract solver domain
  | `LIRA ->
     match !enable_lira with
     | true ->
        let srk = Solver.get_context solver in
        let phi = Solver.get_formula solver in
        Solver.add solver [Syntax.mk_and srk (Syntax.explicit_ints srk phi)];
        Plt.abstract (SubspaceCone `Standard) ~man ~bottom solver terms
     | false ->
        (* The caller should probably be responsible for relaxing the formula
           in the solver.
         *)
        let srk = Solver.get_context solver in
        let phi = Solver.get_formula solver in
        Plt.convex_hull_of_real_relaxation `Lw ~man srk phi terms

let conv_hull ?(man=Polka.manager_alloc_loose ()) srk phi terms =
  match !enable_lira with
  | true ->
     let phi_with_ints = Syntax.mk_and srk (Syntax.explicit_ints srk phi) in
     Plt.convex_hull (SubspaceCone `Standard) ~man srk phi_with_ints terms
  | false ->
     Plt.convex_hull_of_real_relaxation `Lw ~man srk phi terms
