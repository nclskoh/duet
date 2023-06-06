open BatEnum.Infix
module P = Polyhedron
module L = IntLattice
module V = Linear.QQVector
module LM = Linear.MakeLinearMap(QQ)(SrkUtil.Int)(V)(V)

module IntSet = SrkUtil.Int.Set

include Log.Make(struct let name = "abstractLia" end)

(** Abstract domain that supports symbolic abstraction *)
module type AbstractDomain = sig
  type t
  type context
  val context : context Syntax.context

  val bottom : t
  val join : t -> t -> t
  val concretize : t -> context Syntax.formula
  val abstract : context Syntax.formula -> context Interpretation.interpretation -> t

  val pp : Format.formatter -> t -> unit

end

module type Target = sig

  type context
  val context : context Syntax.context

  (** Symbols that the input formula is in *)
  val formula_symbols : Syntax.Symbol.Set.t

  (** Constraints of the integer hull are to be linear in these terms *)
  val terms : context Syntax.arith_term BatArray.t

end

(** Convert between implicants over [Target.formula_symbols] and
    constraints in some vector space, and between interpretations of the implicant
    and valuations of vectors in the vector space.
    [Target.terms] are mapped to the lowest dimensions in this vector space,
    and other symbols of the implicant are mapped to higher dimensions.

    - [valuation(interp)(i) = interp(Target.terms[i])]
 *)
module ImplicantConstraintConversion (Target : Target) : sig

  val dimensions_to_eliminate : int list

  val ambient_dimension : int

  val valuation : Target.context Interpretation.interpretation -> int -> Q.t

  val constraints_of_implicant :
    Target.context Syntax.formula list ->
    ([> `Nonneg | `Zero ] * V.t) list * V.t list

  val implicant_of_polyhedral_constraints :
    ([< `Nonneg | `Pos | `Zero ] * V.t) BatEnum.t -> Target.context Syntax.formula list

  val implicant_of_int_constraints :
    V.t BatEnum.t -> Target.context Syntax.formula list

end = struct

  let (basis, map_to_fresh_dims) =
    let open Syntax in
    let basis = BatDynArray.create () in
    let map =
      let neg_one = V.of_term QQ.one Linear.const_dim in
      BatArray.fold_lefti (fun map i t ->
          let vec = Linear.linterm_of Target.context t in
          BatDynArray.add basis vec;
          LM.may_add vec (V.of_term QQ.one i) map)
        (LM.add_exn neg_one neg_one LM.empty)
        Target.terms
      |> Symbol.Set.fold (fun symbol map ->
             if (Syntax.typ_symbol Target.context symbol <> `TyInt) then
               logf ~level:`always "Warning: Formula contains non-integer symbol %a; treating it as integer type"
                 (Syntax.pp_symbol Target.context) symbol
             else ();
             let symbol_vec = V.of_term QQ.one (Linear.dim_of_sym symbol) in
             let ambient_dim = BatDynArray.length basis in
             match LM.add symbol_vec (V.of_term QQ.one ambient_dim) map with
             | Some map' ->
                BatDynArray.add basis symbol_vec;
                map'
             | None -> map
           )
           Target.formula_symbols
    in (basis, map)

  let ambient_dimension = BatDynArray.length basis

  let dimensions_to_eliminate =
    let dim = Array.length Target.terms in
    BatList.of_enum (dim --^ ambient_dimension)

  let valuation interp i =
    Linear.evaluate_linterm
      (Interpretation.real interp)
      (BatDynArray.get basis i)

  let term_of_vector v =
    Linear.term_of_vec Target.context
      (fun i -> if i = Linear.const_dim then Syntax.mk_real Target.context QQ.one
                else Target.terms.(i)) v

  let atom_of_polyhedral_constraint (ckind, vector) =
    let zero = Syntax.mk_zero Target.context in
    let term = term_of_vector vector in
    let mk_compare cmp term = Syntax.mk_compare cmp Target.context zero term in
    match ckind with
    | `Zero -> mk_compare `Eq term
    | `Nonneg -> mk_compare `Leq term
    | `Pos -> mk_compare `Lt term

  let implicant_of_polyhedral_constraints cnstrnts =
    cnstrnts /@ atom_of_polyhedral_constraint |> BatList.of_enum

  let implicant_of_int_constraints cnstrnts =
    cnstrnts /@ (fun v -> Syntax.mk_is_int Target.context (term_of_vector v))
    |> BatList.of_enum

  let linearize t =
    try
      Linear.linterm_of Target.context t
    with Linear.Nonlinear ->
      let s = Format.asprintf "Term %a is not linear" (Syntax.ArithTerm.pp Target.context) t in
      failwith s

  let constraint_of_atom atom =
    let image v = LM.apply map_to_fresh_dims v |> BatOption.get in
    match atom with
    | `ArithComparison (`Lt, t1, t2) ->
       (* Assuming that all symbols are integer-valued *)
       let v = V.sub (linearize t2) (linearize t1) in
       let offset = QQ.inverse (QQ.of_zz (V.common_denominator v)) in
       let v' = V.sub v (V.of_term offset Linear.const_dim) in
       `Ineq (`Nonneg, image v')
    | `ArithComparison (`Leq, t1, t2) ->
       `Ineq (`Nonneg, image (V.sub (linearize t2) (linearize t1)))
    | `ArithComparison (`Eq, t1, t2) ->
       `Ineq (`Zero, image (V.sub (linearize t2) (linearize t1)))
    | `IsInt s ->
       `InLat (image (linearize s))
    | `Literal _
      | `ArrEq _ -> failwith "Cannot handle atoms"

  let constraints_of_implicant atoms =
    List.fold_left
      (fun (inequalities, lattice_constraints) atom ->
        match constraint_of_atom
                (Interpretation.destruct_atom Target.context atom) with
        | `Ineq cnstrnt -> (cnstrnt :: inequalities, lattice_constraints)
        | `InLat v -> (inequalities, v :: lattice_constraints)
      )
      ([], [])
      atoms

end

module IntHullProjection (Target : Target)
       : (AbstractDomain with type t = DD.closed DD.t
                          and type context = Target.context) = struct

  include ImplicantConstraintConversion(Target)

  type t = DD.closed DD.t
  type context = Target.context
  let context = Target.context

  let bottom = P.dd_of ambient_dimension P.bottom

  let join p1 p2 = DD.join p1 p2

  let concretize p =
    let p_formulas = implicant_of_polyhedral_constraints (DD.enum_constraints p) in
    Syntax.mk_and context p_formulas

  let abstract formula interp =
    let implicant =
      match Interpretation.select_implicant interp formula with
      | Some implicant -> implicant
      | None -> failwith "No implicant found" in
    let (inequalities, _lattice_constraints) = constraints_of_implicant implicant in
    let p = DD.of_constraints_closed ambient_dimension (BatList.enum inequalities) in
    let hull = DD.integer_hull p in
    DD.project dimensions_to_eliminate hull

  let pp fmt p =
    Format.fprintf fmt "{ polyhedron : %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p

end

module IntegerMbp : sig

  val local_project_cooper :
    (int -> QQ.t) -> eliminate:(int list) ->
    Polyhedron.t * IntLattice.t -> Polyhedron.t * IntLattice.t

end = struct

  let normalize a dim =
    let c = V.coeff dim a in
    if QQ.equal c QQ.zero then a
    else V.scalar_mul (QQ.inverse (QQ.abs c)) a

  let get_bound dim v =
    let drop_dim v = V.pivot dim v |> snd in
    if QQ.lt (V.coeff dim v) Q.zero then
      normalize v dim |> drop_dim
    else if QQ.lt Q.zero (V.coeff dim v) then
      normalize v dim |> drop_dim |> V.negate
    else
      failwith "Vector is 0 in the dimension"

  let evaluate_bound dim v m =
    Linear.evaluate_affine m (get_bound dim v)

  let substitute_term t dim v =
    let (c, v') = V.pivot dim v in
    V.add v' (V.scalar_mul c t)

  (* A classified system of constraints with respect to a chosen dimension x and
   a model m contains:
   - The row a^T Y + cx + b >= 0 (or = 0) that gives the glb, if one exists,
     where c is positive
   - All rows that involve x
   - All rows that don't involve x
   *)
  type classified =
    {
      glb_row : (QQ.t * P.constraint_kind * V.t) option
    ; relevant : (P.constraint_kind * V.t) BatEnum.t
    ; irrelevant : (P.constraint_kind * V.t) BatEnum.t
    }

  let classify_constraints m dim constraints =
    BatEnum.fold (fun (classified, upper_bound_seen) (kind, v) ->
        if QQ.equal (V.coeff dim v) QQ.zero then
          begin
            BatEnum.push classified.irrelevant (kind, v);
            (classified, upper_bound_seen)
          end
        else if QQ.lt (V.coeff dim v) QQ.zero then
          begin
            BatEnum.push classified.relevant (kind, v);
            (classified, true)
          end
        else
          begin
            BatEnum.push classified.relevant (kind, v);
            let value = evaluate_bound dim v m in
            match classified.glb_row with
            | None ->
               ({ classified with glb_row = Some (value, kind, v) }, upper_bound_seen)
            | Some (curr_best, curr_kind, _) ->
               if QQ.lt curr_best value ||
                    (QQ.equal curr_best value && curr_kind = `Nonneg && kind = `Pos) then
                 ({ classified with glb_row = Some (value, kind, v) }, upper_bound_seen)
               else
                 (classified, upper_bound_seen)
          end
      )
      ({
          glb_row = None
        ; relevant = BatEnum.empty ()
        ; irrelevant = BatEnum.empty ()
        }, false)
      constraints

  let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

  let local_project_cooper m ~eliminate (p, l) =
    BatList.fold_left (fun (p, l) dim ->
        let (classified, has_upper_bound) =
          classify_constraints m dim (P.enum_constraints p) in
        if not (has_upper_bound) || classified.glb_row = None then
          ( P.of_constraints classified.irrelevant
          , IntLattice.project (fun dim -> not (BatList.mem dim eliminate)) l )
        else
          let glb_term =
            let (_, _, glb_row) = Option.get classified.glb_row in
            get_bound dim glb_row
          in
          let divisor =
            BatList.fold_left
              (fun m v ->
                let coeff = Linear.QQVector.coeff dim v in
                if QQ.equal coeff QQ.zero then m
                else ZZ.lcm m (QQ.denominator coeff))
              ZZ.one
              (L.basis l)
          in
          let difference = QQ.sub (m dim) (Linear.evaluate_affine m glb_term) in
          let residue = QQ.modulo difference (QQ.of_zz divisor) in
          let solution = V.add_term residue Linear.const_dim glb_term in
          logf ~level:`trace "glb value %a <= point %a, difference %a, divisor %a, residue %a@."
            QQ.pp (Linear.evaluate_affine m glb_term) QQ.pp (m dim)
            QQ.pp difference QQ.pp (QQ.of_zz divisor) QQ.pp residue;
          logf ~level:`trace "glb term %a@." V.pp glb_term;
          logf ~level:`trace "selected term %a, <= %a:1@." V.pp solution pp_dim dim;
          let new_p =
            classified.relevant
            /@ (fun (kind, a) ->
              (kind, substitute_term solution dim a))
            |> BatEnum.append classified.irrelevant
            |> P.of_constraints in
          let new_l =
            List.map (substitute_term solution dim) (IntLattice.basis l)
            |> IntLattice.hermitize
          in
          (new_p, new_l)
      ) (p, l) eliminate

end

module LatticePolyhedron : sig

  val lattice_polyhedron_of : P.t -> IntLattice.t -> P.t

end = struct

  module T = Linear.MakeLinearMap(QQ)(Int)(V)(V)

  let pp_linear_map fmt linear_map =
    BatEnum.iter (fun (s, t) ->
        Format.fprintf fmt "(%a, %a); " Linear.QQVector.pp s Linear.QQVector.pp t)
      (T.enum linear_map)

  let force_transform (forward, inverse, num_dimensions) p =
    let q = BatEnum.empty () in
    let (forward, inverse, num_dimensions) =
      BatEnum.fold
        (fun (forward, inverse, num_dimensions) (kind, v) ->
          match T.apply forward v with
          | None ->
             let image = V.of_term QQ.one num_dimensions in
             BatEnum.push q (kind, image);
             let new_forward =
               match T.add v image forward with
               | Some forward' -> forward'
               | None ->
                  logf ~level:`always
                    "force_transform forward: %a is already in the domain of %a@."
                    Linear.QQVector.pp v pp_linear_map forward;
                 failwith "force_transform: forward extension conflict"
             in
             let new_backward =
               match T.add image v inverse with
               | Some backward' -> backward'
               | None ->
                  logf ~level:`always
                    "force_transform inverse: %a is already in the domain of %a@."
                    Linear.QQVector.pp image pp_linear_map inverse;
                  failwith "force_transform: inverse extension conflict"
             in
             ( new_forward, new_backward, num_dimensions + 1)
          | Some image ->
             BatEnum.push q (kind, image);
             (forward, inverse, num_dimensions)
        )
        (forward, inverse, num_dimensions)
        (P.enum_constraints p)
    in
    (forward, inverse, num_dimensions, P.of_constraints q)

  let transform map p =
    let q = BatEnum.empty () in
    BatEnum.iter (fun (kind, v) ->
        match T.apply map v with
        | None -> failwith "transformation is malformed"
        | Some image ->
           BatEnum.push q (kind, image)
      )
      (P.enum_constraints p);
    P.of_constraints q

  let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

  let lattice_polyhedron_of p l =
    let basis = IntLattice.basis l in
    let (forward_l, inverse_l, num_dimensions_l) =
      List.fold_left (fun (forward, inverse, index) v ->
          let f = T.may_add v (V.of_term QQ.one index) forward in
          let b = T.may_add (V.of_term QQ.one index) v inverse in
          (f, b, index + 1))
        ( T.may_add (V.of_term QQ.one Linear.const_dim)
            (V.of_term QQ.one Linear.const_dim) T.empty
        , T.may_add (V.of_term QQ.one Linear.const_dim)
            (V.of_term QQ.one Linear.const_dim) T.empty
        , 0)
        basis
    in
    logf ~level:`trace "Transform computed so far is %a@." pp_linear_map forward_l;
    logf ~level:`trace
      "Forcing transform on polyhedron %a@." (Polyhedron.pp pp_dim) p;
    let (_forward, inverse, _num_dimensions, q) =
      force_transform (forward_l, inverse_l, num_dimensions_l) p
    in
    logf ~level:`trace "Forced transform, obtained %a@." (Polyhedron.pp pp_dim) q;
    let hull = Polyhedron.integer_hull `GomoryChvatal q in
    logf ~level:`trace "standard integer hull is %a@." (Polyhedron.pp pp_dim) hull;
    transform inverse hull

end

module CooperProjection (Target : Target)
       : (AbstractDomain with type t = DD.closed DD.t * IntLattice.t
                          and type context = Target.context) = struct

  include ImplicantConstraintConversion(Target)

  (* (P, L) s.t. P is integral with respect to the lattice satisfying L.
     L is the lattice generated by the vectors in Int(-), i.e., it is the
     dual lattice.
   *)
  type t = DD.closed DD.t * IntLattice.t

  type context = Target.context
  let context = Target.context

  let bottom = ( P.dd_of ambient_dimension P.bottom
               , IntLattice.hermitize [V.of_term QQ.one Linear.const_dim]
               )

  let join (p1, l1) (p2, l2) = (DD.join p1 p2, IntLattice.intersect l1 l2)

  let concretize (p, l) =
    let p_formulas = implicant_of_polyhedral_constraints (DD.enum_constraints p) in
    let l_formulas = implicant_of_int_constraints (BatList.enum (IntLattice.basis l)) in
    Syntax.mk_and Target.context (p_formulas @ l_formulas)

  let pp_dim = fun fmt d -> Format.fprintf fmt "%d" d

  let abstract formula interp =
    let implicant = match Interpretation.select_implicant interp formula with
      | Some implicant -> implicant
      | None -> failwith "No implicant found" in
    let (inequalities, lattice_constraints) = constraints_of_implicant implicant in
    let p = P.of_constraints (BatList.enum inequalities) in
    let l =
      let symbol_dimensions = (0 --^ ambient_dimension)
                              /@ V.of_term QQ.one
                              |> BatList.of_enum in
      logf "symbol dimensions: %a ambient dimension:%d@."
        (Format.pp_print_list V.pp) symbol_dimensions
        ambient_dimension;
      logf "lattice constraints: %a@." (Format.pp_print_list V.pp)
        lattice_constraints;
      IntLattice.hermitize (lattice_constraints @ symbol_dimensions)
    in
    logf "Polyhedron to project: %a@." (Polyhedron.pp pp_dim) p;
    logf "Lattice: %a@." IntLattice.pp l;
    logf "Dimensions to eliminate: %a@."
      (Format.pp_print_list Format.pp_print_int) dimensions_to_eliminate;
    let (projected_p, projected_l) =
      IntegerMbp.local_project_cooper (valuation interp)
        ~eliminate:dimensions_to_eliminate (p, l) in
    logf "Polyhedron after projection: %a@."
      (Polyhedron.pp pp_dim) projected_p;
    logf "Lattice after projection: %a@."
      IntLattice.pp projected_l;
    logf "Computing lattice polyhedron...@;";
    let hull = LatticePolyhedron.lattice_polyhedron_of projected_p projected_l in
    logf "Computed lattice polyhedron: %a@." (P.pp pp_dim) hull;
    ( DD.of_constraints_closed ambient_dimension (P.enum_constraints hull)
    , projected_l)

  let pp fmt (p, l) =
    Format.fprintf fmt "{ polyhedron : %a @. lattice: %a }"
      (DD.pp (fun fmt d -> Format.fprintf fmt "%d" d)) p
      IntLattice.pp l

end

module Abstract (A : AbstractDomain) : sig

  val abstract : A.context Syntax.formula -> A.t

end = struct

  let init formula =
    let solver = Smt.mk_solver A.context in
    Smt.Solver.add solver [formula];
    (solver, A.bottom)

  let abstract formula =
    let (solver, initial_value) = init formula in
    let rec go n value =
      logf "Iteration %d@." n;
      match Smt.Solver.get_model solver with
      | `Sat interp ->
         let rho = A.abstract formula interp in
         logf "abstract: abstracted, now joining";
         let joined = A.join value rho in
         logf "abstract: joining rho %a with %a to get %a@."
           A.pp rho
           A.pp value
           A.pp joined;
         let formula = A.concretize joined in
         logf "abstract: new constraint to negate: %a@."
           (Syntax.pp_smtlib2 A.context) formula;
         Smt.Solver.add solver
           [Syntax.mk_not A.context formula];
         go (n + 1) joined
      | `Unsat ->
         value
      | `Unknown -> failwith "Can't get model"
    in go 1 initial_value

end

let integer_hull (type a) (srk : a Syntax.context) ~how (phi : a Syntax.formula)
      terms =
  let module Target = struct
      type context = a
      let context = srk
      let formula_symbols = Syntax.symbols phi
      let terms = terms
    end in
  match how with
  | `Standard ->
     let module Compute = Abstract(IntHullProjection(Target)) in
     Compute.abstract phi
  | `Cooper ->
     let module Compute = Abstract(CooperProjection(Target)) in
     fst (Compute.abstract phi)
  | `Cone ->
     failwith "Not implemented yet"
