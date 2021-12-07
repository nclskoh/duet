(**

   L = (0, 1, +, -/1, floor, =, <, <=, = mod k)

   E.g.:-

   forall x1 x2. exists x3.
     (x1 = floor(x1)
     /\ x2 = floor(x2)
     /\ (3 + 1) * x1 < floor(2 * x3)
     /\ floor(x3) + floor(x3) < 2 * x2
     /\ x3 = 1 mod 2)

   Algorithm:

    1. \exists x. \psi ---> \exists xi. \exists u. \psi[x |-> xi + u]

    2. \exists xi/u. \psi --->

       a. Make terms into PA and LRA terms, which are of the form
          [n * xi + s] or [n * u + s], where [s] is free of [xi] or [u].

          - 0, 1, variable ---> unchanged
          - c * x, x * c ---> simplify constants
          - T + T ---> recurse, group 'like' parts, simplify constants
          - floor(T) --->
            - Recurse on T to get [T = n * xi + s] or [T = nu + s].
            - Check sort of xi/u
            - If xi, distribute floor to get [nu + floor(s)].
            - If u, [s <= nu + s < n + s] or [n + s < nu + s <= s], so
              [floor(nu + s) = floor(s), 1 + floor(s), ..., n + floor(s)], or
              [floor(nu + s) = n + floor(s), (n + 1) + floor(s), ..., floor(s)].

              For substitution QE: replace [floor(nu + s)] in the formula here
              with [k + floor(s)] and restart (a).

              For implementation: generalize "term-purification" algorithm to
              return a set of terms, and these possibilities are returned.

          Result: all terms are of the form [n * xi + floor(s)] or
          [n * u + floor(s)].

       b. Make atomic formulas into PA and LRA formulas:

          i. Normalize all atoms to be of the form [n xi R s], [nu R s],
             or [s R t] with s, t free of xi/u.

          ii. Rewrite atomic formulas containing xi/u.

          - n xi = s ---> n xi = floor(s) /\ s = floor(s)
          - n u = s ---> unchanged
          - n xi < s ---> n xi < floor(s) \/ (n xi = floor(s) /\ floor(s) < s)
          - n u < s ---> unchanged
          - n xi <= s ---> n xi <= floor(s)
          - n u <= s ---> unchanged
          - n xi = s mod k ---> n xi = floor(s) mod k /\ s = floor(s)
          - n u = s mod k:
            "Multiply" by -1 if necessary to make n > 0.

            nu - s = floor(nu) + (nu)* - (floor(s) + s* ) \in kZZ \subseteq ZZ.
            Hence, (nu)* - s* \in ZZ.
            Since 0 <= (nu)*, s* < 1, -1 < (nu)* - s* < 1, so (nu)* - s* = 0,
            i.e., [(nu)* = s*].

            Since n > 0, [0 <= nu < n], so floor(nu) = 0, 1, ..., n - 1.
            Consequently,
            [nu = floor(nu) + (nu)* = i + (nu)* = i + s*] for some i = 0, ..., n - 1,
            i.e., [nu = i + (s - floor(s))] for i = 0, ..., n - 1.

            We also have [floor(nu) + (nu)* - (floor(s) + s* \in kZZ],
            so [floor(nu) - floor(s) \in kZZ].
            When floor(nu) = i, [floor(s) = i mod k].

            Thus:

            - Substitution QE:
              [nu = s mod k] ---> [\/_{i=0}^{n-1} floor(s) = i mod k /\ nu = i + s - floor(s)].

            - MBP: ???

    3. \psi ---> \psi[xi |-> floor(x), u |-> x - floor(x)].

 *)

module Ctx = SrkAst.Ctx
let srk = Ctx.context

module IntegerFrac : sig

  (** Given a symbol [x], introduce a fresh variable [x_int] denoting its
      integer part and a fresh variable [x_frac] denoting its fractional part.
   *)

  val register_int_frac_symbols_of : Syntax.symbol -> unit

  val int_symbol_of : Syntax.symbol -> Syntax.symbol

  val frac_symbol_of : Syntax.symbol -> Syntax.symbol

end = struct

  let annotate s suffix = String.concat "_" [s; suffix]

  let make_frac s = annotate s "frac"

  let make_int s = annotate s "int"

  let register_int_frac_symbols_of s =
    (* When formula was normalized (prenexified), the quantified variable
       should have been added to the context as a named symbol
     *)
    let name = Syntax.show_symbol srk s in
    let int_name = make_int name in
    let frac_name = make_frac name in
    if (Syntax.is_registered_name srk int_name || Syntax.is_registered_name srk frac_name)
    then
      invalid_arg "Integer or fractional variables to introduce are already in context"
    else
      (Syntax.register_named_symbol srk int_name (`TyInt :> Syntax.typ);
       Syntax.register_named_symbol srk frac_name (`TyReal :> Syntax.typ))

  let int_symbol_of s =
    Syntax.show_symbol srk s
    |> make_int
    |> Syntax.get_named_symbol srk

  let frac_symbol_of s =
    Syntax.show_symbol srk s
    |> make_frac
    |> Syntax.get_named_symbol srk

end

module SplitVariables : sig

  (** phi ---> phi[x |-> x_int + x_frac] *)

  val transform : Syntax.symbol -> Ctx.formula -> Ctx.formula

end = struct

  let transform x phi =
    IntegerFrac.register_int_frac_symbols_of x;
    let xi = IntegerFrac.int_symbol_of x in
    let u = IntegerFrac.frac_symbol_of x in
    let x' = Ctx.mk_add [Ctx.mk_const xi; Ctx.mk_const u] in
    let sigma sym =
      if Syntax.Symbol.compare sym x = 0 then x'
      else Ctx.mk_const sym in
    Syntax.substitute_const srk sigma phi
    (*
    Syntax.Formula.eval srk
      (function
       | `Tru -> Ctx.mk_true
       | `Fls -> Ctx.mk_false
       | `And l ->
       | `Or l ->
       | `Not phi ->
       | `Quantify _ ->
          invalid_arg "weipsfenning_transform: formula should be quantifier-free"
       | `Atom _ ->
       | `Proposition _ ->
       | `Ite _ ->
          invalid_arg "weipsfenning_transform: ITE should have been removed"
      )
      phi
     *)

end

module LinearTerm : sig

  (*
      t ::= r
      | f(t1, ..., tn) | v
      | floor(t) | t1 * t2
      | -t
      | t1 / t2
      | t1 + t2
      | t1 mod t2 (t2 some rational constant)
      | Ite (phi, t1, t2) | Store (t1, t2, t3) | Select (t1, t2)

      --- simplify to --->

      t ::=
      r | f(t1, ..., tn) | v | floor(t)
      (t1 * t2) | r | r f(t1, ..., tn) | r v | r floor(t)
      (-t) | -r | -r f(t1, ..., tn) | -r v | -r floor (t), i.e., same
      (t1 / t2) same
      (t1 + t2) | {r | r f(t_1, ..., t_n) | r v | r floor(t)} + same
      (rest) ignored...

      So a simplified term (linear term) is of the form:

      t = \sum_i a_i s_i,

      where each s_i is in [r | r f(t1, ..., tn) | r v | r floor (t)], and
      each ti is in turn a simplified term.

   *)

  type t

  val real : QQ.t -> t

  val app : Syntax.symbol -> t list -> t

  val var : int -> Syntax.typ_arith -> t

  val add : t -> t -> t

  val mul_rational : QQ.t -> t -> t

  val mul : t -> t -> t (* only possible if one argument is a rational number *)

  val div : t -> t -> t (* only possible if second argument is a rational number *)

  val floor : t -> t

  val negate : t -> t

  val of_term: Ctx.arith_term -> t

  val to_term : t -> Ctx.arith_term

end = struct

  (** TODO: [of_term] converts back and forth between the underlying representation
      of linear terms and terms when walking the expression tree; this is very inefficient.
   *)

  module H = BatHashtbl.Make(struct
                 type t = Ctx.arith_term
                 let equal = Syntax.ArithTerm.equal
                 let hash = Syntax.ArithTerm.hash
               end)

  (** Keys are simplified terms without coefficients, and values are non-zero coefficients.
      A non-zero rational number r is represented with key "1" and value r;
      0 is itself represented by the empty table.
   *)
  type t = QQ.t H.t

  let table () = H.create 11
  let insert = H.replace

  let to_term t =
    H.fold (fun term coeff curr ->
        if QQ.equal coeff QQ.zero then
          curr
        else
          match Syntax.ArithTerm.destruct srk term with
          | `Real r when QQ.equal r QQ.one ->
             Ctx.mk_real r :: curr
          | _ -> Ctx.mk_mul [Ctx.mk_real coeff ; term]  :: curr)
      t []
    |> List.rev
    |> (function
        | [] -> Ctx.mk_real QQ.zero
        | [kt] -> kt
        | _kt :: _kts as l -> Ctx.mk_add l)

  let numeral_of t =
    let get_value term =
      match Syntax.ArithTerm.destruct srk term with
      | `App _
        | `Var _
        | `Add _
        | `Mul _
        | `Binop _
        | `Unop _
        | `Ite _
        | `Select _ -> None
      | `Real r -> Some r
    in
    H.fold (fun term _coeff _curr ->
        match get_value term with
        | None -> None
        | Some r -> Some r)
      t (Some QQ.zero)

  let real q =
    let t = table () in
    if QQ.equal q QQ.zero then t
    else
      (insert t (Ctx.mk_real QQ.one) q;
       t)

  let zero = real QQ.zero

  let app s terms =
    let t = table () in
    insert t (Ctx.mk_app s (List.map to_term terms)) QQ.one;
    t

  let var i typ =
    let t = table () in
    insert t (Ctx.mk_var i (typ : Syntax.typ_arith :> Syntax.typ_fo)) QQ.one;
    t

  let add =
    H.merge (fun _term coeff1_opt coeff2_opt ->
        (match coeff1_opt, coeff2_opt with
         | None, None -> None (* shouldn't happen *)
         | Some coeff1, Some coeff2 ->
            let coeff = QQ.add coeff1 coeff2 in
            if QQ.equal coeff QQ.zero then None
            else Some coeff
         | Some coeff, None
           | None, Some coeff -> Some coeff))

  let mul_rational r = H.map (fun _ coeff -> QQ.mul coeff r)

  let mul t1 t2 =
    match numeral_of t1, numeral_of t2 with
    | None, None -> invalid_arg "LinearTerm: non-linear multiplication"
    | Some r, None -> mul_rational r t2
    | None, Some r -> mul_rational r t1
    | Some r1, Some r2 -> real (QQ.mul r1 r2)

  let div t1 t2 =
    match numeral_of t2 with
    | None -> invalid_arg "LinearTerm: must divide by rational number"
    | Some r ->
       if QQ.equal r QQ.zero then
         invalid_arg "LinearTerm: division by zero"
       else
         mul_rational (QQ.inverse r) t1

  let floor t =
    let t' = table () in
    insert t (Ctx.mk_floor (to_term t)) QQ.one;
    t'

  let negate t =
    H.map (fun _term coeff -> QQ.negate coeff) t

  let of_term term =
    let rec go t =
      match t with
      | `Real r -> real r
      | `App (x, args) -> if args <> [] then
                            invalid_arg "LinearTerm: expecting constant symbols only"
                          else
                            app x []
      | `Var (i, typ) -> var i typ
      | `Add ts -> List.fold_left add zero ts
      | `Mul ts -> List.fold_left mul (real QQ.one) ts
      | `Binop (`Div, t1, t2) -> div t1 t2
      | `Unop (`Floor, t') -> floor t'
      | `Unop (`Neg, t') -> negate t'
      | _ -> invalid_arg "LinearTerm: cannot convert term, unsupported"
    in Syntax.ArithTerm.eval srk go term

end

module NormalTerm : sig

  (** A normalized term is conceptually of the form n x + s, where
      n \in ZZ, x is a variable (symbol), and s is a term not containing x.
   *)

  (**
     a. Make terms into PA and LRA terms, which are of the form
        [n * xi + s] or [n * u + s], where [s] is free of [xi] or [u].

        - 0, 1, variable ---> unchanged
        - c * x, x * c ---> simplify constants
        - T + T ---> recurse, group 'like' parts, simplify constants
        - floor(T) --->
          - Recurse on T to get [T = n * xi + s] or [T = nu + s].
          - Check sort of xi/u
          - If xi, distribute floor to get [nu + floor(s)].
          - If u, [s <= nu + s < n + s] or [n + s < nu + s <= s], so
            [floor(nu + s) = floor(s), 1 + floor(s), ..., n + floor(s)], or
            [floor(nu + s) = n + floor(s), (n + 1) + floor(s), ..., floor(s)].

           For substitution QE: replace [floor(nu + s)] in the formula here
           with [k + floor(s)] and restart (a).

           For implementation: generalize "term-purification" algorithm to
           return a set of terms, and these possibilities are returned.
   *)


  type t

  val zero : Syntax.symbol -> t (* 0 x + 0 *)

  val coeff : t -> QQ.t (* coefficient of x *)

  val symbol : t -> Syntax.symbol

  val rest_of : t -> Ctx.arith_term

  val term_of : t -> Ctx.arith_term

  val add_sym : QQ.t -> t -> t

  val add_rest : Ctx.arith_term -> t -> t
  (* unchecked, make sure it doesn't include the symbol itself *)

  val add : t -> t -> t

  val mul_rational : QQ.t -> t -> t

  val mul : t -> t -> t
  (* defined only when both have the same distinguished symbol and
     at least one of them has zero coefficient for its distinguished symbol *)

  val div : t -> t -> t

  val modulo : t -> t -> t

  val negate : t -> t

  val floor : [`TyIntQe | `TyFracQe ] -> t -> t list

end = struct

  type t = { sym : Syntax.symbol
           ; coeff : QQ.t
           ; rest : Ctx.arith_term option }

  let zero s = { sym = s ; coeff = QQ.zero ; rest = None }

  let coeff t = t.coeff

  let symbol t = t.sym

  let rational_of t =
    let rec go t =
      match t with
      | `Real r -> r
      | `Add rationals -> List.fold_left QQ.add QQ.zero rationals
      | `Mul rationals -> List.fold_left QQ.mul QQ.one rationals
      | `Binop (`Div, num, denom) -> QQ.div num denom
      | `Binop (`Mod, dividend, divisor) -> QQ.modulo dividend divisor
      | `Unop (`Floor, r) -> QQ.of_zz (QQ.floor r)
      | `Unop (`Neg, r) -> QQ.negate r
      | _ -> invalid_arg "NormalTerm: non-linear multiplication?"
    in Syntax.ArithTerm.eval srk go t

  let coerce_rational = function
    | None -> QQ.zero
    | Some term -> rational_of term

  let rest_of t =
    match t.rest with
    | None -> Ctx.mk_real QQ.zero
    | Some rest -> rest

  let term_of t =
    let nx = Ctx.mk_mul [Ctx.mk_real t.coeff; Ctx.mk_const t.sym] in
    match t.rest with
    | None -> nx
    | Some rest -> Ctx.mk_add [nx ; rest]

  let add_sym r t =
    { t with coeff = QQ.add r t.coeff }

  let add_rest r t =
    match t.rest with
    | None -> { t with rest = Some r }
    | Some rest -> { t with rest = Some (Ctx.mk_add [rest ; r]) }

  let add t1 t2 =
    if Syntax.Symbol.compare t1.sym t2.sym = 0 then
      { sym = t1.sym
      ; coeff = QQ.add t1.coeff t2.coeff
      ; rest =
          match t1.rest, t2.rest with
          | None, _ -> t2.rest
          | _, None -> t1.rest
          | Some rest1, Some rest2 -> Some (Ctx.mk_add [rest1; rest2])
      }
    else invalid_arg "NormalTerm: cannot add normal terms with different distinguished symbols"

  let mul_rational r t =
    { sym = t.sym
    ; coeff = QQ.mul r t.coeff
    ; rest = match t.rest with
             | None -> None
             | Some rest -> Some (Ctx.mk_mul [Ctx.mk_real r; rest])
    }

  let mul t1 t2 =
    let zero_rat r = QQ.equal r QQ.zero in
    if t1.sym <> t2.sym then
      invalid_arg "NormalTerm: distinguished symbols must be the same for multiplication"
    else if not (zero_rat t1.coeff) && not (zero_rat t2.coeff) then
      invalid_arg "NormalTerm: non-linear multiplication"
    else
      if zero_rat t1.coeff then
        mul_rational (coerce_rational t1.rest) t2
      else
        mul_rational (coerce_rational t2.rest) t1

  let negate t =
    let negated = match t.rest with
      | None -> None
      | Some rest -> Some (Ctx.mk_mul [Ctx.mk_real (QQ.of_int (-1)); rest ]) in
    { t with coeff = QQ.negate t.coeff ; rest = negated }

  let div t1 t2 =
    if t1.sym <> t2.sym then
      invalid_arg "NormalTerm: distinguished symbols must be the same for division"
    else if not (QQ.equal t2.coeff QQ.zero) then
      invalid_arg "NormalTerm: non-linear division"
    else
      let n = coerce_rational t2.rest in
      if QQ.equal n QQ.zero then
        invalid_arg "NormalTerm: division by zero"
      else
        mul_rational (QQ.inverse n) t1

  let modulo t1 t2 =
    if t1.sym <> t2.sym then
      invalid_arg "NormalTerm: distinguished symbols must be the same for division"
    else if not (QQ.equal t2.coeff QQ.zero) then
      invalid_arg "NormalTerm: non-linear division"
    else
      try
        let n = coerce_rational t2.rest in
        if QQ.equal n QQ.zero then
          invalid_arg "NormalTerm: modulo by zero"
        else
          { sym = t1.sym
          ; coeff = QQ.modulo t1.coeff n
          ; rest = Some (Ctx.mk_real (QQ.modulo (coerce_rational t1.rest) n)) }
      with Invalid_argument _ ->
        invalid_arg "NormalTerm: non-constant modulo non-constant not supported yet"

  let floor typ t =
    let possibilities =
      let n = match QQ.to_int t.coeff with
        | None -> failwith "NormalTerm: coefficient of distinguished symbol not integer"
        | Some n -> n in
      let rec range n =
        if n = 0 then [0]
        else if n > 0 then n :: range (n - 1)
        else n :: range (n + 1) in
      List.map QQ.of_int (range n)
    in
    let sum term n =
      { sym = t.sym
      ; coeff = QQ.zero
      ; rest =
          match term with
          | None -> Some (Ctx.mk_real n)
          | Some term -> Some (Ctx.mk_add [Ctx.mk_real n; term]) }
    in
    match typ, t.rest with
    | `TyIntQe, None -> [t]
    | `TyIntQe, Some term ->
       [{ t with rest = Some (Ctx.mk_floor term) }]
    | `TyFracQe, None ->
       List.map (sum None) possibilities
    | `TyFracQe, Some rest ->
       List.map (sum (Some rest)) possibilities

end

module NormalizeTerm : sig

  val normalize_term : [`TyIntQe | `TyFracQe]
                       -> Syntax.symbol -> Syntax.symbol Syntax.Env.t
                       -> Ctx.arith_term -> NormalTerm.t list

  (* Lift binary operation on normal terms to binary operation on sets
     of normal terms; (A, B) |-> { a op b : a in A, b in B }.
   *)
  val binary_op : (NormalTerm.t -> NormalTerm.t -> NormalTerm.t)
                  -> NormalTerm.t list -> NormalTerm.t list
                  -> NormalTerm.t list

end = struct

  let rec binary_product op l1 l2 =
    match l1 with
    | [] -> []
    | x :: xs ->
       let l2' = binary_product op xs l2 in
       let l1' = List.fold_left (fun accum t -> (op x t) :: accum) [] l2 in
       List.concat [List.rev l1'; l2']

  (** Given a list of sets of normal terms, i.e.,
      S_i = { t_{i,j} }_j
      form the set S = { t_{1, j1} op t_{2, j2} op ... }_{j1, j2, ...},
      i.e., containing all sums where the i-th summand is picked from S_i.
   *)
  let cartesian_product op unit ll =
    List.fold_left (binary_product op) [unit] ll

  let binary_op = binary_product

  let all_sums s = cartesian_product NormalTerm.add (NormalTerm.zero s)

  let all_products s =
    cartesian_product NormalTerm.mul
      (NormalTerm.zero s |> NormalTerm.add_rest (Ctx.mk_real QQ.one))

  let normalize_term (sort: [`TyIntQe | `TyFracQe]) x env =
    let rec go term =
      match term with
      | `Real r -> [NormalTerm.zero x |> NormalTerm.add_rest (Ctx.mk_real r)]
      | `App (sym, args) ->
         if args = [] then
           if Syntax.Symbol.compare sym x = 0 then
             [ NormalTerm.zero x |> NormalTerm.add_sym QQ.one ]
           else
             [ NormalTerm.zero x |> NormalTerm.add_rest (Ctx.mk_app sym args) ]
         else
           invalid_arg "normalize_term: unexpected function symbol"
      | `Var (i, (typ : Syntax.typ_arith)) ->
         if Syntax.Symbol.compare x (Syntax.Env.find env i) = 0 then
           [ NormalTerm.zero x |> NormalTerm.add_sym QQ.one ]
         else
           [ NormalTerm.zero x |> NormalTerm.add_rest (Ctx.mk_var i (typ :> Syntax.typ_fo)) ]
      | `Add l -> all_sums x l (* recursive assumption for eliminator *)
      | `Mul l -> all_products x l
      | `Binop (`Div, num, denum) ->
         binary_product NormalTerm.div num denum
      | `Binop (`Mod, dividend, divisor) ->
         binary_product NormalTerm.modulo dividend divisor
      | `Unop (`Floor, terms) ->
         List.fold_left
           (fun curr t -> List.append curr (NormalTerm.floor sort t))
           []
           terms
      | `Unop (`Neg, terms) ->
         terms
         |> List.map NormalTerm.negate
      | `Ite _
      | `Select _ -> invalid_arg "NormalizeTerm: unsupported" in
    Syntax.ArithTerm.eval srk go

end

module AtomicRewriter : sig

  val rewrite_eq : [`TyIntQe | `TyFracQe]
                   -> Syntax.symbol -> Syntax.symbol Syntax.Env.t
                   -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

end = struct

  let normalize sort x env lhs rhs =
    let lhs_terms = NormalizeTerm.normalize_term sort x env lhs in
    let rhs_terms = NormalizeTerm.normalize_term sort x env rhs in
    let terms = NormalizeTerm.binary_op
                  (fun t1 t2 -> NormalTerm.add t1 (NormalTerm.negate t2))
                  lhs_terms rhs_terms in
    let pairs = List.map (fun t -> (NormalTerm.coeff t, NormalTerm.rest_of t)) terms in



  let rewrite_eq sort x env lhs rhs =


end

module Eliminate : sig

  val eliminate : [`TyIntQe | `TyFracQe] -> Syntax.symbol
                  -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end = struct



end

module Normalize : sig

  val transform : int_sym:Syntax.symbol -> frac_sym:Syntax.symbol
                  -> Ctx.formula -> Ctx.formula

end = struct

  (*
  type coeff_var = QQ.t * [`None | `Rational | `Var of int * Syntax.typ_arith]

  let multiply_coeff_var (coeff1, tag1) (coeff2, tag2) : coeff_var =
    let f = QQ.mul in
    match tag1, tag2 with
    | `None, _ -> (coeff2, tag2)
    | _, `None -> (coeff1, tag1)
    | `Rational, `Rational ->
       (f coeff1 coeff2, `Rational)
    | `Rational, `Var (i, typ)
    | `Var (i, typ), `Rational ->
       (f coeff1 coeff2, `Var (i, typ))
    | `Var (i, typi), `Var (j, typj) when i = j && typi = typj ->
       (f coeff1 coeff2, `Var (i, typi))
    | `Var (_i, _typi), `Var (_j, _typj) ->
       invalid_arg "op_coeff_var: cannot multiply, non-linear or wrong types"

  (** Given a monomial in one variable, compute its coefficient and variable *)
  let coeff_var_of_product term =
    let destruct = Syntax.ArithTerm.destruct srk in
    let rec go t =
      match destruct t with
      | `Real k -> (k, `Rational)
      | `Var (i, typ) ->
         (QQ.one, `Var (i, typ))
      | `Mul l ->
         List.map go l
         |> List.fold_left multiply_coeff_var (QQ.one, `None)
      | `Unop (`Neg, t) ->
         let (k, tag) = go t in
         (QQ.negate k, tag)
      | _ -> invalid_arg "coeff_var_of_product: unexpected term"
    in
    go term

  (** Given a list of linear terms of the form a_i x_i, compute the sum as a vector *)
  let linear_sum_to_vector terms =
    List.fold_left
      (fun vec t ->
        let (k, tag) = coeff_var_of_product t in
        match tag with
        | `Rational -> Linear.QQVector.add_term k 0 vec
        | `Var (_, typ) when typ = `TyInt ->
           invalid_arg "linear_sum_to_vector: variable should be real/rational"
        | `Var (i, typ) when typ = `TyReal ->
           if i <= 0 then
             invalid_arg "linear_sum_to_vector: de Bruijn index <= 0!"
           else Linear.QQVector.add_term k i vec
        | `Var _ -> invalid_arg "linear_sum_to_vector: shouldn't happen"
        | `None -> invalid_arg "linear_sum_to_vector: coefficient should exist"
      )
      Linear.QQVector.zero terms

  let vector_entry_to_term scalar dim =
    if dim > 0 then
      Ctx.mk_mul [Ctx.mk_real scalar; Ctx.mk_var dim `TyReal]
    else if dim = 0 then
      Ctx.mk_real scalar
    else
      invalid_arg "vector_to_terms: dimension unexpected"

  let vector_to_terms v =
    Linear.QQVector.enum v
    |> BatEnum.fold
         (fun l (scalar, dim) -> vector_entry_to_term scalar dim :: l) []
    |> List.rev
   *)

  (*
  let construct_normal_terms _env _x t =
    let open Syntax in
    let rec go (t : ('b, 'a) open_arith_term) =
      match t with
      | `Real c -> [Ctx.mk_real c]
      | `App (f, args) -> [Ctx.mk_app f args] (* TODO? *)
      | `Var (i, typ) ->
         (*
         if Symbol.compare x (Env.find env i) = 0
         (* Turn de Bruijn variable into constant symbol since we are
            eliminating quantifier for x anyway *)
         then [Ctx.mk_const x]
         else [Ctx.mk_var i typ]
          *)
         [Ctx.mk_var i (typ : typ_arith :> typ_fo)]
      | `Add ts ->
         List.map go ts |> cartesian_product
         |> List.map (fun l -> l |> linear_sum_to_vector |> vector_to_terms |> Ctx.mk_add)
      | `Mul ts ->
         List.map go ts |> cartesian_product
         |> List.map (fun l ->
                l
                |> List.fold_left (* Muitiply monomials together provided the result is linear *)
                     (fun coeff_var t ->
                       coeff_var_of_product t |> multiply_coeff_var coeff_var)
                     (QQ.one, `None)
                |> fun (coeff, tag) ->
                   match tag with
                   | `None -> invalid_arg "construct_normal_terms: shouldn't happen"
                   | `Rational ->
                      Ctx.mk_real coeff
                   | `Var (i, typ) ->
                      Ctx.mk_mul [Ctx.mk_real coeff; Ctx.mk_var i (typ : typ_arith :> typ_fo)])
      | `Binop (`Div, `Real k1, `Real k2) when not (QQ.equal k2 QQ.zero) ->
         [Ctx.mk_real (QQ.div k1 k2)]
      | `Unop (`Floor, _t) ->
         (*
         go t
         |> List.map
              (fun term ->
                term
                |> linear_sum_to_vector
                |> Linear.QQVector.enum
                |> BatEnum.fold (fun (curr_x, rest) (scalar, dim) ->
                       if Symbol.compare x (Env.find env i) = 0 then
                         (QQ.add curr_x scalar, rest)
                       else
                         (, vector_entry_to_term scalar dim)
                     )
                     (QQ.zero, vector_entry_to_term scalar dim)
              )
          *)
         invalid_arg "construct_normal_terms: not handled yet"
      | `Unop (`Neg, t) ->

      | `Binop _
      | `Ite _
      | `Select _ -> invalid_arg "construct_normal_terms: unsupported"
    in
    ArithTerm.eval srk go t
   *)

  (*
  let rec linearizer x phi =
    Syntax.Formula.eval srk
      (function
       | `Tru -> Syntax.mk_true
       | `Fls -> Syntax.mk_false
       | `And phis -> Syntax.mk_and srk (linearizer x phis)
       | `Or phis -> Syntax.mk_or srk (linearizer x phis)
       | `Not phi' -> Syntax.mk_not srk (linearizer x phi')
       | `Quantify (quantifier, y, typ, phi') ->
          (match quantifier with
           | `Exists ->
              Syntax.mk_exists srk ~name:y typ (linearizer x phi')
           | `Forall ->
              Syntax.mk_forall srk ~name:y typ (linearizer x phi')
          )
       | `Atom atom ->
          linearize_atom atom
       | `Proposition (`Var i) ->
       | `Proposition (`App (f, args)) ->
       | `Ite (cond, ifbody, elsebody) ->
          Syntax.mk_ite srk (linearizer x  ? ?
       | Node (Eq, _, _) ->
       | Node (Leq, _, _) ->
       | Node (Lt, _, _) ->
       | Node (App, _, _) ->
       | Node (Var (i, typ), _, _) ->
       | Node (Add, _, _) ->
       | Node (Mul, _, _) ->
       | Node (Neg, _, _) ->
       | Node (Floor, _, _) ->
       | Node (Real, _, _) ->
       | Node (Mod, _, _) ->
       | Node (Div _, _) ->
       | Node (ArrEq, _, _) ->
       | Node (Ite, _, _) ->
       | Node (Store, _, _) ->
       | Node (Select, _, _) ->
      ) phi
   *)

  let transform ~int_sym:_xi ~frac_sym:_u phi =
    (* [Formula.eval], [Formula.destruct], [Syntax.rewrite] *)
    Syntax.rewrite srk phi

end

(*
let annotate (typ : Syntax.typ) (x : Syntax.symbol) =
  let name = Option.get (Syntax.symbol_name srk x) in
  let make_name s suffix =
    let s' = String.concat "_" [s; suffix] in
    if Syntax.is_registered_name srk s' then
      invalid_arg (Format.sprintf "annotate: %s already exists" s)
    else
      s'
  in
  match typ with
  | `TyInt ->
     make_name name "int"
  | `TyReal ->
     make_name name "frac"
  | _ ->
     invalid_arg "annotate: can only introduce int or real names"

 *)

(*
let rec weipsfenning_transform
          (phi : (SrkAst.formula, 'a) Syntax.open_formula)
        : SrkAst.formula =
  let open Syntax in
  match phi with
  | `Tru -> Ctx.mk_true
  | `Fls -> Ctx.mk_false
  | `And l -> Ctx.mk_and (List.map (Formula.eval srk weipsfenning_transform) l)
  | `Or l -> Ctx.mk_or (List.map (Formula.eval srk weipsfenning_transform) l)
  | `Not phi -> Ctx.mk_not (Formula.eval srk weipsfenning_transform phi)
  | `Quantify _ ->
     invalid_arg "weipsfenning_transform: formula should be quantifier-free"
  | `Atom atom ->
     (match atom with
      | `Arith (`Eq, lhs, rhs) ->
         Ctx.mk_eq lhs rhs
      | `Arith (`Leq, lhs, rhs) ->
         Ctx.mk_leq lhs rhs
      | `Arith (`Lt, lhs, rhs) ->
         Ctx.mk_lt lhs rhs
      | `ArrEq (_, _) ->
         invalid_arg "weipsfenning_transform: array theory not supported yet")
  | `Proposition _ ->
     invalid_arg "weipsfenning_transform: proposition not supported"
  | `Ite _ ->
     invalid_arg "weipsfenning_transform: ITE should have been removed"
 *)

let weipsfenning_substitution_qe
      (x : Syntax.symbol)
      (qf_formula : Ctx.t Syntax.formula) : Ctx.t Syntax.formula =
  (* Syntax.Formula.eval srk weipsfenning_transform qf_formula *)
  SplitVariables.transform x qf_formula
  |>

let quantifier_elimination ~how:(how : [`Substitution | `Mbp])
      (quantifiers : Quantifier.quantifier_prefix)
      qf_formula =
  (* stolen from Quantifier.ml *)
  let open Quantifier in
  let open Syntax in
  let exists x phi =
    match how with
    | `Substitution
    | `Mbp ->
       weipsfenning_substitution_qe x phi
  in
  List.fold_right
    (fun (qt, x) qf ->
      match qt with
      | `Exists ->
         exists x (snd (normalize srk qf))
      | `Forall ->
         mk_not srk (exists x (snd (normalize srk
                                      (mk_not srk qf)))))
    quantifiers (* fold over quantifiers *)
    qf_formula
