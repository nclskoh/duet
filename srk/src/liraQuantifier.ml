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

(* module Ctx = SrkAst.Ctx *)

module Ctx = Syntax.MakeContext ()
let lira_ctx = Ctx.context

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
    let name = Syntax.show_symbol lira_ctx s in
    let int_name = make_int name in
    let frac_name = make_frac name in
    if (Syntax.is_registered_name lira_ctx int_name || Syntax.is_registered_name lira_ctx frac_name)
    then
      invalid_arg "Integer or fractional variables to introduce are already in context"
    else
      (Syntax.register_named_symbol lira_ctx int_name (`TyInt :> Syntax.typ);
       Syntax.register_named_symbol lira_ctx frac_name (`TyReal :> Syntax.typ))

  let int_symbol_of s =
    Syntax.show_symbol lira_ctx s
    |> make_int
    |> Syntax.get_named_symbol lira_ctx

  let frac_symbol_of s =
    Syntax.show_symbol lira_ctx s
    |> make_frac
    |> Syntax.get_named_symbol lira_ctx

end

module SplitVariables : sig

  (** phi ---> phi[x |-> x_int + x_frac] *)

  val transform : Syntax.symbol -> Ctx.formula -> Syntax.symbol * Syntax.symbol * Ctx.formula

end = struct

  let transform x phi =
    IntegerFrac.register_int_frac_symbols_of x;
    let xi = IntegerFrac.int_symbol_of x in
    let u = IntegerFrac.frac_symbol_of x in
    let x' = Ctx.mk_add [Ctx.mk_const xi; Ctx.mk_const u] in
    let sigma sym =
      if Syntax.Symbol.compare sym x = 0 then x'
      else Ctx.mk_const sym in
    (xi, u, Syntax.substitute_const lira_ctx sigma phi)
    (*
    Syntax.Formula.eval lira_ctx
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

  val simplify: Ctx.arith_term -> Ctx.arith_term

  val pp : Format.formatter -> t -> unit

end = struct

  (** TODO: The current implementation only represents the top-level linear sum;
      linear subterms are not represented as LinearTerm.t.
      Hence, [of_term] converts back and forth between LinearTerm.t and terms
      when walking the expression tree; this is very inefficient.
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

  let pp fmt t =
    if H.is_empty t then
      Format.fprintf fmt "(0, 0)"
    else
      begin
        H.iter (fun term coeff ->
            Format.fprintf Format.str_formatter "(term: %a, coeff: %a), "
              (Syntax.ArithTerm.pp lira_ctx)
              term QQ.pp coeff) t;
        let s = Format.flush_str_formatter () in
        Format.fprintf fmt "%s" s
      end

  let to_term t =
    H.fold (fun term coeff curr ->
        let this_term =
          if QQ.equal coeff QQ.zero then
            invalid_arg "LinearTerm: to_term: coefficient in table should always be non-zero"
          else
            match Syntax.ArithTerm.destruct lira_ctx term with
            | `Real r when QQ.equal r QQ.one ->
               Some (Ctx.mk_real coeff)
            | _ when QQ.equal coeff QQ.one ->
               Some term
            | _ when QQ.equal coeff (QQ.negate QQ.one) ->
               Some (Ctx.mk_neg term)
            | _ -> Some (Ctx.mk_mul [Ctx.mk_real coeff ; term])
        in
        match this_term with
        | None -> curr
        | Some this_term -> this_term :: curr
      )
      t []
    |> List.rev
    |> (function
        | [] -> Ctx.mk_real QQ.zero
        | [kt] -> kt
        | _kt :: _kts as l -> Ctx.mk_add l)

  let numeral_of t =
    let get_value term =
      match Syntax.ArithTerm.destruct lira_ctx term with
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
    H.fold (fun term coeff curr ->
        match get_value term, curr with
        | _, None -> None (* non-constant term already present *)
        | None, Some _ -> None
        | Some _, Some _ -> Some coeff)
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

  let add t1 t2 =
    let t =
      H.merge (fun _term coeff1_opt coeff2_opt ->
          match coeff1_opt, coeff2_opt with
          | None, None -> None (* shouldn't happen *)
          | Some coeff1, Some coeff2 ->
             let coeff = QQ.add coeff1 coeff2 in
             if QQ.equal coeff QQ.zero then None
             else Some coeff
          | Some coeff, None
            | None, Some coeff -> Some coeff) t1 t2 in
    Log.logf ~level:`trace "@[LinearTerm: adding %a and %a gives %a@]@;" pp t1 pp t2 pp t;
    t

  let mul_rational r t =
    H.fold (fun term coeff curr ->
        let c = QQ.mul r coeff in
        if QQ.equal c QQ.zero then curr
        else
          (insert curr term c; curr)
      )
      t
      (table ())

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
    (* TODO: This is quite inefficient *)
    match numeral_of t with
    | None ->
       let t' = table () in
       insert t' (Ctx.mk_floor (to_term t)) QQ.one;
       t'
    | Some r ->
       real (QQ.of_zz (QQ.floor r))

  let negate t =
    H.map (fun _term coeff -> QQ.negate coeff) t

  let of_term term =
    let go t =
      match t with
      | `Real r -> real r
      | `App (x, args) ->
         if args <> [] then
           invalid_arg
             (Format.sprintf "LinearTerm: expecting constant symbols only, see %s"
                (Syntax.show_symbol lira_ctx x))
         else
           app x []
      | `Var (i, typ) -> var i typ
      (* TODO: Check that we don't have variables after normalization. *)
      | `Add ts -> List.fold_left add zero ts
      | `Mul ts -> List.fold_left mul (real QQ.one) ts
      | `Binop (`Div, t1, t2) -> div t1 t2
      | `Unop (`Floor, t') -> floor t'
      | `Unop (`Neg, t') -> negate t'
      | _ -> invalid_arg "LinearTerm: cannot convert term, unsupported"
    in Syntax.ArithTerm.eval lira_ctx go term

  let simplify term =
    term
    |> of_term
    |> (fun converted -> Log.logf ~level:`trace "@[LinearTerm: of_term(%a) = %a@]@;"
                           (Syntax.ArithTerm.pp lira_ctx) term
                           pp converted
                       ; converted)
    |> to_term
    |> (fun res -> Log.logf ~level:`trace "@[LinearTerm: to_term(...) = %a@]@;"
                     (Syntax.ArithTerm.pp lira_ctx) res
                 ; res)

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

  val pp : Format.formatter -> t -> unit

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

  let pp fmt t =
    Format.fprintf fmt "[%a %a + %a]"
      QQ.pp t.coeff
      (Syntax.pp_symbol lira_ctx) t.sym
      (Format.pp_print_option (Syntax.ArithTerm.pp lira_ctx)) t.rest

  let zero s = { sym = s ; coeff = QQ.zero ; rest = None }

  let coeff t = t.coeff

  let symbol t = t.sym

  let rational_of t =
    let go t =
      match t with
      | `Real r -> r
      | `Add rationals -> List.fold_left QQ.add QQ.zero rationals
      | `Mul rationals -> List.fold_left QQ.mul QQ.one rationals
      | `Binop (`Div, num, denom) -> QQ.div num denom
      | `Binop (`Mod, dividend, divisor) -> QQ.modulo dividend divisor
      | `Unop (`Floor, r) -> QQ.of_zz (QQ.floor r)
      | `Unop (`Neg, r) -> QQ.negate r
      | _ -> invalid_arg "NormalTerm: non-linear multiplication?"
    in Syntax.ArithTerm.eval lira_ctx go t

  let coerce_rational = function
    | None -> QQ.zero
    | Some term -> rational_of term

  let rest_of t =
    match t.rest with
    | None -> Ctx.mk_real QQ.zero
    | Some rest -> (* LinearTerm.simplify rest *) rest

  let term_of t =
    (* TODO: verify that it's fine to output a symbol, which may be undefined
       in the quantifier-free context before we eliminate.
     *)
    let nx = Ctx.mk_mul [Ctx.mk_real t.coeff; Ctx.mk_const t.sym] in
    match t.rest with
    | None -> nx
    | Some rest -> LinearTerm.simplify (Ctx.mk_add [nx ; rest])

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
    match typ, t.rest with
    | `TyIntQe, None -> [t] (* floor(n xi + 0) = n xi *)
    | `TyIntQe, Some term ->
       [{ t with rest = Some (Ctx.mk_floor term) }] (* floor(n xi + s) = n xi + floor(s) *)
    | `TyFracQe, _ ->
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
       begin
         Log.logf ~level:`trace "@[NormalTerm: floor: possibilities are: %a@]@;"
           (Format.pp_print_list ~pp_sep:Format.pp_print_space QQ.pp)
           possibilities;
         let result =
           match t.rest with
           | None ->
              List.map (sum None) possibilities
           | Some rest ->
              List.map (sum (Some (Ctx.mk_floor rest))) possibilities
         in
         Log.logf ~level:`debug "@[NormalTerm for %a: fractional floor(%a) = %a@]@;"
           (Syntax.pp_symbol lira_ctx) t.sym
           pp t
           (Format.pp_print_list ~pp_sep:Format.pp_print_space pp)
           result;
         result
       end

end

module NormalizeTerm : sig

  (** Given a term, return the set of possible normal terms corresponding to it.
   *)
  val normalize_term : [`TyIntQe | `TyFracQe]
                       -> Syntax.symbol
                       -> Ctx.arith_term -> NormalTerm.t list

  (* Lift binary operation on normal terms to binary operation on sets
     of normal terms; (A, B) |-> { a op b : a in A, b in B }.
   *)
  val binary_op : (NormalTerm.t -> NormalTerm.t -> NormalTerm.t)
                  -> NormalTerm.t list -> NormalTerm.t list
                  -> NormalTerm.t list

end = struct

  let pp = Format.pp_print_list ~pp_sep:Format.pp_print_space
             NormalTerm.pp

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

  let binary_op op l1 l2 =
    let l = binary_product op l1 l2 in
    Log.logf ~level:`trace "@[NormalizeTerm: binary_op: given %a and %a, result is %a@]@;"
      pp l1 pp l2 pp l;
    l

  let all_sums s = cartesian_product NormalTerm.add (NormalTerm.zero s)

  let all_products s =
    cartesian_product NormalTerm.mul
      (NormalTerm.zero s |> NormalTerm.add_rest (Ctx.mk_real QQ.one))

  let normalize_term (sort: [`TyIntQe | `TyFracQe]) x term =
    let go term =
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
      | `Var (_i, (_typ : Syntax.typ_arith)) ->
         (*
         if Syntax.Symbol.compare x (Syntax.Env.find env i) = 0 then
           [ NormalTerm.zero x |> NormalTerm.add_sym QQ.one ]
         else
           [ NormalTerm.zero x |> NormalTerm.add_rest (Ctx.mk_var i (typ :> Syntax.typ_fo)) ]
          *)
         invalid_arg "normalize_term: [Quantifier.normalize] should have turned Var into a constant symbol"
      | `Add l -> all_sums x l (* recursive assumption for eliminator *)
      | `Mul l -> all_products x l
      | `Binop (`Div, num, denum) ->
         binary_product NormalTerm.div num denum
      | `Binop (`Mod, dividend, divisor) ->
         binary_product NormalTerm.modulo dividend divisor
      | `Unop (`Floor, terms) ->
         let res =
           List.fold_left
             (fun curr t -> List.append curr (NormalTerm.floor sort t))
             []
             terms
         in
         Log.logf ~level:`trace "@[NormalizeTerm: floor({%a}) = {%a}@]@;"
           pp terms pp res;
         res

      | `Unop (`Neg, terms) ->
         terms
         |> List.map NormalTerm.negate
      | `Ite _
        | `Select _ -> invalid_arg "NormalizeTerm: unsupported" in
    let res = Syntax.ArithTerm.eval lira_ctx go term in
    Log.logf ~level:`debug "@[@[NormalizeTerm: normalizing @[%a@] gives@]@; @[%a@]@]@;"
      (Syntax.ArithTerm.pp lira_ctx) term pp res;
    res

end

module AtomicRewriter : sig

  val simplify_atomic : [`Eq | `Leq | `Lt]
                        -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

  val rewrite_eq : [`TyIntQe | `TyFracQe]
                   -> Syntax.symbol
                   -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

  val rewrite_leq : [`TyIntQe | `TyFracQe]
                   -> Syntax.symbol
                   -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

  val rewrite_lt : [`TyIntQe | `TyFracQe]
                   -> Syntax.symbol
                   -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

  val rewrite_modulo : [`TyIntQe | `TyFracQe]
                       -> Syntax.symbol
                       -> Ctx.arith_term -> Ctx.arith_term
                       -> Syntax.symbol (* TODO: remove the need for this modulo symbol *)
                       -> Ctx.arith_term
                       -> Ctx.formula

end = struct

  (*
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
   *)

  (*
  let normalize sort x lhs rhs =
    let lhs_terms = NormalizeTerm.normalize_term sort x lhs in
    let rhs_terms = NormalizeTerm.normalize_term sort x rhs in
    let terms = NormalizeTerm.binary_op
                  (fun t1 t2 -> NormalTerm.add t1 (NormalTerm.negate t2))
                  lhs_terms rhs_terms in
    let pairs = List.map (fun t -> (NormalTerm.coeff t, NormalTerm.rest_of t)) terms in

    let rewrite_eq sort x env lhs rhs =
   *)

  let simplify_atomic atom lhs rhs =
    let atomize atom =
      match atom with
      | `Eq -> Ctx.mk_eq
      | `Leq -> Ctx.mk_leq
      | `Lt -> Ctx.mk_lt
    in
    atomize atom (LinearTerm.simplify lhs) (LinearTerm.simplify rhs)

  let pp_lhs_rhs_list l =
    Format.pp_print_list ~pp_sep:Format.pp_print_space
      (fun fmt (coeff, rhs) -> Format.fprintf fmt "(LHS coeff: %a, RHS term: %a)"
                                 QQ.pp coeff (Syntax.ArithTerm.pp lira_ctx) rhs) l

  let log_formulas prefix l =
    Log.logf ~level:`trace
      "@[AtomicRewriter: %s: %a@]@;"
      prefix
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
         (Syntax.Formula.pp lira_ctx)) l

  let log_rewriting (relation : [`Eq | `Leq | `Lt]) lhs rhs result =
    let rel_symbol = match relation with
      | `Eq -> "="
      | `Leq -> "<="
      | `Lt -> "<"
    in
    Log.logf ~level:`debug "@[@[AtomicRewriter: rewritten @[(%a %s %a)@] into@]@; %a@]@;"
      (Syntax.ArithTerm.pp lira_ctx) lhs
      rel_symbol
      (Syntax.ArithTerm.pp lira_ctx) rhs
      (Syntax.Formula.pp lira_ctx) result

  let split sort x lhs rhs =
    let lhs_terms = NormalizeTerm.normalize_term sort x lhs in
    let rhs_terms = NormalizeTerm.normalize_term sort x rhs in
    let terms = NormalizeTerm.binary_op
                  (fun t1 t2 -> NormalTerm.add t1 (NormalTerm.negate t2))
                  lhs_terms rhs_terms in
    let coeffs_rhs =
      List.map
        (fun t ->
          let rhs = NormalTerm.rest_of t
                    |> (fun rest -> Log.logf ~level:`trace "AtomicRewriter: Rest: %a"
                                      (Syntax.ArithTerm.pp lira_ctx) rest; rest)
                    |> Ctx.mk_neg
                    |> LinearTerm.simplify
                    |> (fun simplified -> Log.logf
                                            ~level:`trace "AtomicRewriter: simplified negated rest: %a"
                                            (Syntax.ArithTerm.pp lira_ctx) simplified; simplified)
          in
          (NormalTerm.coeff t, rhs))
        terms
    in
    Log.logf ~level:`trace "@[AtomicRewriter: splitting (%a, %a) gives %a@]@;"
      (Syntax.ArithTerm.pp lira_ctx) lhs
      (Syntax.ArithTerm.pp lira_ctx) rhs
      pp_lhs_rhs_list coeffs_rhs;
    coeffs_rhs

  let mk_monomial coeff x = Ctx.mk_mul [Ctx.mk_real coeff; Ctx.mk_const x]

  let mk_atomic (atom: [`Eq | `Leq | `Lt]) coeff x rhs =
    match atom with
    | `Eq -> Ctx.mk_eq (mk_monomial coeff x) rhs
    | `Leq -> Ctx.mk_leq (mk_monomial coeff x) rhs
    | `Lt -> Ctx.mk_lt (mk_monomial coeff x) rhs

  let rewrite_eq sort x lhs rhs =
    let coeffs_rhs = split sort x lhs rhs in
    match sort with
    | `TyIntQe ->
       let formulas = List.map (fun (coeff, rhs) ->
                          let floored = Ctx.mk_floor rhs in
                          LinearTerm.simplify floored
                          |> mk_atomic `Eq coeff x
                          |> (fun phi -> Ctx.mk_and [phi; Ctx.mk_eq rhs floored])
                        )
                        coeffs_rhs
       in Ctx.mk_or formulas
    | `TyFracQe ->
       List.map (fun (coeff, rhs) -> mk_atomic `Eq coeff x rhs) coeffs_rhs
       |> Ctx.mk_or

  let rewrite_leq sort x lhs rhs =
    let coeffs_rhs = split sort x lhs rhs in
    Log.logf ~level:`trace "@[AtomicRewriter: rewrite_leq: coeffs_rhs: %a@]@;"
      pp_lhs_rhs_list coeffs_rhs;

    match sort with
    | `TyIntQe ->
       let formulas = List.map (fun (coeff, rhs) ->
                          let floored = Ctx.mk_floor rhs in
                          LinearTerm.simplify floored
                          |> mk_atomic `Leq coeff x)
                        coeffs_rhs in
       let res = Ctx.mk_or formulas in
       log_rewriting `Leq lhs rhs res;
       res
    | `TyFracQe ->
       let res = List.map (fun (coeff, rhs) -> mk_atomic `Leq coeff x rhs) coeffs_rhs
                 |> (fun l -> log_formulas "disjuncts of rewrite_leq:" l ; l)
                 |> Ctx.mk_or in
       log_rewriting `Leq lhs rhs res;
       res

  let rewrite_lt sort x lhs rhs =
    let coeffs_rhs = split sort x lhs rhs in
    match sort with
    | `TyIntQe ->
       let formulas =
         List.map (fun (coeff, rhs) ->
             let floored = Ctx.mk_floor rhs in
             let equal_case = Ctx.mk_and
                                [ mk_atomic `Eq coeff x floored
                                ; Ctx.mk_lt floored rhs
                                ]
             in
             Ctx.mk_or [mk_atomic `Lt coeff x floored; equal_case]
           )
           coeffs_rhs
       in Ctx.mk_or formulas
    | `TyFracQe ->
       List.map (fun (coeff, rhs) -> mk_atomic `Lt coeff x rhs) coeffs_rhs
       |> Ctx.mk_or

  let rewrite_modulo _sort _x lhs rhs mod_symbol divisor =
    Ctx.mk_app mod_symbol [lhs; rhs; divisor]

end

module Eliminate : sig

  val reduce : ?simplify:[`Normalize | `Simplify | `KeepOriginal]
               -> [`TyIntQe | `TyFracQe] -> Syntax.symbol
               -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end = struct

  let simplify_formula phi =
    let go phi =
      match phi with
      | `Tru -> Ctx.mk_true
      | `Fls -> Ctx.mk_false
      | `And phis -> Ctx.mk_and phis
      | `Or phis -> Ctx.mk_or phis
      | `Not phi -> Ctx.mk_not phi
      | `Quantify _ -> invalid_arg "Eliminate: expecting QF formula"
      | `Atom (`Arith (`Eq, t1, t2)) ->
         Ctx.mk_eq (LinearTerm.simplify t1) (LinearTerm.simplify t2)
      | `Atom (`Arith (`Leq, t1, t2)) ->
         Ctx.mk_leq (LinearTerm.simplify t1) (LinearTerm.simplify t2)
      | `Atom (`Arith (`Lt, t1, t2)) ->
         Ctx.mk_lt (LinearTerm.simplify t1) (LinearTerm.simplify t2)
      | `Atom (`ArrEq _) -> invalid_arg "Eliminate: array theory not supported"
      | `Proposition (`Var _) ->
         invalid_arg "Eliminate: not expecting a propositional variable"
      | `Proposition (`App (sym, args)) ->
         Ctx.mk_app sym args
      | `Ite _ -> invalid_arg "Eliminate: ITE should have been removed"
    in
    Syntax.Formula.eval lira_ctx go phi

  let reduce ?simplify:(simplify = `Normalize) sort x phi =
    let clean psi = match simplify with
      | `Normalize -> simplify_formula psi
                      |> Quantifier.normalize lira_ctx |> snd
      | `Simplify -> simplify_formula psi
      | `KeepOriginal -> psi
    in
    let go phi =
      match phi with
      | `Tru -> Ctx.mk_true
      | `Fls -> Ctx.mk_false
      | `And phis -> Ctx.mk_and phis
      | `Or phis -> Ctx.mk_or phis
      | `Not phi -> Ctx.mk_not phi
      | `Quantify _ -> invalid_arg "Eliminate: expecting QF formula"
      | `Atom (`Arith (`Eq, t1, t2)) ->
         (* AtomicRewriter.simplify_atomic `Eq t1 t2 *)
         clean (AtomicRewriter.rewrite_eq sort x t1 t2)
      | `Atom (`Arith (`Leq, t1, t2)) ->
      (* AtomicRewriter.simplify_atomic `Leq t1 t2 *)
         clean (AtomicRewriter.rewrite_leq sort x t1 t2)
      | `Atom (`Arith (`Lt, t1, t2)) ->
         clean (AtomicRewriter.rewrite_lt sort x t1 t2)
      | `Atom (`ArrEq _) -> invalid_arg "Eliminate: array theory not supported"
      | `Proposition (`Var _) ->
         invalid_arg "Eliminate: not expecting a propositional variable"
      | `Proposition (`App (sym, [t1; t2; t3]))
           when String.equal (Syntax.show_symbol lira_ctx sym) "mod" ->
         let f = Syntax.Expr.arith_term_of lira_ctx in
         AtomicRewriter.rewrite_modulo sort x (f t1) (f t2) sym (f t3)
      | `Proposition (`App (sym, args)) ->
         (* NK: This typechecks because we can arbitrarily instantiate
            the target ['typ] in [expr].
            The implementation can satisfy such a type because the type parameter
            is phantom and terms in the type appear in all instances of the type.
            (The "same" term in different type instances may technically be different terms,
            but in any context relating the two, it must be typed consistently at
            one type, so this difference is never observed.)
          *)
         Ctx.mk_app sym args
      | `Ite _ -> invalid_arg "Eliminate: ITE should have been removed"
    in
    let res = Syntax.Formula.eval lira_ctx go phi in
    Log.logf ~level:`debug
      "@[Eliminate: reduce: eliminating @[%a@] from @[%a@] yields @[%a@]@;"
      (Syntax.pp_symbol lira_ctx) x
      (Syntax.Formula.pp lira_ctx) phi
      (Syntax.Formula.pp lira_ctx) res;
    res

end

module Test = struct

  let qe_as (sort: [`TyIntQe | `TyFracQe]) (phi: Ctx.t Syntax.formula) =
    let (prefix, qf) = Quantifier.normalize lira_ctx phi in
    let qf_cleaned = Syntax.eliminate_ite lira_ctx qf in
    Log.logf ~level:`always "@[Input formula is: %a@]@;" (Syntax.Expr.pp lira_ctx) phi;
    Log.logf ~level:`always
      "@[@[Quantifier-free part after normalization is:@]@; @[%a@]@]@;" (Syntax.Expr.pp lira_ctx)
      qf_cleaned;
    let exists x phi =
      Eliminate.reduce sort x phi
    in
    List.fold_right
      (fun (qt, x) qf ->
        match qt with
        | `Exists ->
           exists x (snd (Quantifier.normalize lira_ctx qf))
        | `Forall ->
           Ctx.mk_not (exists x (snd (Quantifier.normalize lira_ctx
                                        (Ctx.mk_not qf)))))
      prefix (* fold over quantifiers *)
      qf_cleaned

end

let weispfenning_qe
      (x : Syntax.symbol)
      (qf_formula : Ctx.t Syntax.formula) : Ctx.t Syntax.formula =
  (* Syntax.Formula.eval lira_ctx weipsfenning_transform qf_formula *)
  SplitVariables.transform x qf_formula
  |> (fun (xi, u, phi) ->
    Eliminate.reduce `TyIntQe xi phi
    |> Eliminate.reduce `TyFracQe u)

let qe phi =
  (* essentially stolen from Quantifier.ml *)
  (* Normalization turns all negated formulas into positive formulas by using < and <=,
     turns all de Bruijn indices into constant symbols, etc.
   *)
  let (prefix, qf) = Quantifier.normalize lira_ctx phi in
  let qf_cleaned = Syntax.eliminate_ite lira_ctx qf in
  Log.logf ~level:`always "@[Input formula is: %a@]@;" (Syntax.Expr.pp lira_ctx) phi;
  Log.logf "@[Quantifier-free part before ITE elim is: %a@]@;" (Syntax.Expr.pp lira_ctx) qf;
  Log.logf ~level:`always
    "@[Quantifier-free part after ITE elim is: %a@]@;" (Syntax.Expr.pp lira_ctx) qf_cleaned;
  let exists x phi = weispfenning_qe x phi
  in
  List.fold_right
    (fun (qt, x) qf ->
      match qt with
      | `Exists ->
         exists x (snd (Quantifier.normalize lira_ctx qf))
      | `Forall ->
         Ctx.mk_not (exists x (snd (Quantifier.normalize lira_ctx
                                      (Ctx.mk_not qf)))))
    prefix (* fold over quantifiers *)
    qf_cleaned
