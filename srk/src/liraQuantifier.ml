(**

   L = (0, 1, +, -/1, floor/to_int, =, <, <=, = mod k)

   Algorithm:

    1. \exists x. \psi ---> \exists xi. \exists u. \psi[x |-> xi + u]

    2. \exists xi/u. \psi --->

       a. Make terms into PA and LRA terms that are of the form
          [n * xi + s] or [n * u + s], where [s] is free of [xi] or [u].

          Call such a term a "normal term".
          For a term t, let T_{xi}(t) be the set of normal terms such that
          R, t = floor(t) \models \bigvee_{n xi + s in T_{xi}(t)} (t = n xi + s).
          Similarly, let T_u(t) be the set of normal terms such that
          R, 0 <= u < 1 \models \bigvee_{n u + s in T} (t = nu + s).

          T_{xi}, T_u are defined recursively as follows.

          - 0, 1, variable: T(-) = {-}, i.e., unchanged/singleton.
          - c * x, x * c for c an expression denoting an integer:
            T(c x) = { simplify(c) t' : t' in T(x) },
            where simplify simplifies its argument into an integer  constant.
          - T(t1 + t2) = { simplify(t1' + t2') : t1' in T(t1), t2' in T(t2) },
            where simplify regroups terms and simplifies coefficients.
          - T(-t) = { simplify(-t') : t' in T(t) }.

          - T_{xi}(floor(t)) = { n xi + floor(s) : n xi + s in T(t) }

            T_u(floor(t)) = 
            \bigcup_{nu + s in T_u(t)} { i + floor(s) : i in {0, 1, ..., n} }
            if n >= 0.

            T_u(floor(t)) = 
            \bigcup_{nu + s in T_u(t)} { i + floor(s) : i in {n, n-1, ..., 0} }

            T_u(floor(t)) = 
            \bigcup_{0u + s in T_u(t)} { floor(s) }.

          Result: all terms are of the form [n * xi + floor(s)] or
          [n * u + floor(s)].

       b. Reduce atomic formulas into PA and LRA formulas, specifically
          LIRA in Z3 (https://smtlib.cs.uiowa.edu/theories-Reals_Ints.shtml,
          AUFLIRA).

          i. Using T_{xi} or T_u, depending on what is to be eliminated,
             normalize each atom to be of the form [n xi R s], [nu R s],
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

            nu - s = floor(nu) + (nu)* - (floor(s) + s* ) \in kZZ \subseteq ZZ.
            Hence, (nu)* - s* \in ZZ.
            Since 0 <= (nu)*, s* < 1, -1 < (nu)* - s* < 1, so (nu)* - s* = 0,
            i.e., [(nu)* = s*].

            Suppose n > 0 first. [0 <= nu < n], so floor(nu) = 0, 1, ..., n - 1.
            Consequently,
            [nu = floor(nu) + (nu)* = i + (nu)* = i + s*] for some i = 0, ..., n - 1,
            i.e., [nu = i + (s - floor(s))] for i = 0, ..., n - 1.

            When floor(nu) = i, i - floor(s) = floor(nu) - floor(s) \in kZZ,
            so floor(s) \equiv i mod k.

            Call this transformation F, so the reduction result is F(\psi).
 *)

(* module Ctx = SrkAst.Ctx *)

(*
  module Ctx = Syntax.MakeContext ()
  let lira_ctx = Ctx.context
 *)

let rec range_towards_zero n =
  if n = 0 then [0]
  else if n > 0 then n :: range_towards_zero (n - 1)
  else n :: range_towards_zero (n + 1)

let rational_of srk t =
  let go t =
    match t with
    | `Real r -> r
    | `Add rationals -> List.fold_left QQ.add QQ.zero rationals
    | `Mul rationals -> List.fold_left QQ.mul QQ.one rationals
    | `Binop (`Div, num, denom) -> QQ.div num denom
    | `Binop (`Mod, dividend, divisor) -> QQ.modulo dividend divisor
    | `Unop (`Floor, r) -> QQ.of_zz (QQ.floor r)
    | `Unop (`Neg, r) -> QQ.negate r
    | _ -> invalid_arg "rational_of: cannot interpret as a numeric constant"
  in Syntax.ArithTerm.eval srk go t

module IntegerFrac : sig

  (** Given a symbol [x], introduce a fresh variable [x_int] denoting its
      integer part and a fresh variable [x_frac] denoting its fractional part.
   *)

  val register_int_frac_symbols_of : 'a Syntax.context -> Syntax.symbol -> unit

  val int_symbol_of : 'a Syntax.context -> Syntax.symbol -> Syntax.symbol

  val frac_symbol_of : 'a Syntax.context -> Syntax.symbol -> Syntax.symbol

end = struct

  let annotate s suffix = String.concat "_" [s; suffix]

  let make_frac s = annotate s "frac"

  let make_int s = annotate s "int"

  let register_int_frac_symbols_of srk s =
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

  let int_symbol_of srk s =
    Syntax.show_symbol srk s
    |> make_int
    |> Syntax.get_named_symbol srk

  let frac_symbol_of srk s =
    Syntax.show_symbol srk s
    |> make_frac
    |> Syntax.get_named_symbol srk

end

module SplitVariables : sig

  (** phi ---> phi[x |-> x_int + x_frac] *)

  val transform : 'a Syntax.context
                  -> Syntax.symbol -> 'a Syntax.formula
                  -> Syntax.symbol * Syntax.symbol * 'a Syntax.formula

end = struct

  let transform srk x phi =
    IntegerFrac.register_int_frac_symbols_of srk x;
    let xi = IntegerFrac.int_symbol_of srk x in
    let u = IntegerFrac.frac_symbol_of srk x in
    let x' = Syntax.mk_add srk [Syntax.mk_const srk xi; Syntax.mk_const srk u] in
    let sigma sym =
      if Syntax.Symbol.compare sym x = 0 then x'
      else Syntax.mk_const srk sym in
    (xi, u, Syntax.substitute_const srk sigma phi)

end

module LinearTerm (Ctx : Syntax.Context) : sig

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

  (*

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

  val pp : Format.formatter -> t -> unit

  *)

  val simplify: Ctx.arith_term -> Ctx.arith_term

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

  let srk = Ctx.context

  (*
  (** Keys are simplified terms without coefficients, and values are non-zero coefficients.
      A non-zero rational number r is represented with key "1" and value r;
      0 is itself represented by the empty table.
   *)
  type t = QQ.t H.t
   *)

  let table () = H.create 11
  let insert = H.replace

  let pp fmt t =
    if H.is_empty t then
      Format.fprintf fmt "(0, 0)"
    else
      begin
        H.iter (fun term coeff ->
            Format.fprintf Format.str_formatter "(term: %a, coeff: %a), "
              (Syntax.ArithTerm.pp srk)
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
            match Syntax.ArithTerm.destruct srk term with
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
      try
        Some (rational_of srk term)
      with
        Invalid_argument _ -> None
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
            | None, Some coeff -> Some coeff)
        t1 t2 in
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

  let rec of_term term =
    let go t =
      match t with
      | `Real r -> real r
      | `App (x, args) -> app x (List.map (fun arg ->
                                     Syntax.Expr.arith_term_of srk arg
                                     |> of_term) args)
      | `Var (i, typ) -> var i typ
      (* TODO: Check that we don't have variables after normalization. *)
      | `Add ts -> List.fold_left add zero ts
      | `Mul ts -> List.fold_left mul (real QQ.one) ts
      | `Binop (`Div, t1, t2) -> div t1 t2
      | `Unop (`Floor, t') -> floor t'
      | `Unop (`Neg, t') -> negate t'
      | `Binop (`Mod, _, _)
        | `Ite _
        | `Select _ -> invalid_arg "LinearTerm: cannot convert term, unsupported"
    in Syntax.ArithTerm.eval srk go term

  let simplify term =
    term
    |> of_term
    |> (fun converted -> Log.logf ~level:`trace "@[LinearTerm: of_term(%a) = %a@]@;"
                           (Syntax.ArithTerm.pp srk) term
                           pp converted
                       ; converted)
    |> to_term
    |> (fun res -> Log.logf ~level:`trace "@[LinearTerm: to_term(...) = %a@]@;"
                     (Syntax.ArithTerm.pp srk) res
                 ; res)

end

module NormalTerm (Ctx : Syntax.Context) : sig

  (** A normalized term is conceptually of the form (n x + s, \phi), where
      n \in ZZ, x is a variable (symbol), and s is a term not containing x.
      When x is an integer variable, \phi is just true.
      If x is a fractional variable, it is a formula in x that is
      (1) in the language of LRA, and
      (2) if t is a term that normalizes to (nx + s, \phi)
          (via. [NormalizeTerm.normalize_term]),
          and M is a model such that [M \models \phi],
          then [M \models t = nx + s].

      TODO: This is bad design because of the dependence on [NormalizeTerm]; 
      refactor.
   *)

  type t

  val pp : Format.formatter -> t -> unit

  val zero : Syntax.symbol -> t (* 0 x + 0 *)

  val coeff : t -> QQ.t (* coefficient of x *)

  val symbol : t -> Syntax.symbol

  val rest_of : t -> Ctx.arith_term

  val term_of : t -> Ctx.arith_term

  val condition_of : t -> ([`Leq | `Lt] * Ctx.arith_term * Ctx.arith_term) list
  (* interpret as a conjunction of atoms *)

  val formula_of_condition : ([`Leq | `Lt] * Ctx.arith_term * Ctx.arith_term) -> Ctx.formula

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

  let srk = Ctx.context

  module LT = LinearTerm(Ctx)

  type t = { sym : Syntax.symbol
           ; coeff : QQ.t
           ; rest : Ctx.arith_term option
           ; condition : ([`Leq | `Lt] * Ctx.arith_term * Ctx.arith_term) list (* interpreted conjunctively; each atom is an LRA atom *)
           }

  let formula_of_condition (tag, lhs, rhs) =
    match tag with
    | `Leq -> Ctx.mk_leq lhs rhs
    | `Lt -> Ctx.mk_lt lhs rhs

  let pp fmt t =
    Format.fprintf fmt "[%a %a + %a, %a]"
      QQ.pp t.coeff
      (Syntax.pp_symbol srk) t.sym
      (Format.pp_print_option (Syntax.ArithTerm.pp srk)) t.rest
      (Format.pp_print_list
         ~pp_sep:(fun fmt _ -> Format.pp_print_string fmt ", ")
         (Syntax.Formula.pp srk))
      (List.map formula_of_condition t.condition)

  let zero s = { sym = s ; coeff = QQ.zero ; rest = None ;  condition = [] }

  let coeff t = t.coeff

  let symbol t = t.sym

  let condition_of t = t.condition

  let coerce_rational = function
    | None -> QQ.zero
    | Some term -> rational_of srk term

  let rest_of t =
    match t.rest with
    | None -> Ctx.mk_real QQ.zero
    | Some rest -> LT.simplify rest (* TODO: Should we simplify here? *)

  let term_of t =
    (* TODO: verify that it's fine to output a symbol, which may be undefined
       in the quantifier-free context before we eliminate.
     *)
    let nx =
      (* keep 0 coefficient for now in case we don't want terms to just disappear *)
      if QQ.equal t.coeff QQ.one then Ctx.mk_const t.sym
      else if QQ.equal t.coeff (QQ.negate QQ.one) then Ctx.mk_neg (Ctx.mk_const t.sym)
      else Ctx.mk_mul [Ctx.mk_real t.coeff; Ctx.mk_const t.sym]
    in
    match t.rest with
    | None -> nx
    | Some rest -> LT.simplify (Ctx.mk_add [nx ; rest])

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
          begin
            match t1.rest, t2.rest with
            | None, _ -> t2.rest
            | _, None -> t1.rest
            | Some rest1, Some rest2 -> Some (Ctx.mk_add [rest1; rest2])
          end
      ; condition = List.append t1.condition t2.condition
      }
    else invalid_arg "NormalTerm: cannot add normal terms with different distinguished symbols"

  let mul_rational r t =
    { sym = t.sym
    ; coeff = QQ.mul r t.coeff
    ; rest =
        begin
          match t.rest with
          | None -> None
          | Some rest -> Some (Ctx.mk_mul [Ctx.mk_real r; rest])
        end
    ; condition = t.condition
    }

  let mul t1 t2 =
    let zero_rat r = QQ.equal r QQ.zero in
    if t1.sym <> t2.sym then
      invalid_arg "NormalTerm: distinguished symbols must be the same for multiplication"
    else if not (zero_rat t1.coeff) && not (zero_rat t2.coeff) then
      invalid_arg "NormalTerm: non-linear multiplication"
    else
      let multiply rat t =
        let t' = mul_rational (coerce_rational rat.rest) t in
        { t' with condition = List.append rat.condition t'.condition }
      in
      if zero_rat t1.coeff then
        multiply t1 t2
      else
        multiply t2 t1

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
        let t = mul_rational (QQ.inverse n) t1 in
        { t with condition = List.append t.condition t2.condition }

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
          ; rest = Some (Ctx.mk_real (QQ.modulo (coerce_rational t1.rest) n))
          ; condition = List.append t1.condition t2.condition
          }
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
         (* This is a little subtle, but [n] itself should be included even when n is positive,
            because n u + s can exceed n after adding s, and flooring gives n + floor(s)
            and not (n - 1) + floor(s).
          *)
         List.map QQ.of_int (range_towards_zero n)
       in
       let sum term n =
         let new_rest = match term with
           | None -> Ctx.mk_real n
           | Some term -> Ctx.mk_add [Ctx.mk_real n; term]
         in
         { sym = t.sym
         ; coeff = QQ.zero
         ; rest = Some new_rest
         ; condition =
             let t_expr = term_of t in
             [ (`Leq, new_rest, t_expr)
             ; (`Lt, t_expr, Ctx.mk_add [new_rest; Ctx.mk_real QQ.one]) ]
         }
       in
       begin
         Log.logf ~level:`trace "@[NormalTerm: floor: possibilities are: %a@]@;"
           (Format.pp_print_list ~pp_sep:Format.pp_print_space QQ.pp)
           possibilities;
         let result =
           match t.rest with
           | None ->
              (* {0, 1, ..., n } + floor(0), similarly for negative n *)
              List.map (sum None) possibilities
           | Some rest ->
              (* {0, 1, ..., n} + floor(s), similarly for negative n *)
              List.map (sum (Some (Ctx.mk_floor rest))) possibilities
         in
         Log.logf ~level:`debug "@[NormalTerm for %a: fractional floor(%a) = %a@]@;"
           (Syntax.pp_symbol srk) t.sym
           pp t
           (Format.pp_print_list ~pp_sep:Format.pp_print_space pp)
           result;
         result
       end

end

module NormalizeTerm (Ctx : Syntax.Context): sig

  module NT : module type of NormalTerm (Ctx)

  (** Given a term, return the set of possible normal terms corresponding to it.
   *)
  val normalize_term : [`TyIntQe | `TyFracQe]
                       -> Syntax.symbol
                       -> Ctx.arith_term -> NT.t list

  (* Lift binary operation on normal terms to binary operation on sets
     of normal terms; (A, B) |-> { a op b : a in A, b in B }.
   *)
  val binary_op : (NT.t -> NT.t -> NT.t)
                  -> NT.t list -> NT.t list
                  -> NT.t list

end = struct

  module NT = NormalTerm(Ctx)

  let pp = Format.pp_print_list ~pp_sep:Format.pp_print_space
             NT.pp

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

  let all_sums s = cartesian_product NT.add (NT.zero s)

  let all_products s =
    cartesian_product NT.mul
      (NT.zero s |> NT.add_rest (Ctx.mk_real QQ.one))

  let normalize_term (sort: [`TyIntQe | `TyFracQe]) x term =
    let go term =
      match term with
      | `Real r -> [NT.zero x |> NT.add_rest (Ctx.mk_real r)]
      | `App (sym, args) ->
         if args = [] then
           if Syntax.Symbol.compare sym x = 0 then
             [ NT.zero x |> NT.add_sym QQ.one ]
           else
             [ NT.zero x |> NT.add_rest (Ctx.mk_app sym args) ]
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
         binary_product NT.div num denum
      | `Binop (`Mod, dividend, divisor) ->
         binary_product NT.modulo dividend divisor
      | `Unop (`Floor, terms) ->
         let res =
           List.fold_left
             (fun curr t -> List.append curr (NT.floor sort t))
             []
             terms
         in
         Log.logf ~level:`trace "@[NormalizeTerm: floor({%a}) = {%a}@]@;"
           pp terms pp res;
         res

      | `Unop (`Neg, terms) ->
         terms
         |> List.map NT.negate
      | `Ite _
        | `Select _ -> invalid_arg "NormalizeTerm: unsupported" in
    let res = Syntax.ArithTerm.eval Ctx.context go term in
    Log.logf ~level:`debug "@[@[NormalizeTerm: normalizing @[%a@] gives@]@; @[%a@]@]@;"
      (Syntax.ArithTerm.pp Ctx.context) term pp res;
    res

end

module AtomicRewriter (Ctx : Syntax.Context) : sig

  val rewrite_eq :
    ?simplify:[`Normalize | `Simplify | `KeepOriginal]
    -> ?z3lira:bool
    -> [`TyIntQe | `TyFracQe]
    -> Syntax.symbol
    -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

  val rewrite_leq :
    ?simplify:[`Normalize | `Simplify | `KeepOriginal]
    -> ?z3lira:bool    
    -> [`TyIntQe | `TyFracQe]
    -> Syntax.symbol
    -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

  val rewrite_lt :
    ?simplify:[`Normalize | `Simplify | `KeepOriginal]
    -> ?z3lira:bool    
    -> [`TyIntQe | `TyFracQe]
    -> Syntax.symbol
    -> Ctx.arith_term -> Ctx.arith_term -> Ctx.formula

  val rewrite_modulo :
    ?simplify:[`Normalize | `Simplify | `KeepOriginal]
    -> ?z3lira:bool    
    -> [`TyIntQe | `TyFracQe]
    -> Syntax.symbol
    -> Ctx.arith_term -> Ctx.arith_term
    -> Syntax.symbol (* TODO: remove the need for this modulo symbol *)
    -> Ctx.arith_term
    -> Ctx.formula

end = struct

  let srk = Ctx.context

  module Normalize = NormalizeTerm(Ctx)
  module LT = LinearTerm(Ctx)

  let pp_lhs_rhs_cond_list l =
    Format.pp_print_list ~pp_sep:Format.pp_print_space
      (fun fmt (coeff, rhs, cond) ->
        Format.fprintf fmt "(LHS coeff: %a, RHS term: %a, holds under: %a)"
          QQ.pp coeff (Syntax.ArithTerm.pp srk) rhs
          (Format.pp_print_list
             ~pp_sep:(fun fmt _ -> Format.pp_print_string fmt ", ")
             (Syntax.Formula.pp srk)) (List.map Normalize.NT.formula_of_condition cond))
      l

  let log_formulas prefix l =
    Log.logf ~level:`trace
      "@[AtomicRewriter: %s: %a@]@;"
      prefix
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
         (Syntax.Formula.pp srk)) l

  let log_rewriting (relation : [`Eq | `Leq | `Lt | `Modulo of Syntax.symbol * QQ.t])
        lhs rhs result =
    let rel_symbol = match relation with
      | `Eq -> "="
      | `Leq -> "<="
      | `Lt -> "<"
      | `Modulo (_, k) -> Format.asprintf "mod_%a" QQ.pp k
    in
    Log.logf ~level:`debug "@[@[AtomicRewriter: rewritten @[(%a %s %a)@] into@]@; %a@]@;"
      (Syntax.ArithTerm.pp srk) lhs
      rel_symbol
      (Syntax.ArithTerm.pp srk) rhs
      (Syntax.Formula.pp srk) result

  let split sort x lhs rhs =
    (* Make into the form (nx, s) corresponding to [nx op s] *)
    let lhs_terms = Normalize.normalize_term sort x lhs in
    let rhs_terms = Normalize.normalize_term sort x rhs in
    let terms = Normalize.binary_op
                  (fun t1 t2 -> Normalize.NT.add t1 (Normalize.NT.negate t2))
                  lhs_terms rhs_terms in
    let coeffs_rhs_conds =
      List.map
        (fun t ->
          let rhs = Normalize.NT.rest_of t
                    |> (fun rest -> Log.logf ~level:`trace "AtomicRewriter: Rest: %a"
                                      (Syntax.ArithTerm.pp srk) rest; rest)
                    |> Ctx.mk_neg
                    |> LT.simplify (* probably a good idea to always simplify *)
                    |>
                      (fun simplified ->
                        Log.logf
                          ~level:`trace "AtomicRewriter: simplified negated rest: %a"
                          (Syntax.ArithTerm.pp srk) simplified; simplified)
          in
          (Normalize.NT.coeff t, rhs, Normalize.NT.condition_of t))
        terms
    in
    Log.logf ~level:`trace "@[AtomicRewriter: splitting (%a, %a) gives %a@]@;"
      (Syntax.ArithTerm.pp srk) lhs
      (Syntax.ArithTerm.pp srk) rhs
      pp_lhs_rhs_cond_list coeffs_rhs_conds;
    coeffs_rhs_conds

  let mk_monomial coeff x =
    Ctx.mk_mul [Ctx.mk_real coeff ; Ctx.mk_const x]

  let mk_atomic
        ?simplify:(simplify = `Simplify)
        ?z3lira:(z3lira = true) (* output modulo function instead of mod relation *)
        (atom: [< `Eq | `Leq | `Lt | `Modulo of Syntax.symbol * QQ.t ])
        lhs rhs =
    let mk_atom op simplify lhs rhs =
      let lhs, rhs = match simplify with
        | `Simplify -> (LT.simplify lhs, LT.simplify rhs)
        | `Normalize -> (LT.simplify (Ctx.mk_add [lhs; Ctx.mk_neg rhs])
                        , Ctx.mk_real QQ.zero)
        | `KeepOriginal -> (lhs, rhs)
      in
      op lhs rhs
    in
    match atom with
    | `Eq -> mk_atom Ctx.mk_eq simplify lhs rhs
    | `Leq -> mk_atom Ctx.mk_leq simplify lhs rhs
    | `Lt -> mk_atom Ctx.mk_lt simplify lhs rhs
    | `Modulo (mod_sym, k) ->
       if z3lira then
         mk_atom (fun lhs rhs -> Ctx.mk_eq (Ctx.mk_mod lhs (Ctx.mk_real k)) rhs)
           `Normalize lhs rhs
       else
         mk_atom
           (fun lhs rhs -> Ctx.mk_app mod_sym [lhs ; rhs; Ctx.mk_real k])
           simplify
           lhs
           rhs

  let strengthen_with_integral_rhs
        ?simplify:(simplify = `Simplify)
        (rel : [`Eq | `Modulo of Syntax.symbol * QQ.t])
        coeff x rhs =
    (* Strengthen = or mod_k by flooring RHS and asserting that RHS is integral *)
    let floored = Ctx.mk_floor rhs in
    let strengthened =
      mk_atomic ~simplify rel (mk_monomial coeff x) floored in
    let integral = mk_atomic ~simplify `Eq rhs floored in
    Ctx.mk_and [strengthened; integral]

  let rewrite_eq ?simplify:(simplify = `Simplify) ?z3lira:(z3lira = true)
        sort x lhs rhs =
    let coeffs_rhs_conds = split sort x lhs rhs in
    match sort with
    | `TyIntQe ->
       let formulas = List.map (fun (coeff, rhs, cond) ->
                          (* For integer elimination, condition should just be true *)
                          assert (cond = []);
                          strengthen_with_integral_rhs ~simplify `Eq coeff x rhs
                        )
                        coeffs_rhs_conds in
       let res = Ctx.mk_or formulas in
       log_rewriting `Eq lhs rhs res;
       res
    | `TyFracQe ->
       let res = List.map (fun (coeff, rhs, cond) ->
                     let atom = mk_atomic ~simplify ~z3lira `Eq (mk_monomial coeff x) rhs in
                     let side_conditions =
                       List.map (fun (tag, lhs, rhs) ->
                           mk_atomic ~simplify ~z3lira tag lhs rhs) cond in
                     Ctx.mk_and (atom :: side_conditions)
                   )
                   coeffs_rhs_conds
                 |> Ctx.mk_or
       in
       log_rewriting `Eq lhs rhs res;
       res

  let rewrite_leq
        ?simplify:(simplify = `Simplify)
        ?z3lira:(z3lira = true)
        sort x lhs rhs =
    let coeffs_rhs_conds = split sort x lhs rhs in
    Log.logf ~level:`trace "@[AtomicRewriter: rewrite_leq: coeffs_rhs: %a@]@;"
      pp_lhs_rhs_cond_list coeffs_rhs_conds;
    match sort with
    | `TyIntQe ->
       let formulas =
         List.map (fun (coeff, rhs, cond) ->
             assert (cond = []);
             let floored = Ctx.mk_floor rhs in
             mk_atomic ~simplify `Leq (mk_monomial coeff x) floored)
           coeffs_rhs_conds in
       let res = Ctx.mk_or formulas in
       log_rewriting `Leq lhs rhs res;
       res
    | `TyFracQe ->
       let res =
         List.map (fun (coeff, rhs, cond) ->
             let atom = mk_atomic ~simplify ~z3lira `Leq (mk_monomial coeff x) rhs in
             let side_conditions =
               List.map (fun (tag, lhs, rhs) ->
                   mk_atomic ~simplify ~z3lira tag lhs rhs) cond in
             Ctx.mk_and (atom :: side_conditions)
           )
           coeffs_rhs_conds
         |> (fun l -> log_formulas "disjuncts of rewrite_leq:" l ; l)
         |> Ctx.mk_or in
       log_rewriting `Leq lhs rhs res;
       res

  let rewrite_lt
        ?simplify:(simplify = `Simplify)
        ?z3lira:(z3lira = true)
        sort x lhs rhs =
    let coeffs_rhs_conds = split sort x lhs rhs in
    match sort with
    | `TyIntQe ->
       let formulas =
         List.map (fun (coeff, rhs, cond) ->
             assert (cond = []);
             let floored = Ctx.mk_floor rhs in
             let equal_case = Ctx.mk_and
                                [ mk_atomic ~simplify `Eq (mk_monomial coeff x) floored
                                ; mk_atomic ~simplify `Lt floored rhs
                                ]
             in
             Ctx.mk_or [mk_atomic ~simplify `Lt (mk_monomial coeff x) floored;
                        equal_case]
           )
           coeffs_rhs_conds in
       let res = Ctx.mk_or formulas in
       log_rewriting `Lt lhs rhs res;
       res
    | `TyFracQe ->
       let res =
         List.map (fun (coeff, rhs, cond) ->
             let atom = mk_atomic ~simplify `Lt (mk_monomial coeff x) rhs in
             let side_conditions =
               List.map (fun (tag, lhs, rhs) ->
                   mk_atomic ~simplify ~z3lira tag lhs rhs) cond in
             Ctx.mk_and (atom :: side_conditions)
           )
           coeffs_rhs_conds
         |> Ctx.mk_or in
       log_rewriting `Lt lhs rhs res;
       res

  let rewrite_modulo
        ?simplify:(simplify = `Simplify)
        ?z3lira:(z3lira = true)
        sort x lhs rhs mod_symbol divisor =
    let coeffs_rhs_conds = split sort x lhs rhs in
    let divisor_n = rational_of srk divisor in
    match sort with
    | `TyIntQe ->
       let formulas =
         List.map
           (fun (coeff, rhs, cond) ->
             assert (cond = []);
             strengthen_with_integral_rhs ~simplify (`Modulo (mod_symbol, divisor_n)) coeff x rhs)
           coeffs_rhs_conds
       in
       let res = Ctx.mk_or formulas in
       log_rewriting (`Modulo (mod_symbol, divisor_n)) lhs rhs res;
       res
    | `TyFracQe ->
       (* nu \equiv s mod k ==> (nu)* = s*
          ==>
          if n > 0: (nu = (s - floor(s)) + i /\ floor(s) \equiv i mod k)
                    for some i in {0, 1, ..., n-1},
          if n = 0: s = floor(s) /\ s \equiv 0 mod k, ignore until we eliminate a variable in s.
          if n < 0: n <= floor(nu) <= 0, nu = s* + floor(nu)
          so        nu = (s - floor(s)) + i for some i in {n, n + 1, ..., 0}
                    /\ floor(s) \equiv i mod k
        *)
       let adjoin_cases curr (coeff, rhs, cond) =
         let form_formula i =
           let num = Ctx.mk_real (QQ.of_int i) in
           let frac_constraint =
             mk_atomic ~simplify `Eq
               (mk_monomial coeff x)
               (Ctx.mk_add [ rhs
                           ; Ctx.mk_neg (Ctx.mk_floor rhs)
                           ; num]) in
           let mod_constraint =
             mk_atomic ~simplify (`Modulo (mod_symbol, divisor_n))
               (Ctx.mk_floor rhs)
               num
           in
           let side_conditions =
             List.map (fun (tag, lhs, rhs) ->
                 mk_atomic ~simplify ~z3lira tag lhs rhs) cond in
           Ctx.mk_and (List.append [frac_constraint; mod_constraint] side_conditions)
         in
         let possibilities =
           match QQ.to_int coeff with
           | None -> invalid_arg
                       (Format.asprintf
                          "AtomicRewrite: rewrite_modulo: non-integral coefficient?: %a"
                          QQ.pp coeff)
           | Some n ->
              if n > 0 then
                range_towards_zero (n - 1)
              else if n < 0 then
                range_towards_zero n
              else
                []
         in
         List.append (List.map form_formula possibilities) curr
       in
       let formulas = List.fold_left adjoin_cases [] coeffs_rhs_conds in
       Ctx.mk_or formulas

end

module Eliminate (Ctx : Syntax.Context) : sig

  val reduce : ?simplify:[`Normalize | `Simplify | `KeepOriginal]
               -> [`TyIntQe | `TyFracQe] -> Syntax.symbol
               -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end = struct

  (* TODO: Push simplify option and simplification to AtomicRewrite. *)
  (*
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
    Syntax.Formula.eval srk go phi
   *)

  let srk = Ctx.context
  module AR = AtomicRewriter(Ctx)

  let reduce ?simplify:(simplify = `Simplify) sort x phi =
    (*
    let clean psi = match simplify with
      | `Normalize -> simplify_formula psi
                      |> Quantifier.normalize srk |> snd
      | `Simplify -> simplify_formula psi
      | `KeepOriginal -> psi
    in
     *)
    let go phi =
      match phi with
      | `Tru -> Ctx.mk_true
      | `Fls -> Ctx.mk_false
      | `And phis -> Ctx.mk_and phis
      | `Or phis -> Ctx.mk_or phis
      | `Not phi -> Ctx.mk_not phi
      | `Quantify _ -> invalid_arg "Eliminate: expecting QF formula"
      | `Atom (`Arith (`Eq, t1, t2)) ->
         AR.rewrite_eq ~simplify sort x t1 t2
      | `Atom (`Arith (`Leq, t1, t2)) ->
         AR.rewrite_leq ~simplify sort x t1 t2
      | `Atom (`Arith (`Lt, t1, t2)) ->
         AR.rewrite_lt ~simplify sort x t1 t2
      | `Atom (`ArrEq _) -> invalid_arg "Eliminate: array theory not supported"
      | `Proposition (`Var _) ->
         invalid_arg "Eliminate: not expecting a propositional variable"
      | `Proposition (`App (sym, [t1; t2; t3]))
           when String.equal (Syntax.show_symbol srk sym) "mod" ->
         let f = Syntax.Expr.arith_term_of srk in
         AR.rewrite_modulo ~simplify sort x (f t1) (f t2) sym (f t3)
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
    let res = Syntax.Formula.eval srk go phi in
    Log.logf ~level:`debug
      "@[Eliminate: reduce: eliminating @[%a@] from @[%a@] yields @[%a@]@;"
      (Syntax.pp_symbol srk) x
      (Syntax.Formula.pp srk) phi
      (Syntax.Formula.pp srk) res;
    res

end

module LiraQe (Ctx : Syntax.Context) = struct

  let srk = Ctx.context
  module Elim = Eliminate(Ctx)

  let reduce = Elim.reduce

  let qe_as (sort: [`TyIntQe | `TyFracQe]) (phi: Ctx.t Syntax.formula) =
    let (prefix, qf) = Quantifier.normalize srk phi in
    let qf_cleaned = Syntax.eliminate_ite srk qf in
    Log.logf ~level:`always "@[Input formula is: %a@]@;" (Syntax.Expr.pp srk) phi;
    Log.logf ~level:`always
      "@[@[Quantifier-free part after normalization is:@]@; @[%a@]@]@;" (Syntax.Expr.pp srk)
      qf_cleaned;
    let exists x phi =
      let reduced = Elim.reduce sort x phi in
      Log.logf "@[Reduced formula is %a@]@;" (Syntax.Formula.pp srk) reduced;
      reduced
      (* Quantifier.mbp srk (fun s -> Syntax.compare_symbol s x <> 0) reduced *)
      (* Quantifier.qe_mbp srk reduced *)
    in
    List.fold_right
      (fun (qt, x) qf ->
        match qt with
        | `Exists ->
           exists x (snd (Quantifier.normalize srk qf))
        | `Forall ->
           Ctx.mk_not (exists x (snd (Quantifier.normalize srk
                                        (Ctx.mk_not qf)))))
      prefix (* fold over quantifiers *)
      qf_cleaned

  let weispfenning_qe
        (x : Syntax.symbol)
        (qf_formula : Ctx.formula) : Ctx.formula =
    SplitVariables.transform srk x qf_formula
    |> (fun (xi, u, phi) ->
      Elim.reduce `TyIntQe xi phi
      |> Elim.reduce `TyFracQe u)

  let qe phi =
    (* essentially stolen from Quantifier.ml *)
    (* Normalization turns all negated formulas into positive formulas by using < and <=,
     turns all de Bruijn indices into constant symbols, etc.
     *)
    let (prefix, qf) = Quantifier.normalize srk phi in
    let qf_cleaned = Syntax.eliminate_ite srk qf in
    Log.logf ~level:`always "@[Input formula is: %a@]@;" (Syntax.Expr.pp srk) phi;
    Log.logf "@[Quantifier-free part before ITE elim is: %a@]@;" (Syntax.Expr.pp srk) qf;
    Log.logf ~level:`always
      "@[Quantifier-free part after ITE elim is: %a@]@;" (Syntax.Expr.pp srk) qf_cleaned;
    let exists x phi = weispfenning_qe x phi
    in
    List.fold_right
      (fun (qt, x) qf ->
        match qt with
        | `Exists ->
           exists x (snd (Quantifier.normalize srk qf))
        | `Forall ->
           Ctx.mk_not (exists x (snd (Quantifier.normalize srk
                                        (Ctx.mk_not qf)))))
      prefix (* fold over quantifiers *)
      qf_cleaned

end
