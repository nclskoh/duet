
module Ctx : Syntax.Context

val qe: Ctx.formula -> Ctx.formula

module Test : sig

  (** Eliminate quantifiers with all variables treated as integer type or fractional
      type (taking values in the interval [0, 1)).
   *)
  val qe_as : [`TyIntQe | `TyFracQe]
              -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end

module IntegerFrac : sig

  (** Given a symbol [x], introduce a fresh variable [x_int] denoting its
      integer part and a fresh variable [x_frac] denoting its fractional part.
   *)

  val register_int_frac_symbols_of : Syntax.symbol -> unit

  val int_symbol_of : Syntax.symbol -> Syntax.symbol

  val frac_symbol_of : Syntax.symbol -> Syntax.symbol

end

module SplitVariables : sig

  (** phi ---> phi[x |-> x_int + x_frac] *)

  val transform : Syntax.symbol -> Ctx.formula
                  -> Syntax.symbol * Syntax.symbol * Ctx.formula

end

module LinearTerm : sig

  type t

  val pp : Format.formatter -> t -> unit

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

end

module NormalTerm : sig

  (** A normalized term is conceptually of the form n x + s, where
      n \in ZZ, x is a variable (symbol), and s is a term not containing x.
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

end

module NormalizeTerm : sig

  val normalize_term : [`TyIntQe | `TyFracQe] -> Syntax.symbol
                       -> Ctx.arith_term -> NormalTerm.t list

  (* Lift binary operation on normal terms to binary operation on sets
     of normal terms; (A, B) |-> { a op b : a in A, b in B }.
   *)
  val binary_op : (NormalTerm.t -> NormalTerm.t -> NormalTerm.t)
                  -> NormalTerm.t list -> NormalTerm.t list
                  -> NormalTerm.t list

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
end
