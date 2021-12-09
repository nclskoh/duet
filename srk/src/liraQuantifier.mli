
module Ctx : Syntax.Context

val qe: Ctx.formula -> Ctx.formula

module Test : sig

  (** Eliminate quantifiers with all variables treated as integer type or fractional
      type (taking values in the interval [0, 1)).
   *)
  val qe_as : [`TyIntQe | `TyFracQe]
              -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end

module Eliminate : sig

  val reduce : ?simplify:[`Normalize | `Simplify | `KeepOriginal]
               -> [`TyIntQe | `TyFracQe] -> Syntax.symbol
               -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end

module LinearTerm : sig

  (** A simplified term (linear term) is of the form:

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
