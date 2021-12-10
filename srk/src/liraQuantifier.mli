
module SplitVariables : sig

  (** phi ---> phi[x |-> x_int + x_frac] *)

  val transform : 'a Syntax.context
                  -> Syntax.symbol -> 'a Syntax.formula
                  -> Syntax.symbol * Syntax.symbol * 'a Syntax.formula

end

module LiraQe (Ctx: Syntax.Context) : sig

  (** Given quantifier-free phi that contains a free variable x
      of integer or fractional (in [0, 1)) sort,
      [reduce sort x phi] is a QF-formula such that
      (1) it is equivalent to phi in the theory of reals,
      (2) all terms containing x are terms in LRA if x is of fractional sort,
      and in LIA if x is of integer sort; in either case, x is not in the scope
      of floor (to_int).
      (3) all atomic subformulas containing x are essentially atomic formulas
      in LRA if x is of fractional sort, and in LIA if x is of integer sort.

      The "essential" qualification in (3) is because terms in these formulas
      may not be in the language of LRA/LIA, but these terms do not contain x
      (by (2)) and can be replaced by a fresh variable along with a defining
      equality in the context, resulting in atomic formulas that are in LRA/LIA.

      Then, to eliminate x, run LRA QE and LIA QE on this result.
   *)
  val reduce : ?simplify:[`Normalize | `Simplify | `KeepOriginal]
               -> [`TyIntQe | `TyFracQe] -> Syntax.symbol
               -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

  (** DO NOT USE; for testing only *)
  val qe_as : [`TyIntQe | `TyFracQe] -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

  (** DO NOT USE; for testing only *)
  val qe : Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end
