
module Ctx : Syntax.Context

val qe: Ctx.formula -> Ctx.formula

module Test : sig

  (** Eliminate quantifiers with all variables treated as integer type or fractional
      type (taking values in the interval [0, 1)).
   *)
  val qe_as : [`TyIntQe | `TyFracQe]
              -> Ctx.t Syntax.formula -> Ctx.t Syntax.formula

end
