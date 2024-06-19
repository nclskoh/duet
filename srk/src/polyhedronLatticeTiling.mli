(** Concept space of polyhedron-lattice-tilings (PLTs) *)

module LocalAbstraction: sig

  type ('concept1, 'point1, 'concept2, 'point2) t

  val apply: ('concept1, 'point1, 'concept2, 'point2) t ->
             'point1 -> 'concept1 -> 'concept2

  val compose:
    ('concept1, 'point1, 'concept2, 'point2) t ->
    ('concept2, 'point2, 'concept3, 'point3) t ->
    ('concept1, 'point1, 'concept3, 'point3) t

end

module Abstraction: sig

  type ('concept1, 'point1, 'concept2, 'point2) t

  val apply: ('concept1, 'point1, 'concept2, 'point2) t -> 'concept1 -> 'concept2

end

type dd = DD.closed DD.t * int

module LocalGlobal: sig

  val localize:
    ('concept1, 'point1, 'concept2, 'point2) Abstraction.t ->
    ('concept1, 'point1, 'concept2, 'point2) LocalAbstraction.t

  val lift_dd_abstraction:
    'a Syntax.context -> max_dim:int -> term_of_dim:(int -> 'a Syntax.arith_term) ->
    ('a Syntax.formula, 'a Interpretation.interpretation, dd, int -> QQ.t)
      LocalAbstraction.t ->
    ('a Syntax.formula, 'a Interpretation.interpretation, dd, int -> QQ.t)
      Abstraction.t

end

type plt

val formula_of_dd:
  'a Syntax.context -> (int -> 'a Syntax.arith_term) -> DD.closed DD.t ->
  'a Syntax.formula

val abstract_lw:
    max_dim_in_projected: int ->
    (Polyhedron.t, int -> QQ.t, dd, int -> QQ.t) LocalAbstraction.t

val abstract_sc:
  max_dim_in_projected: int ->
  (plt, int -> QQ.t, dd, int -> QQ.t) LocalAbstraction.t

val convex_hull: 'a Syntax.context -> 'a Syntax.formula ->
                 ('a Syntax.arith_term ) Array.t -> DD.closed DD.t
