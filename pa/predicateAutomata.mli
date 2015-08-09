open Apak

module type Sigma = sig
  type t
  val pp : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
end

module type Predicate = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Make (A : Sigma) (P : Predicate) : sig
  type t
  type predicate = P.t
  type alpha = A.t
  type formula = (predicate, int) PaFormula.formula
  type config

  module Config : Struct.S with type predicate = predicate
                            and type t = config

  val pp : Format.formatter -> t -> unit
  val pp_ground : int -> Format.formatter -> t -> unit
  val pp_formula : Format.formatter -> formula -> unit

  (** [make sigma accept initial] creates a new PA with alphabet [sigma],
      accepting predicates [accept], and initial formula [initial].
      Initially, the transition rule is defined to be [delta(q,a) = false] for
      all [(q,a)].  Transitions can be added using [add_transition]. *)
  val make : alpha list ->
    predicate list ->
    formula ->
    t

  (** [add_transition pa q sigma phi] adds destructively updates the PA [pa]
      by adding the transition rule [delta(q,sigma) = phi \/ psi], where [psi]
      was the previous transition rule for [(q,sigma)]. *)
  val add_transition : t -> predicate -> alpha -> formula -> unit

  val alphabet : t -> alpha BatEnum.t

  (** [vocabulary pa] returns an enumeration of the predicate symbols used in
      [pa] along with their arity. *)
  val vocabulary : t -> (predicate * int) BatEnum.t

  val initial : t -> formula

  val negate : t -> t

  val intersect : t -> t -> t

  val union : t -> t -> t

  (** Compute the strongest post-condition of a formula under the transition
      relation corresponding to a given letter. *)
  val post : t -> formula -> alpha -> formula

  (** Compute the strongest post-condition of a formula under the transition
      relation corresponding to a given indexed letter. *)
  val concrete_post : t -> formula -> (alpha * int) -> formula

  val succs : t -> config -> (alpha * int) -> config BatEnum.t

  val pred : t -> config -> (alpha * int) -> config

  val empty : t -> ((alpha * int) list) option

  (** [bounded_empty pa bound] finds [Some] word which is accepted by [pa] and
      uses only indexed letters with index [<= bound]; [None] if there are no
      such words. *)
  val bounded_empty : t -> int -> ((alpha * int) list) option

  val bounded_invariant : t -> int -> formula -> ((alpha * int) list) option

  (** [accepting_formula pa phi] determines whether all models of [phi] are
      accepting configurations of [pa]. *)
  val accepting_formula : t -> formula -> bool
end