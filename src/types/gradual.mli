open Base
open Tvar

module GTy : sig
    type t
    val dyn: t
    val static: t
    val top: t
    val bot : t
    val mk: typ -> bool -> t
    val mk_static: typ -> t
    val dyn_comp: t -> bool
    val static_comp: t -> typ
    val components : t -> typ * bool
    val cap: t -> t -> t
    val cup: t -> t -> t
    val conj : t list -> t
    val disj : t list -> t

    val fv : t -> TVarSet.t
    val substitute : Subst.t -> t -> t
    val map_dyn : typ -> t -> typ

    val is_top : t -> bool
    val is_bot : t -> bool
    val leq : t -> t -> bool
    val equiv : t -> t -> bool
    val leq_static : t -> t -> bool
    val equiv_static : t -> t -> bool

    val simplify : t -> t
    val normalize : t -> t
    val map : (typ -> typ) -> t -> t
    val map2 : (typ -> typ -> typ) -> t -> t -> t
    val map3 : (typ -> typ -> typ -> typ) -> t -> t -> t -> t
    val mapl : (typ list -> typ) -> t list -> t

    val pp : Format.formatter -> t -> unit
end
