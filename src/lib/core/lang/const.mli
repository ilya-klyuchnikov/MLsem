open Mlsem_types

type t =
| Unit | Nil
| Bool of bool
| Int of Z.t
| Float of float
| Char of char
| String of string

val typeof : t -> Ty.t

(** [is_approximated t] returns [false] if and only if [typeof t] is a singleton type
    capturing only [t]. *)
val is_approximated : t -> bool

val pp : Format.formatter -> t -> unit
