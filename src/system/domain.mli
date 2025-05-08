open Types.Tvar
open Env

type t
val empty : t
val add : REnv.t -> t -> t
val covers : TVarSet.t -> t -> REnv.t -> bool
val pp : Format.formatter -> t -> unit
