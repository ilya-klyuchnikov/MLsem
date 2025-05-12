open Annot

type t
val empty : t
val add : IAnnot.coverage -> t -> t
val covers : t -> IAnnot.coverage -> bool
val pp : Format.formatter -> t -> unit
