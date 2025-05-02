open Env
open Annot

val infer : Env.t -> Ast.t -> Annot.t option
