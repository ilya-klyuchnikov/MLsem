open Mlsem_common
open Mlsem_types
module MVariable = Mlsem_lang.MVariable

module type Main = sig
  module P : PAst.ParserExt

  module NameMap : Map.S with type key=string
  type message = Mlsem_system.Analyzer.severity * Position.t * string * string option
  type treat_result =
  | TSuccess of (Variable.t * string) list * message list * float
  | TDone
  | TFailure of Variable.t option * Position.t * string * string option * float

  type envs = P.B.benv * Variable.t NameMap.t * Ty.t list VarMap.t * Env.t * PEnv.t
  val treat : envs -> 'a Position.located * P.E.element -> envs * treat_result
  val treat_sig : envs -> 'a Position.located * P.E.element -> envs * treat_result
  val treat_def : envs -> 'a Position.located * P.E.element -> envs * treat_result
  val treat_all_sigs : envs -> ('a Position.located * P.E.element) list -> envs * treat_result

  val initial_envs : envs
  val initial_senv : Ty.t list VarMap.t
  val initial_benv : P.B.benv
  val initial_penv : PEnv.t

  type parsing_result =
  | PSuccess of P.E.program
  | PFailure of Position.t * string

  val parse : [< `File of string | `String of string ] -> parsing_result
end

module Make(P:PAst.ParserExt) : Main with module P=P

module PNoExt : PAst.ParserExt
module NoExt : Main with module P=PNoExt
