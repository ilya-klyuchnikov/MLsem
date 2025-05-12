open Types.Base
open Parsing.Variable
open Env
open Annot

type t = IAnnot.coverage list
[@@deriving show]

let empty = []
let add c t = c::t

let env_to_typ renv =
  let bindings = renv
    |> REnv.bindings |> List.map
      (fun (v, ty) -> (Variable.get_unique_name v, (false, ty)))
  in
  mk_record true bindings

let more_specific res1 res2 =
  match res1, res2 with
  | _, None -> true
  | None, _ -> false
  | Some (eid1,ty1), Some (eid2,ty2) when eid1=eid2 ->
    subtype ty1 ty2
  | Some _, Some _ -> false

let covers t (res,renv) =
  let renvs = t
    |> List.filter (fun (res',_) -> more_specific res' res)
    |> List.map (fun (_,renv) -> renv)
  in
  let a = renvs |> List.map env_to_typ |> disj in
  let b = env_to_typ renv in
  subtype b a
