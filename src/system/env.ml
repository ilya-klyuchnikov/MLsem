open Parsing.Variable
open Types
open Types.Tvar

module Env = struct
  type t = TyScheme.t VarMap.t * TVarSet.t

  let empty = (VarMap.empty, TVarSet.empty)
  let is_empty (m,_) =  VarMap.is_empty m
  let singleton v t = (VarMap.singleton v t, TyScheme.fv t)
  let construct lst = (VarMap.of_seq (List.to_seq lst),
    List.map snd lst |> List.map TyScheme.fv |> TVarSet.union_many)

  let add v t (m,s) = (VarMap.add v t m, TVarSet.union s (TyScheme.fv t))

  let domain (m, _) = VarMap.bindings m |> List.map fst

  let bindings (m, _) = VarMap.bindings m

  let mem v (m, _) = (VarMap.mem v m)

  let reconstruct m = VarMap.bindings m |> construct

  let rm v (m, _) = VarMap.remove v m |> reconstruct

  let find v (m, _) = VarMap.find v m

  let filter f (m, _) = VarMap.filter f m |> reconstruct

  let rms vs t =
    let vs = VarSet.of_list vs in
    t |> filter (fun v _ -> VarSet.mem v vs |> not)

  let restrict vs t =
    let vs = VarSet.of_list vs in
    t |> filter (fun v _ -> VarSet.mem v vs)

  let leq (m1,_) (m2,_) =
    VarMap.for_all (fun v t ->
      VarMap.mem v m1 && TyScheme.leq (VarMap.find v m1) t
    ) m2

  let equiv env1 env2 = leq env1 env2 && leq env2 env1

  let pp fmt (m, _) =
    VarMap.bindings m
    |> List.iter (fun (v, ts) ->
      Format.fprintf fmt "%a: %a\n" Variable.pp v TyScheme.pp ts
    )

  let show = Format.asprintf "%a" pp

  let pp_filtered names fmt env =
    let env = filter (fun v _ -> List.mem (Variable.show v) names) env in
    pp fmt env

  let add v t e = assert (mem v e |> not) ; add v t e

  let tvars (_, s) = s

  let map f t =
    bindings t |> List.map (fun (v,t) -> (v,f t)) |> construct
end