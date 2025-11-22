open Mlsem_common
open Mlsem_types
open Annot

module Domain = struct
  type t = IAnnot.coverage list
  [@@deriving show]

  let transform_abstract =
    let aux (_, dnf) =
      let has_no_empty lst =
        List.for_all Ty.non_empty lst
      in
      let has_no_empty (ps,_) =
        List.for_all has_no_empty ps
      in
      List.filter has_no_empty dnf
    in
    Abstract.transform aux

  let empty = []
  let add c t = c::t

  let env_to_typ ?(normalize=false) renv =
    let f = if normalize then transform_abstract else Fun.id in
    let bindings = renv
      |> REnv.bindings |> List.map
        (fun (v, ty) -> (Variable.get_unique_name v, (f ty, false)))
    in
    Record.mk_open bindings

  let more_specific res1 res2 =
    match res1, res2 with
    | _, None -> true
    | None, _ -> false
    | Some (eid1,ty1), Some (eid2,ty2) when eid1=eid2 ->
      Ty.leq ty1 ty2
    | Some _, Some _ -> false

  let covers t (res,renv) =
    let renvs = t
      |> List.filter (fun (res',_) -> more_specific res' res)
      |> List.map (fun (_,renv) -> renv)
    in
    let a = renvs |> List.map env_to_typ |> Ty.disj in
    let b = env_to_typ ~normalize:(!Config.no_empty_param) renv in
    Ty.leq b a
end

module TVCache = struct
  type t = { c1: (Eid.t * TVar.t, TVar.t) Hashtbl.t ;
             c2: (Eid.t * RVar.t, RVar.t) Hashtbl.t }

  let empty () = { c1 = Hashtbl.create 100 ; c2 = Hashtbl.create 100 }

  let get1 t eid tv =
    match Hashtbl.find_opt t.c1 (eid, tv) with
    | Some tv -> tv
    | None ->
      let tv' = TVar.mk KInfer None in
      Hashtbl.replace t.c1 (eid, tv) tv' ; tv'

  let get2 t eid rv =
    match Hashtbl.find_opt t.c2 (eid, rv) with
    | Some rv -> rv
    | None ->
      let rv' = RVar.mk KInfer None in
      Hashtbl.replace t.c2 (eid, rv) rv' ; rv'

  let get' t eid tvs =
    let tvs, rvs = MVarSet.elements tvs in
    let tvs = List.map (fun tv -> tv, get1 t eid tv |> TVar.typ) tvs in
    let rvs = List.map (fun rv -> rv, get2 t eid rv |> Row.id_for) rvs in
    Subst.of_list tvs rvs
  
  let res_tvar = TVar.mk KTemporary None
end