open Base
open Tvar

type t = TVarSet.t * typ
let mk tvs ty =
  let tvs = TVarSet.inter tvs (vars ty) in
  (tvs, ty)
let mk_mono ty = mk TVarSet.empty ty
let mk_poly ty = mk (vars ty) ty
let get (tvs, ty) = (tvs, ty)
let fv (tvs, ty) = TVarSet.diff (vars ty) tvs
let leq (tvs1,ty1) (tvs2,ty2) =
  TVarSet.subset tvs2 tvs1 &&
  subtype ty1 ty2
let equiv t1 t2 = leq t1 t2 && leq t2 t1
let leq_inst (tvs1,ty1) (_,ty2) =
  let s = refresh tvs1 in
  let mono = TVarSet.union (vars ty1) (vars ty2) in
  let ty1 = Subst.apply s ty1 in
  test_tallying mono [ty1,ty2]
let equiv_inst t1 t2 = leq_inst t1 t2 && leq_inst t2 t1
let pp fmt (tvs, ty) =
  Format.fprintf fmt "∀%a.%a"
    (Utils.pp_list TVar.pp) (TVarSet.destruct tvs) pp_typ ty
let pp_short fmt (tvs, ty) =
  let s = shorten_names tvs in
  let ty = Subst.apply s ty in
  let tvs = TVarSet.destruct tvs
    |> List.map TVar.typ
    |> List.map (Subst.apply s) in
  Format.fprintf fmt "∀%a.%a"
    (Utils.pp_list pp_typ) tvs pp_typ ty
