open Tvar

type t = TVarSet.t * Gradual.t
let mk tvs ty =
  let tvs = TVarSet.inter tvs (Gradual.fv ty) in
  (tvs, ty)
let mk_poly_except mono ty =
  let tvs = TVarSet.diff (Gradual.fv ty) mono in
  (tvs, ty)
let mk_mono ty = mk TVarSet.empty ty
let mk_poly ty = mk_poly_except TVarSet.empty ty
let get (tvs, ty) = (tvs, ty)
let get_fresh (tvs, ty) =
  let mono = TVarSet.diff (Gradual.fv ty) tvs in
  let s = TVOp.refresh tvs in
  mono, Gradual.substitute s ty
let fv (tvs, ty) = TVarSet.diff (Gradual.fv ty) tvs

let substitute s (tvs, ty) =
  let s = Subst.remove s tvs in
  (tvs, Gradual.substitute s ty)

let leq (tvs1,ty1) (tvs2,ty2) =
  TVarSet.subset tvs2 tvs1 &&
  Gradual.leq ty1 ty2
let equiv t1 t2 = leq t1 t2 && leq t2 t1
let bot_instance (tvs,t) =
  let mono = TVarSet.diff (Gradual.fv t) tvs in
  let t = Gradual.map (TVOp.bot_instance mono) t in
  mk tvs t
let top_instance (tvs,t) =
  let mono = TVarSet.diff (Gradual.fv t) tvs in
  let t = Gradual.map (TVOp.top_instance mono) t in
  mk tvs t
let simplify (tvs,ty) = (tvs, Gradual.simplify ty)
let normalize (tvs,ty) = (tvs, Gradual.normalize ty)
let norm_and_simpl ts = ts |> normalize |> simplify
let pp fmt (tvs, ty) =
  if TVarSet.is_empty tvs
  then Format.fprintf fmt "%a" Gradual.pp ty
  else
    Format.fprintf fmt "∀%a. %a"
      (Utils.pp_seq TVar.pp ",") (TVarSet.destruct tvs) Gradual.pp ty
let pp_short fmt (tvs, ty) =
  let s = TVOp.shorten_names tvs in
  let ty = Gradual.substitute s ty in
  let tvs = TVarSet.destruct tvs
    |> List.map (fun v -> Subst.find s v |> TVOp.vars |> TVarSet.destruct |> List.hd)
    |> TVarSet.construct
  in
  pp fmt (tvs,ty)
