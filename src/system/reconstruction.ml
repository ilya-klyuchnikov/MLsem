open Annot
open Types.Base
open Types.Tvar
open Types
open Env
open Ast

type ('a,'b) result =
| Ok of 'a * typ
| Fail
| Subst of Subst.t list * 'b * 'b

let rec infer env annot (id, e) =
  let open IAnnot in
  let retry_with a = infer env a (id, e) in
  match e, annot with
  | _, A a -> Ok (a, Checker.typeof env a (id, e))
  | _, Untyp -> Fail
  | Abstract _, Infer -> retry_with (A Annot.AAbstract)
  | Const _, Infer -> retry_with (A Annot.AConst)
  | Var v, Infer ->
    let (tvs,_) = Env.find v env |> TyScheme.get in
    let s = refresh tvs in
    retry_with (A (Annot.AAx s))
  | Atom _, Infer -> retry_with (A Annot.AAtom)
  | Tag _, Infer -> retry_with (ATag Infer)
  | Tag (_, e'), ATag annot' ->
    begin match infer' env annot' e' with
    | Ok (annot', _) -> retry_with (A (Annot.ATag annot'))
    | Subst (ss,a1,a2) -> Subst (ss,ATag a1,ATag a2)
    | Fail -> Fail
    end
  | Lambda (tys,_,_), Infer ->
    let refresh_internal ty =
      let s = refresh (vars_internal ty) in
      Subst.apply s ty
    in
    let tys = List.map refresh_internal tys in
    let branches = List.map (fun ty -> ALambda (ty, Infer)) tys in
    retry_with (AInter branches)
  | Lambda (_,v,e'), ALambda (ty, annot') ->
    let env' = Env.add v (TyScheme.mk_mono ty) env in
    begin match infer' env' annot' e' with
    | Ok (annot', _) -> retry_with (A (Annot.ATag annot'))
    | Subst (ss,a1,a2) -> Subst (ss,ALambda (ty, a1),ALambda (ty, a2))
    | Fail -> Fail
    end
  | Ite _, Infer -> retry_with (AIte (Infer, BInfer, BInfer))
  | Ite (e0,tau,e1,e2), AIte (a0,a1,a2) ->
    begin match infer' env a0 e0 with
    | Fail -> Fail
    | Subst (ss,a,a') -> Subst (ss,AIte (a,a1,a2),AIte (a',a1,a2))
    | Ok (a0, s) ->
      begin match infer_b' env a1 e1 s tau with
      | Fail -> Fail
      | Subst (ss,a,a') -> Subst (ss,AIte(A a0,a,a2), AIte(A a0,a',a2))
      | Ok (a1, _) ->
        begin match infer_b' env a2 e2 s (neg tau) with
        | Fail -> Fail
        | Subst (ss,a,a') -> Subst (ss,AIte(A a0,B a1,a), AIte(A a0,B a1,a'))
        | Ok (a2, _) -> retry_with (A (Annot.AIte(a0,a1,a2)))
        end
      end
    end
  | App _, Infer -> retry_with (AApp (Infer, Infer))
  | App (e1, e2), AApp (a1,a2) ->
    begin match infer' env a1 e1 with
    | Fail -> Fail
    | Subst (ss,a,a') -> Subst (ss,AApp(a,a2),AApp(a',a2))
    | Ok (a1,t1) ->
      begin match infer' env a2 e2 with
      | Fail -> Fail
      | Subst (ss,a,a') -> Subst (ss,AApp(A a1,a),AApp(A a1,a'))
      | Ok (a2,t2) ->
        let tv = TVar.mk None in
        let arrow = mk_arrow t2 (TVar.typ tv) in
        let ss = tallying_with_result (TVar.user_vars ()) tv [(t1, arrow)] in
        Subst (ss, A (Annot.AApp(a1,a2)), Untyp)
      end
    end
  | _, _ -> failwith "TODO"
and infer' env annot e =
  let mono = TVarSet.union (Env.tvars env) (TVar.user_vars ()) in
  let subst_disjoint s =
    TVarSet.inter (Subst.dom s) mono |> TVarSet.is_empty
  in
  match infer env annot e with
  | Ok (a, ty) -> Ok (a, ty)
  | Fail -> Fail
  | Subst (ss, a1, a2) when List.for_all subst_disjoint ss ->
    let branches = ss |> List.map (fun s ->
      let annot = IAnnot.substitute s a1 in
      let tvs = TVarSet.diff (IAnnot.tvars annot) mono in
      IAnnot.substitute (refresh tvs) annot
      ) in
    let annot = IAnnot.AInter (branches@[a2]) in
    infer' env annot e
  | Subst (ss, a1, a2) -> Subst (ss, a1, a2)
and infer_b' env bannot e s tau =
  match bannot with
  | IAnnot.B b -> Ok (b, Checker.typeof_b env b e)
  | IAnnot.BInfer ->
    let ss = tallying (TVar.user_vars ()) [(s,neg tau)] in
    Subst (ss, IAnnot.B Annot.BSkip, IAnnot.BType Infer)
  | IAnnot.BType annot ->
    begin match infer' env annot e with
    | Ok (a, ty) -> Ok (Annot.BType a, ty)
    | Subst (ss,a1,a2) -> Subst (ss,IAnnot.BType a1,IAnnot.BType a2)
    | Fail -> Fail
    end

let infer env e =
  match infer env IAnnot.Infer e with
  | Fail -> None
  | Subst _ -> assert false
  | Ok (a,_) -> Some a
