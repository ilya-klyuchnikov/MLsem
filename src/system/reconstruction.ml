open Annot
open Types.Base
open Types.Tvar
open Types
open Env
open Ast

type result =
| Ok of Annot.t * typ
| Fail
(* | Subst of Subst.t * IAnnot.t * IAnnot.t *)

let rec infer env annot (id, e) =
  let open IAnnot in
  match e, annot with
  | _, A a -> Ok (a, Checker.typeof env a (id, e))
  | _, Untyp -> Fail
  | Abstract _, Infer -> infer env (A Annot.AAbstract) (id, e)
  | Const _, Infer -> infer env (A Annot.AConst) (id, e)
  | Var v, Infer ->
    let (tvs,_) = Env.find v env |> TyScheme.get in
    let s = refresh tvs in
    infer env (A (Annot.AAx s)) (id, e)
  | Atom _, Infer -> infer env (A Annot.AAtom) (id, e)
  | _, _ -> failwith "TODO"

let infer env e =
  match infer env IAnnot.Infer e with
  | Fail -> None
  (* | Subst _ -> assert false *)
  | Ok (a,_) -> Some a
