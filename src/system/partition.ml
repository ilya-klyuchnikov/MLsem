open Ast
open Env
open Types
open Types.Tvar

let constr env renv e =
  match e with
  | Abstract ty -> [], ty
  | Const c -> [], Checker.typeof_const c
  | Var v when REnv.mem v renv -> [], REnv.find v renv
  | Var v when Env.mem v env ->
    let (tvs,t) = Env.find v env |> TyScheme.get in
    let s = refresh tvs in
    [], Subst.apply s t
  | Var _ -> assert false
  | _ -> failwith "TODO"