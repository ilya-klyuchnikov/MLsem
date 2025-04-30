open Parsing
open Variable
open Types.Base
open Types.Tvar

type e =
| Abstract of typ
| Const of Ast.const
| Var of Variable.t
| Atom of atom
| Tag of tag * e
| Lambda of (typ list) * Variable.t * e
| Ite of e * typ * e * e
| App of e * e
| Tuple of e list
| Cons of e * e
| Projection of Ast.projection * e
| RecordUpdate of e * string * e option
| Let of (typ list) * Variable.t * e * e
| TypeConstr of e * typ
| TypeCoerce of e * typ list
[@@deriving show]

let fixpoint_var = Variable.create_gen (Some "__builtin_fixpoint")
let fixpoint_typ =
  let a = TVar.mk_poly None |> TVar.typ in
  let b = TVar.mk_poly None |> TVar.typ in
  let f = mk_arrow a b in
  let c = TVar.mk_poly None |> TVar.typ in
  let fc = cap f c in
  let arg = mk_arrow f fc in
  mk_arrow arg fc
let initial_env =
  Env.construct [(fixpoint_var, fixpoint_typ)]

let map f =
  let rec aux e =
    begin match e with
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Var v -> Var v
    | Atom a -> Atom a
    | Tag (t,e) -> Tag (t, aux e)
    | Lambda (ta, v, e) -> Lambda (ta, v, aux e)
    | Ite (e, t, e1, e2) -> Ite (aux e, t, aux e1, aux e2)
    | App (e1, e2) -> App (aux e1, aux e2)
    | Tuple es -> Tuple (List.map aux es)
    | Cons (e1, e2) -> Cons (aux e1, aux e2)
    | Projection (p, e) -> Projection (p, aux e)
    | RecordUpdate (e, str, eo) -> RecordUpdate (aux e, str, Option.map aux eo)
    | Let (ta, v, e1, e2) -> Let (ta, v, aux e1, aux e2)
    | TypeConstr (e, t) -> TypeConstr (aux e, t)
    | TypeCoerce (e, ts) -> TypeCoerce (e, ts)
    end
    |> f
  in
  aux

let fold f =
  let rec aux e =
    begin match e with
    | Abstract _ | Const _ | Var _ | Atom _ -> []
    | Tag (_, e) | Lambda (_,_, e) | Projection (_, e)
    | RecordUpdate (e, _, None) | TypeConstr (e,_) | TypeCoerce (e,_) -> [e]
    | Ite (e,_,e1,e2) -> [e ; e1 ; e2]
    | App (e1,e2) | Cons (e1,e2)
    | RecordUpdate (e1,_,Some e2) | Let (_,_,e1,e2) -> [e1 ; e2]
    | Tuple es -> es
    end
    |> List.map aux
    |> f e
  in
  aux

let fv' e accs =
  let acc = List.fold_left VarSet.union VarSet.empty accs in
  match e with
  | Abstract _ | Const _ | Atom _ | Tag _ | Ite _
  | App _ | Tuple _ | Cons _ | Projection _
  | RecordUpdate _ | TypeConstr _ | TypeCoerce _ -> acc
  | Var v -> VarSet.add v acc
  | Let (_, v, _, _) | Lambda (_, v, _) -> VarSet.remove v acc

let fv e = fold fv' e
