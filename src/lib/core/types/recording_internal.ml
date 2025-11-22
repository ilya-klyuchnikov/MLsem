
type tally_call = {
    vars1 : Sstt.Var.t list ;
    vars2 : Sstt.RowVar.t list ;
    mono1 : Sstt.Var.t list ;
    mono2 : Sstt.RowVar.t list ;
    constraints : (Sstt.Ty.t * Sstt.Ty.t) list
    }
let tally_calls = ref []
let recording = ref false
let record mono cs =
  if !recording then begin
    let vars1 (s,t) = Sstt.VarSet.union (Sstt.Ty.vars s) (Sstt.Ty.vars t) in
    let vars2 (s,t) = Sstt.RowVarSet.union (Sstt.Ty.row_vars s) (Sstt.Ty.row_vars t) in
    let tvars1 = List.fold_left
      (fun acc c -> Sstt.VarSet.union acc (vars1 c)) Sstt.VarSet.empty cs in
    let tvars2 = List.fold_left
      (fun acc c -> Sstt.RowVarSet.union acc (vars2 c)) Sstt.RowVarSet.empty cs in
    let order1 = Sstt.VarSet.elements tvars1 in
    let order2 = Sstt.RowVarSet.elements tvars2 in
    let mono1 = Sstt.VarSet.inter tvars1 (Sstt.MixVarSet.proj1 mono)
    |> Sstt.VarSet.elements in
    let mono2 = Sstt.RowVarSet.inter tvars2 (Sstt.MixVarSet.proj2 mono)
    |> Sstt.RowVarSet.elements in
    tally_calls := {vars1=order1;vars2=order2;mono1;mono2;constraints=cs}::!tally_calls
  end
