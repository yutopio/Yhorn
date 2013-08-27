open Expr
open Formula
open MTypes
open Types
open Util

let interpolate (t1, t2) =
  let fvs = S.union (Types.fvs t1) (Types.fvs t2) in
  let binder = S.fold (fun x l -> x :: l) fvs [] in
  let pid = Id.create () in
  let p = PredVar (pid, binder) in

  let clauses =
    [Term (LinearExpr t1), p;
     And [Term p; Term (LinearExpr t2)], LinearExpr (Term (GT, M.empty))] in
  let args, ret = Horn.solve clauses |> M.find pid in

  let createRename = List.fold_left2 (fun m k v -> M.add k v m) M.empty in
  let rename = ref (createRename args binder) in
  Formula.map (renameExpr rename) ret
