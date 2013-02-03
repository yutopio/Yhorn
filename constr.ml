open Types
open Util

let pollPVarId (op, coefs) =
  let getId = function
    | "" -> None
    | x -> Some (int_of_string (String.sub x 1 (String.length x - 1))) in
  match tryPick getId (M.keys op) with
    | Some x -> Some x
    | None -> tryPick (M.keys |- tryPick getId) (M.values coefs)

let mergeConstrs pvarIds (ids, puf, constrs as sol) =
  let constrIds =
    List.map (fun x ->
      List.fold_left (fun i y -> if x < y then i else i + 1) 0 ids |>
      Puf.find puf) pvarIds |>
    sort_distinct in

  match constrIds with
    | [] -> (-1), sol
    | baseId::rest ->
      let (constr, constrs) =
        List.fold_left (fun (constr, constrs) x ->
          (MI.find x constrs) :: constr,
          MI.remove x constrs) ([], constrs) constrIds in
      let constr = reduce (&&&) constr in
      let puf = List.fold_left (
        fun puf x -> Puf.union puf baseId x) puf rest in

      (* TODO: Will be removed in future when compiling into a module. *)
      let newId = Puf.find puf baseId in

      let constrs = MI.add newId constr constrs in
      newId, (ids, puf, constrs)

let solve (_, _, constrs) =
  MI.fold (fun _ constr m ->
    match Z3interface.integer_programming constr with
      | Some sol -> M.simpleMerge sol m
      | None -> raise Not_found) constrs M.empty
