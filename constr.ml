open ListEx
open Util
open Types

let pollPVarId (op, coefs) =
  try Some (List.find ((<>) Id.const) (M.keys op))
  with Not_found ->
    tryPick (fun x ->
      try Some (List.find ((<>) Id.const) (M.keys x))
      with Not_found -> None) (M.values coefs)

let mergeConstrs pvarIds (ids, puf, constrs as sol) =
  let constrIds =
    List.map (fun x ->
      List.fold_left (fun i y -> if x <= y then i else i + 1) 0 ids |>
      Puf.find puf) pvarIds |>
    sort_distinct in

  match constrIds with
    | [] -> (-1), sol
    | baseId::rest ->
      let (constr, constrs) =
        List.fold_left (fun (constr, constrs) x ->
          (MI.find x constrs) :: constr,
          MI.remove x constrs) ([], constrs) constrIds in
      let constr = List.reduce (&&&) constr in
      let puf = List.fold_left (
        fun puf x -> Puf.union puf baseId x) puf rest in

      (* TODO: Will be removed in future when compiling into a module. *)
      let newId = Puf.find puf baseId in

      let constrs = MI.add newId constr constrs in
      newId, (ids, puf, constrs)

let merge (i1, p1, c1) (i2, p2, c2) =
  let i1 = mapi (fun i x -> x, i, true) i1 in
  let i2 = mapi (fun i x -> x, i, false) i2 in
  let i = List.fast_sort compare (i1 @ i2) in

  let _, m1, m2 = List.fold_left (fun (i, m1, m2) (_, t, i1flag) -> i + 1,
    (if i1flag then MI.add t i m1 else m1),
    (if not i1flag then MI.add t i m2 else m2)) (0, MI.empty, MI.empty) i in
  let i = List.map (fun (x, _, _) -> x) i in

  let constructPuf i p m =
    repeat (fun x puf ->
      let x' = MI.find x m in
      let y' = MI.find (Puf.find p x) m in
      Puf.union puf x' y') (List.length i) in
  let p =
    Puf.create (List.length i) |>
    constructPuf i1 p1 m1 |>
    constructPuf i2 p2 m2 in

  let moveConstr m = MI.fold (fun k -> MI.add (MI.find k m |> Puf.find p)) in
  let c =
    MI.empty |>
    moveConstr m1 c1 |>
    moveConstr m2 c2 in

  i, p, c

let solve (_, _, constrs) =
  MI.fold (fun _ constr m ->
    match Z3interface.integer_programming constr with
      | Some sol -> M.simpleMerge sol m
      | None -> raise Not_found) constrs M.empty
