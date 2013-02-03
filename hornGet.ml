open Util
open Types

let unify nfs constr =
  (* Extract one parameter each from two parameterized expression. *)
  let pvarIds =
    List.flatten (List.flatten nfs) |>
    List.map Constr.pollPVarId |>
    List.filter ((<>) None) |>
    List.map (fun (Some x) -> x) in

  let newId, (ids, puf, constrs) = Constr.mergeConstrs pvarIds constr in
  match newId with
    | (-1) -> Some constr
    | _ ->
      (* TODO: Will be replaced not to handle constraint set directly. *)
      let constr = MI.find (Puf.find puf newId) constrs in
      try
        match Template.unify Unify.generatePexprUnifyConstr
          constr ~maxSize:5 nfs with
          | Some (_, additional) ->
            let constr = constr &&& additional in
            let constrs = MI.add (Puf.find puf newId) constr constrs in
            Some (ids, puf, constrs)
          | None -> None
      with Not_found -> None

let tryUnify (p1, p2) (preds, constr) =
  (* Specified predicate variables must exist. *)
  let [(param1, nf1);(param2, nf2)] = List.map (fun p ->
    assert (M.mem p preds); M.find p preds) [p1;p2] in

  (* Parameters for the predicate variable must match. *)
  assert (List.length param1 = List.length param2);
  let preds, nf2 =
    if param1 = param2 then preds, nf2 else
      let m = ref (listFold2 (fun m a b -> M.add a b m)
        M.empty param1 param2) in
      let nf2 = List.map (List.map (renamePexpr m)) nf2 in
      M.add p2 (param1, nf2) preds, nf2 in

  (* Try to unify nf1 and nf2. *)
  match unify [nf1;nf2] constr with
    | Some constr -> Some (M.add p2 (param1, nf1) preds, constr)
    | None -> None

let tryUnify unify solution =
  (* Use Jean-Christophe Filliâtre's Union-Find tree implementation. *)
  let m = ref M.empty in
  let puf = ref (Puf.create (2 * List.length unify)) in
  let get x =
    if M.mem x !m then
      M.find x !m
    else (
      let v = M.cardinal !m in
      m := M.add x v !m; v) in
  let union x y = puf := Puf.union !puf (get x) (get y) in
  let find x = Puf.find !puf (get x) in

  (* Reduce merge groups to meaningful ones. *)
  List.filter (fun (a, b) ->
    let ret = (find a) <> (find b) in
    if ret then union a b;
    ret) unify |>

  List.fold_left (fun (fail, solution) pair ->
  if fail then (true, solution) else
    match tryUnify pair solution with
      | Some x -> (false, x)
      | None -> (true, solution)
    ) (false, solution) |> snd

let assignParameters assign (op, expr) =
  (M.fold (fun k v o -> if v <> 0 && M.findDefault EQ k op = LTE then
      (assert (v > 0); LTE) else o) assign EQ),
  (M.map (fun v -> M.fold (fun k v -> (+) ((
    M.findDefault 1 k assign) * v)) v 0) expr)

let simplifyCNF =
  let simplifyDF =
    List.fold_left (fun (tautology, exprs) (op, coef as expr) ->
      if tautology || M.cardinal coef = 0 then true, []
      else if M.cardinal coef > 1 || not (M.mem "" coef) then
        false, expr :: exprs
      else
        let c = M.find "" coef in
        (match op with
          | EQ -> c = 0
          | LTE -> c <= 0), exprs) (false, []) in

  List.fold_left (fun (contradiction, clauses) clause ->
    let tautology, exprs = simplifyDF clause in
    if tautology then contradiction, clauses
    else if contradiction || List.length exprs = 0 then true, []
    else false, exprs :: clauses) (false, [])

let getSolution (pexprs, constr) =
  let sol = Constr.solve constr in

  (* Construct one interpolant *)
  M.map (fun (params, cnf) ->
    let cnf = List.map (List.map (assignParameters sol)) cnf in
    let cntrdct, clauses = simplifyCNF cnf in
    let formula =
      if cntrdct then Expr (EQ, M.add "" 1 M.empty)
      else if List.length clauses = 0 then Expr (EQ, M.empty)
      else convertToFormula true clauses in
    params, formula) pexprs

let getSolution a (clauses, (b, c)) =
  let sol = tryUnify a (b, c) |> getSolution in

  (* DEBUG: Solution verification. *)
  print_endline "\nVerification";
  assert (List.for_all (Z3interface.check_clause sol) clauses);
  print_newline ();

  sol
