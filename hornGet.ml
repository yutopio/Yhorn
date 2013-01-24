open Util
open Types

let pexprUnify (ids, puf, constrs as sol) a b c d e =
  (* Test wether the constraint is satisfiable or not. *)
  let test x = not (Z3interface.integer_programming x = None) in

  (* Extract one parameter each from two parameterized expression. *)
  List.map (
    tryPick (fun (op, coefs) ->
      tryPick (
        tryPick (fun x ->
          if x = "" then None
          else Some (int_of_string (String.sub x 1 (String.length x - 1)))))
        ((M.keys op) :: (List.map M.keys (M.values coefs)))) |-
    (function
      | Some x ->
        List.fold_left (fun i y -> if x < y then i else i + 1) 0 ids |>
        Puf.find puf
      | None -> -1)) [b;d] |>

  (function
    | [-1;-1] -> `A
    | [-1;gx]
    | [gx;-1] -> `B gx
    | [gb;gd] -> if gb = gd then `B gb else `C (gb, gd)
    | _ -> assert false) |>

  (function
    | `A -> Some sol
    | `B gx ->
      let add = Unify.generatePexprUnifyConstr ~nl:true (List.hd b) (List.hd d) in
      let pgx = Puf.find puf gx in
      let constr = add &&& MI.find pgx constrs in
      if test constr then
        Some (ids, puf, MI.add pgx constr constrs)
      else None
    | `C (gb, gd) ->
      let add = Unify.generatePexprUnifyConstr ~nl:true (List.hd b) (List.hd d) in
      let (constr, constrs) =
        List.map (Puf.find puf) [gb;gd] |>
        List.fold_left (fun (constr, constrs) x ->
          constr &&& (MI.find x constrs),
          MI.remove x constrs) (add, constrs) in
      if test constr then
        let puf = Puf.union puf gb gd in
        let constrs = MI.add (Puf.find puf gb) constr constrs in
        Some (ids, puf, constrs)
      else None)

let pexprListUnify original a b c d e =
  let b, d = List.hd b, List.hd d in
  match List.fold_left (fun l x ->
    let ret =
      Combine.lists x pexprUnify b d |>
      List.split |> snd in
    ret @ l) [] original with
    | [] -> None
    | x -> Some x

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

  (* Try to unify nf1 and nf2. Randomly choose the first constraint if
     succeeds. *)
  let ret = Combine.lists [constr] pexprListUnify nf1 nf2 in
  let choices = List.flatten (List.map snd ret) in
  let length = List.length choices in
  if length > 0 then
    Some (preds, List.hd choices)
  else
    None

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
      | Some x -> (false, solution)
      | None -> (true, solution)
    ) (false, solution) |> snd

let trySimplify p (preds, constr) =
  (* Specified predicate variables must exist. *)
  let param, nf = assert (M.mem p preds); M.find p preds in

  (* Try to simplify nf. Randomly choose the first constraint if succeeds. *)
  let choices = Combine.elements [constr] pexprListUnify nf 1 in
  if List.length choices > 0 then
    let k, v = List.hd choices in
    let preds = M.add p (param, List.map List.hd k) preds in
    Some (preds, List.hd v)
  else
    None

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

let getSolution (pexprs, (_, _, constrs)) =
  let sol = MI.fold (fun _ constr m ->
    match Z3interface.integer_programming constr with
      | Some sol -> M.simpleMerge sol m
      | None -> raise Not_found) constrs M.empty in

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
