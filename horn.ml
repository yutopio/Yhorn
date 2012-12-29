open Util
open Types

let assignParameters assign (op, expr) =
  (M.fold (fun k v o -> if v <> 0 && M.findDefault EQ k op = LTE then
      (assert (v > 0); LTE) else o) assign EQ),
  (M.map (fun v -> M.fold (fun k v -> (+) ((
    M.findDefault 1 k assign) * v)) v 0) expr)

let generatePexprMergeConstr (op1, coef1) (op2, coef2) =
  (* Consider all variables are present in both *)
  let vars = [] |>
    M.fold (fun k v r -> k :: r) coef1 |>
    M.fold (fun k v r -> k :: r) coef2 |>
    distinct in

  (* Generate auxiliary variables. *)
  let q1, q2 =
    let f () = "q" ^ string_of_int (new_id ()) in
    f (), f () in
  let c3 = Expr(GT , M.add q1 1 M.empty) in (* q1  > 0 *)
  let c1 = Expr(NEQ, M.add q2 1 M.empty) in (* q2 != 0 *)
  let c2 = Expr(NEQ, M.add q2 1 M.empty) in (* q2  > 0 *)

  (* Coefficients of both interpolants must be the same *)
  let mul v coef = M.fold (fun k -> M.add (k ^ "*" ^ v)) coef M.empty in
  let c3 = List.fold_left (fun r k ->
    let [v1;v2] = List.map (M.findDefault M.empty k) [coef1;coef2] in
    (Expr(EQ, (mul q1 v1) -- (mul q2 v2)) :: r)) [c3] vars in

  (* Check weight variables those for making an interpolant LTE. *)
  let f x =
    let p = M.fold (fun k v p -> if v = LTE then k :: p else p) x [] in
    let eq = List.fold_left (fun c x ->
      (Expr (EQ, M.add x 1 M.empty)) :: c) [] p in
    (p, eq) in
  let (p1lte, i1eq), (p2lte, i2eq) = (f op1), (f op2) in

  let [c3;i1eq;i2eq] = List.map (fun x -> And x) [c3;i1eq;i2eq] in

  (* Constraint for making both interpolant the same operator. *)
  match p1lte, p2lte with
    | [], [] -> c1 &&& c3
    | _, [] -> c1 &&& c3 &&& i1eq
    | [], _ -> c1 &&& c3 &&& i2eq
    | _ -> c3 &&& (i1eq <=> i2eq) &&& (i1eq ==> c1) &&& ((!!! i1eq) ==> c2)

let buildGraph clauses =
  (* TODO: Handle props without assumptions, and props that imply nothing. *)
  let predVertices = ref M.empty in
  List.fold_left (fun g (lh, rh) ->
    (* Rename all variables to internal names for avoiding name collision. *)
    let nameMap = ref M.empty in

    let src = match rh with
      | PredVar (p, l) ->
        if M.mem p !predVertices then (
          (* If the predicate `p` already exists, build a renaming map so that
             the current horn clause become consistent with already built part
             of the graph. *)
          let src = M.find p !predVertices in
          let PredVar (_, binders) = G.V.label src in
          nameMap := listFold2 (fun m a b -> M.add a b m) M.empty l binders;
          src
        ) else (
          (* Otherwise, create a new predicate vertex and remember it. *)
          let src = G.V.create (PredVar (p, (renameList nameMap l))) in
          predVertices := M.add p src !predVertices;
          src)
      | LinearExpr e ->
        (* If the right-hand of the horn clause is a linear expression, there
           are no special things to consider. Just create a new vertex. *)
        G.V.create (LinearExpr (mapFormula (renameExpr nameMap) e)) in

    (* Following statement has no effect if the vertex `src` is in the graph. *)
    let g = G.add_vertex g src in

    let (pvars, la) = lh in
    let g, dsts = List.fold_left (fun (g, dsts) (p, args) ->
      (* Get (or create if needed) the predicate variable vertex and its binder.
         We will relate this vertex from newly-created predicate variable
         vertices that corrensponds to the application of such predicates. The
         edge will carry binding information. *)
      let dst, binders =
        if M.mem p !predVertices then
          (* If exists, extract binders from the vertex label. *)
          let dst = M.find p !predVertices in
          let PredVar (_, binders) = G.V.label dst in
          dst, binders
        else (
          (* If not yet exists, create a new vertex with a fresh binder. *)
          let binders = repeat (fun _ l -> (new_name ()) :: l)
            (List.length args) [] in
          let dst = G.V.create (PredVar (p, binders)) in
          predVertices := M.add p dst !predVertices;
          dst, binders) in

      (* Create a vertex which corresponds to the application to the predicate
         variable. *)
      let args = renameList nameMap args in
      let src = G.V.create (PredVar (p, args)) in

      (* Build a name mapping between referred predicate variable (appears on
         the right-hand of Horn clause) and referring one (on the left-hand). *)
      let renames = listFold2 (fun l a b -> (a, b) :: l) [] binders args in

      (* Add a edge between origin *)
      let g = G.add_edge_e g (G.E.create src (Some renames) dst) in
      g, (src :: dsts)
    ) (g, []) pvars in

    (* If a linear expression exists on the left-hand, create a corresponding
       vertex. *)
    let dsts = match la with
      | None -> dsts
      | Some x ->
        (G.V.create (LinearExpr (mapFormula (renameExpr nameMap) x))) :: dsts in

    (* Add edges between all left-hand terms and right-hand term. *)
    List.fold_left (fun g dst -> G.add_edge g src dst) g dsts
  ) G.empty clauses

let top = Expr (EQ, M.empty)

let flattenGraph g =
  G.fold_vertex (fun v l ->
    (* TODO: This algorithm cannot find the self-looping predicate variable node
       which has no children. *)
    if G.in_degree g v = 0 then v :: l else l) g [] |>

  (* Traverse the graph from given starting points to make trees. *)
  List.map (fun v ->
    (* Keep track of linear expressions with giving a unique ID. *)
    let laGroups = ref MI.empty in

    (* After splitting a graph into a tree, one predicate variable may appear
       multiple times in the tree. Thus, each appearance will be remembered by
       the ID. `predMap` tracks the mapping between such predicate ID and linear
       expression IDs appearing above the predicate. `predCopies` remembers the
       correspondance between the original name of predicate variable and
       predicate IDs. *)
    let predMap = ref MI.empty in
    let predCopies = ref M.empty in

    let rec f v nameMap =
      let renamedLabel v = renameHornTerm nameMap (G.V.label v) in

      let (u's, la) = G.fold_succ (fun u (u's, la) ->
        match renamedLabel u with
          | PredVar (p, args) ->
            (* This prevents `nameMap` to be shared over all DFS. *)
            let nameMap = ref (!nameMap) in

            (* Every application vertex must have exactly one parent. *)
            let es = G.fold_succ_e (fun e l -> e :: l) g u [] in
            let e = assert (List.length es = 1); List.hd es in

            (* Bindings of predicate variables are converted to linear equations
               so that it can be treated easy. Note that the binder and argument
               will have different names even if they have the same one before
               conversion.*)
            let dst, (Some bindings) = (G.E.dst e), (G.E.label e) in
            let constr = List.fold_left (fun constr (x, y) ->
              let x' = new_name () in
              let y' = renameVar nameMap y in
              nameMap := M.add x x' !nameMap;
              Expr (EQ, M.add x' 1 (M.add y' (-1) M.empty)) :: constr)
              [] bindings in

            (* Traverse children first to unify predicate variable nodes. *)
            let u' = f dst nameMap in
            (u' @ u's), (if constr = [] then la else la &&& And(constr))

          | LinearExpr e ->
            (* NOTE: Linear expressions must appear only once. *)
            u's, (la &&& e)
      ) g v ([], top) in

      let registerLa la =
        let key = MI.cardinal !laGroups in
        laGroups := MI.add key la !laGroups; key in

      match (renamedLabel v) with
        | PredVar (p, param) ->
          let pid = (new_id ()) in
          let u's = if la <> top then (registerLa la) :: u's else u's in
          predMap := MI.add pid (param, u's) !predMap;
          predCopies := M.addDefault [] (fun l x -> x :: l) p pid !predCopies;
          u's

        | LinearExpr e ->
          (* NOTE: The vertex 'v' must be the root of traversal. *)
          registerLa (if la <> top then la &&& (!!! e) else !!! e);
          [] (* Doesn't care on what to return. *)
    in
    ignore(f v (ref M.empty));
    !laGroups, !predMap, !predCopies)

let getSolution (pexprs, (_, _, constrs)) =
  (* DEBUG: Dump Z3 problem.
  print_endline ("Z3 problem: " ^ (printFormula printExpr constr)); *)

  let sol = MI.fold (fun _ constr m ->
    match Z3interface.integer_programming constr with
      | Some sol -> M.simpleMerge sol m
      | None -> raise Not_found) constrs M.empty in

  (* DEBUG: Dump Z3 solution.
  print_endline ("Z3 solution: [" ^ (String.concat ", " (
    M.fold (fun k v l -> (k ^ "=" ^ (string_of_int v))::l) sol [])) ^ "]\n"); *)

  (* Construct one interpolant *)
  M.map (fun (params, cnf) ->
    let x = convertToFormula true cnf in
    params, (mapFormula (assignParameters sol) x)) pexprs

let merge (sols, predMap, predCopies) =
  let predSols, maxIds, constrs = List.fold_left (fun (predSolsByPred, maxIds, constrs)
    (dnfChoice, predSolsByDnf, maxId, constr) ->
      MI.fold (fun pid ->
        MI.addDefault ([], MIL.empty) (fun (_, m) (param, pexpr) -> param,
          let groupKey =
            (MI.fold (fun k v l ->
              if List.mem k (MI.find pid predMap) then l
              else (k, v) :: l) dnfChoice []) |>
            (List.sort comparePair) |>
            List.split |> snd in
          MIL.addDefault [] (fun l x -> x :: l) groupKey pexpr m
        ) pid) predSolsByDnf predSolsByPred,
      maxId :: maxIds,
      MI.add (List.length maxIds) constr constrs
  ) (MI.empty, [], MI.empty) sols in

  let predSols = MI.map (fun (param, pexpr) -> param,
    MIL.fold (fun _ v l -> v :: l) pexpr []) predSols in

  (M.map (fun x ->
    reduce (fun (p1, e1) (p2, e2) -> assert (p1 = p2); (p1, e1 @ e2))
      (List.map (fun x -> MI.find x predSols) x)) predCopies),
  (List.rev maxIds),
  constrs

let solveTree (laGroups, predMap, predCopies) =
  let (laIds, laDnfs) = laGroups |>
      MI.add (-1) (Expr (LTE, M.add "" (-1) M.empty)) |>
      MI.map (
        mapFormula normalizeExpr |-
        splitNegation |-
        convertToNF false) |>
      MI.bindings |> List.split in

  (* Give choice IDs to each conjunctions inside DNF. At the same time, filter
     the inserted tautologies 0=0 during the process. *)
  let laDnfs = List.map (mapi (fun i x -> (i,
    List.filter (fun x -> x <> (EQ, M.empty)) x))) laDnfs in

  List.map (fun assigns ->
    (* Give IDs and flatten. *)
    let dnfChoice, exprs = listFold2 (fun (s, t) x (z, y) ->
      (MI.add x z s), ((List.map (fun z -> (x, z)) y) @ t))
      (MI.empty, []) laIds assigns in

    (* Build the coefficient mapping for all assigned expressions and check
       the operator of each expression. *)
    let coefs, constr, ops, exprGroup =
      List.fold_left (fun (coefs, constr, ops, exprGroup) (gid, (op, coef)) ->
        let exprId = "p" ^ (string_of_int (new_id ())) in

        (* DEBUG: *)
        print_endline ((string_of_int gid) ^ "\t" ^ exprId ^ "\t" ^
          (printExpr (op, coef)));

        (* Building an coefficient mapping in terms of variables *)
        (M.fold (fun k v -> M.addDefault
          M.empty (fun m (k, v) -> M.add k v m) k (exprId, v)) coef coefs),

        (* If the expression is an inequality, its weight should be
           positive *)
        (match op with
          | EQ -> constr
          | LTE -> Expr(GTE, M.add exprId 1 M.empty) :: constr
          | _ -> assert false),

        (* The flag to note that the interpolant should be LTE or EQ *)
        (if op = LTE then M.add exprId op ops else ops),

        (* Correspondance between expression ID and groupID *)
        (M.add exprId gid exprGroup)
      ) (M.empty, [], M.empty, M.empty) exprs in

    let predSols = MI.map (fun (params, a) ->
      (* Parameters have internal names at this moment, so they are renamed
         to 'a' - 'z' by alphabetical order. Make a renaming map and then
         apply it. We beleive there are no more than 26 parameters... *)
      let (i, renameMap) = List.fold_left (fun (i, m) x -> (i + 1),
        M.add x (String.make 1 (Char.chr (97 + i))) m) (0, M.empty) params in
      assert (i <= 26);
      let renameMap = ref renameMap in

      (* Parameter list for the predicate are renamed. *)
      renameList renameMap params,

      (* Predicate body are built from coefficient mapping by extracting only
         relating coefficinet and weight. Finally the body is renamed. *)
      renameExpr renameMap (ops, coefs |>
          M.filter (fun k _ -> List.mem k params || k = "") |>
          M.map (M.filter (fun k _ -> List.mem (M.find k exprGroup) a)))
    ) predMap in

    let constr = M.fold (fun k v -> (@) [ Expr((if k = "" then
        (* TODO: Consider completeness of Farkas' Lemma application. *)
        (if constr = [] then NEQ else GT) else EQ), v) ]) coefs constr in

    dnfChoice,
    predSols,
    new_id (), (* sentinel for merger *)
    (match constr with [c] -> c | _ -> And constr)
  ) (directProduct laDnfs) |>

  (fun x -> x, (MI.map snd predMap), predCopies) |>

  merge

let preprocLefthand =
  List.fold_left (fun (pvars, la) -> function
    | LinearExpr x -> pvars, Some (match la with
        | None -> x
        | Some y -> x &&& y)
    | PredVar pvar -> (pvar :: pvars), la) ([], None)

module Pexpr = struct
  type t = pexpr
  let compare = compare
end
module MP = Merge.Merger(Pexpr)

module PexprList = struct
  type t = pexpr list
  let compare = compare
end
module MPL = Merge.Merger(PexprList)


let combinationCheck lookup f a b c d e =
  let rec choose f a ((bi, bl) as b) c ((di, dl) as d) e = function
    | (i,x)::rest ->
      (choose f a (i, x::bl) c d e rest) &&
      (choose f a b c (i, x::dl) e rest)
    | [] ->
      bi < 0 || di < 0 || (
      List.sort (fun (x,_) (y,_) -> x-y) ([b;d] @ c) |>
      List.split |> (fun (_,x) -> f (a @ x @ e))) in
  let b' = List.map (fun x -> lookup x, x) b in
  let c' = List.map (fun x -> (List.hd x |> lookup), x) c in
  choose f a (-1, []) c' (-1, d) e (List.rev b')

let pexprMerge lookup input origin _ a b c d e =
  if not (combinationCheck lookup (
    fun x -> MP.M.mem x input) a b c d e) then None else

  (* Test wether the constraint is satisfiable or not. *)
  let test x = not (Z3interface.integer_programming x = None) in

  let (ids, puf, constrs) as sol = MP.M.find origin input in

  (* Extract one parameter each from two parameterized expression. *)
  List.map (
    tryPick (fun (op, coefs) ->
      tryPick (function
        | x :: _ -> Some (int_of_string (String.sub x 1 (String.length x - 1)))
        | _ -> None)
        ((M.keys op) :: (List.map M.keys (M.values coefs)))) |-
    (function
      | Some x ->
        List.fold_left (fun i y -> if x < y then i else i + 1) 0 ids |>
        Puf.find puf
      | None -> -1)) [b;d] |>

  function
    | [-1;-1] -> Some sol
    | [-1;gx]
    | [gx;-1] ->
      let add = generatePexprMergeConstr (List.hd b) (List.hd d) in
      let pgx = Puf.find puf gx in
      let constr = add &&& MI.find pgx constrs in
      if test constr then
        Some (ids, puf, MI.add pgx constr constrs)
      else None

    | [gb;gd] as g ->
      let add = generatePexprMergeConstr (List.hd b) (List.hd d) in
      let (constr, constrs) =
        List.map (Puf.find puf) g |>
        List.fold_left (fun (constr, constrs) x ->
          constr &&& (MI.find x constrs),
          MI.remove x constrs) (add, constrs) in
      if test constr then
        let puf = Puf.union puf gb gd in
        let constr = MI.add (Puf.find puf gb) constr constrs in
        Some (ids, puf, constrs)
      else None

let pexprListMerge lookup input origin _ a b c d e =
  if not (combinationCheck lookup (
    fun x -> MPL.M.mem x input) a b c d e) then None else

  let b, d = List.hd b, List.hd d in
  match List.fold_left (fun l x ->
    let ret =
      MP.merge_twoLists x pexprMerge b d |>
      MP.M.bindings |>
      List.split |> snd in
    ret @ l) [] (MPL.M.find origin input) with
    | [] -> None
    | x -> Some x

let validateMergeGroups predMerge =
  (* Use Jean-Christophe Filliâtre's Union-Find tree implementation. *)
  let m = ref M.empty in
  let puf = ref (Puf.create (2 * List.length predMerge)) in
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
    ret) predMerge

let tryMerge predMerge solution =
  validateMergeGroups predMerge |>

  List.fold_left (fun (fail, (preds, constr as sol)) (p1, p2) ->
    if fail then (true, sol) else (

    (* Specified predicate variables must exist. *)
    let [(param1, nf1);(param2, nf2)] = List.map (fun p ->
      assert (M.mem p preds); M.find p preds) [p1;p2] in

    (* Parameters for the predicate variable must match. It should have been
       renamed to (a,b, ...) during the solving algorithm, thus here the
       significance is in the number of the parameters. *)
    assert (param1 = param2);

    (* Try to merge nf1 and nf2. Randomly choose the first constraint if
       succeeds. *)
    let ret = MPL.merge_twoLists [constr] pexprListMerge nf1 nf2 in
    if MPL.M.cardinal ret > 0 then
      (false, (preds, List.hd (snd (MPL.M.choose ret))))
    else
      (true, sol))
  ) (false, solution) |> snd

let solve clauses =
  assert (List.length clauses > 0);
  reset_id ();

  List.map (fun (lh, rh) -> (preprocLefthand lh), rh) clauses |>
  buildGraph |>

  (* DEBUG: Show the constructed graph. *)
  (fun g ->
    let cycle = Traverser.has_cycle g in
    print_endline ("Cycle: " ^ (string_of_bool cycle));
    display_with_gv (Operator.mirror g);
    assert (not cycle);
    g) |>

  flattenGraph |>
  List.map solveTree |>

  reduce (fun (m1, i1, c1) (m2, i2, c2) ->
    (M.merge (fun _ a b ->
      match a, b with
        | None, None -> assert false
        | Some (p1, e1), Some (p2, e2) ->
          assert (p1 = p2); Some (p1, (e1 @ e2))
        | x, None
        | None, x -> x) m1 m2),
    i1 @ i2,
    let l1 = List.length i1 in
    MI.fold (fun k -> MI.add (k + l1)) c2 c1) |>

  (fun (m, i, c) -> (m, (i, Puf.create (List.length i), c)))

let getSolution = tryMerge ||- getSolution
