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
    | _ -> c3 &&& (i1eq <=> i2eq) &&& (i1eq ==> c1) &&& ((!!!i1eq) ==> c2)

let buildGraph clauses =
  (* TODO: Handle props without assumptions, and props that imply nothing. *)

  (* Create predicate symbol vertices in advance. *)
  let predVertices = List.fold_left (fun predVertices (_, rh) ->
    match rh with
      | PredVar (p, l) ->
        if M.mem p predVertices then
          (* A predicate symbol should not be implied in different Horn clauses.
             e.g. x=0->A(x). y=0->A(y). is illegal. *)
          assert false
        else if List.length l <> List.length (distinct l) then
          (* The parameter definition has the same name variable in the list.
             e.g. x=0->A(x,x). is illegal. *)
          assert false
        else
          (* Create a new predicate vertex and remember it. *)
          M.add p (G.V.create rh) predVertices
      | _ -> predVertices) M.empty clauses in
  let predVertices = ref predVertices in

  List.fold_left (fun g (lh, rh) ->
    let src = match rh with
      | PredVar (p, _) -> M.find p !predVertices
      | LinearExpr _ -> G.V.create rh in
    let g = G.add_vertex g src in

    let (pvars, la) = lh in
    let g, dsts = List.fold_left (fun (g, dsts) (p, args) ->
      (* Get (or create if needed) the predicate variable vertex and its binder.
         We will relate this vertex from newly-created predicate variable
         vertices that corrensponds to the application of such predicates. The
         edge will carry binding information. *)
      let g, dst, binders =
        if M.mem p !predVertices then
          (* If exists, extract binders from the vertex label. *)
          let dst = M.find p !predVertices in
          let PredVar (_, binders) = G.V.label dst in
          g, dst, binders
        else (
          (* If not yet exists, create a new vertex with a fresh binder. [bot]
             implies the predicate symbol. This means that this predicate
             variable has no implication in input Horn clauses. *)
          let binders = repeat (fun _ l -> (new_name ()) :: l)
            (List.length args) [] in
          let dst = G.V.create (PredVar (p, binders)) in
          let bot = G.V.create (LinearExpr (Expr (EQ, M.add "" 1 M.empty))) in
          let g = G.add_edge g dst bot in
          predVertices := M.add p dst !predVertices;
          g, dst, args) in

      (* Build a name mapping between referred predicate variable (appears on
         the right-hand of Horn clause) and referring one (on the left-hand).

         NOTE: You must not omit same-name bindings such as (x,x). Otherwise, it
         will harm renaming during building constraints around line 156-158. *)
      let renames = listFold2 (fun l a b -> (a, b) :: l) [] binders args in

      (* Add a edge between origin *)
      g, (dst, Some renames) :: dsts
    ) (g, []) pvars in

    (* If a linear expression exists on the left-hand, create a corresponding
       vertex. *)
    let dsts = match la with
      | None -> dsts
      | Some x -> (G.V.create (LinearExpr x), None) :: dsts in

    (* Add edges between all left-hand terms and right-hand term. *)
    List.fold_left (fun g (dst, label) ->
      G.add_edge_e g (G.E.create src label dst)) g dsts
  ) G.empty clauses

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

    let g, v, nameMap = match G.V.label v with
      | LinearExpr e ->
        let nameMap = ref M.empty in
        ignore(mapFormula (renameExpr nameMap) e);
        g, v, M.fold (fun k v -> M.add k k) !nameMap M.empty
      | PredVar (_, l) ->
        let top = G.V.create (LinearExpr (Expr (EQ, M.empty))) in
        G.add_edge_e g (G.E.create top (Some (
          List.map (fun x -> (x, x)) l)) v), top, M.empty
    in

    let rec f v nameMap g' =
      let registerLa la =
        let key = MI.cardinal !laGroups in
        laGroups := MI.add key la !laGroups; key in

      let (g', u's, u'keys, _) = G.fold_succ_e (fun e
        (g', u's, u'keys, hadLa) ->

        let u = G.E.dst e in
        match G.V.label u, G.E.label e with
          | PredVar _, Some bindings ->
            (* Bindings of predicate variables are converted to linear equations
               so that it can be treated easy. Note that the binder and argument
               will have different names even if they have the same one before
               conversion.*)
            let nameMap = List.fold_left (fun m (x, y) ->
              let y' = renameVar nameMap y in
              M.add x y' m) M.empty bindings in

            (* Traverse children first to unify predicate variable nodes. *)
            let (g', u', u'keys') = f u (ref nameMap) g' in
            g', ((u', Some bindings) :: u's), u'keys' @ u'keys, hadLa

          | LinearExpr e, None ->
            if hadLa then
              (* NOTE: Linear expressions must appear only once. *)
              assert false
            else
              let laKey = registerLa (e, !nameMap) in
              g', (G'.V.create (La laKey), None) :: u's, laKey :: u'keys, true

          | _ -> assert false
      ) g v (g', [], [], false) in

      let v' = G'.V.create (
        match G.V.label v with
          | PredVar (p, param) ->
            let pid = (new_id ()) in
            predMap := MI.add pid (param, u'keys) !predMap;
            predCopies := M.addDefault [] (fun l x -> x :: l) p pid !predCopies;
            Pid pid

          | LinearExpr e ->
            (* NOTE: The vertex 'v' must be the root of traversal. *)
            La (registerLa (!!!e, !nameMap))) in

      (* Add edges between new left-hand nodes and right-hand node. *)
      let g' = List.fold_left (fun g' (u', lb) ->
        G'.E.create u' lb v' |> G'.add_edge_e g') g' u's in
      g', v', u'keys
    in
    let (g', _, _) = f v (ref nameMap) G'.empty in
    g', !laGroups, !predMap, !predCopies)

let getSolution (pexprs, (_, _, constrs)) =
  let sol = MI.fold (fun _ constr m ->
    match Z3interface.integer_programming constr with
      | Some sol -> M.simpleMerge sol m
      | None -> raise Not_found) constrs M.empty in

  (* Construct one interpolant *)
  M.map (fun (params, cnf) ->
    let x = convertToFormula true cnf in
    params, (mapFormula (assignParameters sol) x)) pexprs

let merge (sols, predMap, predCopies) =
  let predSols, maxIds, constrs = List.fold_left (fun
    (predSolsByPred, maxIds, constrs)
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

let solveTree (g, laGroups, predMap, predCopies) =
  display_with_gv' g;

  (* Perform topological sort. *)
  let pvs = List.rev (Sorter.fold (fun v l ->
    match G'.V.label v with Pid _ -> v :: l | _ -> l) g []) in

  let (laIds, laDnfs) = laGroups |>
      MI.map (
        fst |-
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
      (MI.add x z s), ((List.map (fun z ->
        (x, "p" ^ (string_of_int (new_id ())), z)) y) @ t))
      (MI.empty, []) laIds assigns in

    (* Create a new copy of renaming maps for each group. This must be done here
       inside this loop because the renaming map must be shared inside the group
       and must not be shared across different DNF choices. *)
    let laRenames = MI.map (fun x -> ref (snd x)) laGroups in

    (* Build the coefficient mapping for all assigned expressions and check
       the operator of each expression. *)
    let coefs, constr, ops, exprGroup =
      List.fold_left (fun (coefs, constr, ops, exprGroup) (gid, exprId, expr) ->
        let (op, coef) = renameExpr (MI.find gid laRenames) expr in

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

    let predSols = List.fold_left (fun m pv ->
      let Pid pid = G'.V.label pv in
      let (params, a) = MI.find pid predMap in

      (* Predicate body are built from coefficient mapping by extracting only
         relating coefficinet and weight. *)
      let x = G'.fold_pred_e (fun e x -> x +++ (
        match G'.V.label (G'.E.src e), G'.E.label e with
          | Pid pid', Some bindings ->
            let _, (_, pcoefs) = MI.find pid' m in
            M.fold (fun k v m ->
              let k = try List.assoc k bindings with Not_found -> k in
              (M.add k v M.empty) +++ m) pcoefs M.empty
          | La laId, None ->
            List.fold_left (fun coefs (gid, exprId, (_, coef)) ->
              if gid <> laId then coefs else
              M.fold (fun k v -> M.addDefault
                M.empty (fun m (k, v) -> M.add k v m) k (exprId, v)) coef coefs
            ) M.empty exprs
          | _ -> assert false)
      ) g pv M.empty in

      MI.add pid (params, (ops, x)) m
    ) MI.empty pvs in

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

  (function
    | [-1;-1] -> `A
    | [-1;gx]
    | [gx;-1] -> `B gx
    | [gb;gd] -> if gb = gd then `B gb else `C (gb, gd)
    | _ -> assert false) |>

  (function
    | `A -> Some sol
    | `B gx ->
      let add = generatePexprMergeConstr (List.hd b) (List.hd d) in
      let pgx = Puf.find puf gx in
      let constr = add &&& MI.find pgx constrs in
      if test constr then
        Some (ids, puf, MI.add pgx constr constrs)
      else None
    | `C (gb, gd) ->
      let add = generatePexprMergeConstr (List.hd b) (List.hd d) in
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

    (* Parameters for the predicate variable must match. *)
    assert (List.length param1 = List.length param2);
    let preds, nf2 =
      if param1 = param2 then preds, nf2 else
        let m = ref (listFold2 (fun m a b -> M.add a b m)
          M.empty param1 param2) in
        let nf2 = List.map (List.map (renameExpr m)) nf2 in
        M.add p2 (param1, nf2) preds, nf2 in

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
