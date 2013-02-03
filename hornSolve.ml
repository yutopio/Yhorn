open Util
open Types

let buildGraph clauses =
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
          let binders = repeat (fun _ l -> (Id.create ()) :: l)
            (List.length args) [] in
          let dst = G.V.create (PredVar (p, binders)) in
          let bot = G.V.create (LinearExpr (Expr (EQ, M.add Id.const 1 M.empty))) in
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
    let predMap = ref M.empty in
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
            let pid = Id.create () in
            predMap := M.add pid (param, u'keys) !predMap;
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
    List.filter (fun x -> x <> (EQ, M.empty) &&
                          x <> (LTE, M.empty)) x))) laDnfs in

  let sols = List.map (fun assigns ->
    (* Give IDs and flatten. *)
    let dnfChoice, exprs = listFold2 (fun (s, t) x (z, y) ->
      (MI.add x z s), ((List.map (fun z ->
        (x, Id.create (), z)) y) @ t))
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
        print_endline ((string_of_int gid) ^ "\t" ^ Id.print exprId ^ "\t" ^
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
      let (params, _) = M.find pid predMap in

      (* Predicate body are built from coefficient mapping by extracting only
         relating coefficinet and weight. *)
      let x = G'.fold_pred_e (fun e x -> x @ (
        match G'.V.label (G'.E.src e), G'.E.label e with
          | Pid pid', Some bindings ->
            let _, (_, pcoefs) = M.find pid' m in
            M.fold (fun k v l ->
              let k = try List.assoc k bindings with Not_found -> k in
              (M.add k v M.empty) :: l) pcoefs []
          | La laId, None ->
            List.filter (fun (gid, _, _) -> gid = laId) exprs |>
            List.map (fun (_, exprId, (_, coef)) ->
              M.fold (fun k v -> M.addDefault
                M.empty (fun m (k, v) ->
                  assert (not (M.mem k m));
                  M.add k v m) k (exprId, v)) coef M.empty)
          | _ -> assert false)
      ) g pv [M.empty] in

      M.add pid (params, (ops, reduce (+++) x)) m
    ) M.empty pvs in

    let constr = M.fold (fun k v -> (@) [ Expr((if k = Id.const then
        (* TODO: Consider completeness of Farkas' Lemma application. *)
        (if constr = [] then NEQ else GT) else EQ), v) ]) coefs constr in

    dnfChoice,
    predSols,
    Id.create (), (* sentinel for merger *)
    (match constr with [c] -> c | _ -> And constr)
  ) (directProduct laDnfs) in

  let predMap = M.map snd predMap in
  let predSols, maxIds, constrs = List.fold_left (fun
    (predSolsByPred, maxIds, constrs)
    (dnfChoice, predSolsByDnf, maxId, constr) ->
      M.fold (fun pid ->
        M.addDefault ([], MIL.empty) (fun (_, m) (param, pexpr) -> param,
          let groupKey =
            (MI.fold (fun k v l ->
              if List.mem k (M.find pid predMap) then l
              else (k, v) :: l) dnfChoice []) |>
            (List.sort comparePair) |>
            List.split |> snd in
          MIL.addDefault [] (fun l x -> x :: l) groupKey pexpr m
        ) pid) predSolsByDnf predSolsByPred,
      maxId :: maxIds,
      MI.add (List.length maxIds) constr constrs
  ) (M.empty, [], MI.empty) sols in

  let predSols = M.map (fun (param, pexpr) -> param,
    MIL.fold (fun _ v l -> v :: l) pexpr []) predSols in

  (M.map (fun x ->
    reduce (fun (p1, e1) (p2, e2) -> assert (p1 = p2); (p1, e1 @ e2))
      (List.map (fun x -> M.find x predSols) x)) predCopies),
  (List.rev maxIds),
  constrs

let simplifyPCNF clauses =
  let simplifyPDF exprs =
    assert (List.length exprs > 0);
    let tautology = List.exists (fun (_, coef) ->
      (* NOTE: We don't need to consider operator because only EQ and LTE are
         used. If there is no coefficient, it must be tautology. *)
      List.length (M.keys coef) = 0) exprs in
    if tautology then []
    else exprs in

  assert (List.length clauses > 0);
  let filtered = List.fold_left (fun l x ->
    let x = simplifyPDF x in
    if x = [] then l else x :: l) [] clauses in
  if List.length filtered = 0 then [[M.empty, M.empty]] (* Tautology *)
  else [M.empty, M.empty] :: filtered

let renameClauses =
  List.fold_left (fun (clauses, pm) (lh, rh) ->
    let vm = ref M.empty in
    let pm = ref pm in
    let f = function
      | PredVar (p, l) ->
        let p' = M.findDefault (Id.from_string (
          "P" ^ string_of_int (M.cardinal !pm))) p !pm in
        pm := M.add p p' !pm;
        ignore(renameList vm l);
        PredVar (p', l)
      | LinearExpr e ->
        ignore(mapFormula (renameExpr vm) e);
        LinearExpr e in
    let terms = List.map f (rh::lh) in
    let i = ref 0 in
    vm := M.map (fun v -> Id.from_string ("x" ^ string_of_int (incr i; !i))) !vm;
    let rh::lh = List.map (renameHornTerm vm) terms in
    (lh, rh) :: clauses, !pm
  ) ([], M.empty)

let solve clauses =
  assert (List.length clauses > 0);

  (* DEBUG: *)
  print_newline ();
  print_endline "Yhorn\n";
  let renClauses, pm = renameClauses clauses in
  let pm = M.fold (fun k v -> M.add v k) pm M.empty in
  print_endline (
    String.concat "\n" (List.map printHorn renClauses) ^ "\n");
  let preprocLefthand = List.fold_left (fun (pvars, la) -> function
    | LinearExpr x -> pvars, Some (match la with
        | None -> x
        | Some y -> x &&& y)
    | PredVar pvar -> (pvar :: pvars), la) ([], None) in
  List.map (fun (lh, rh) -> (preprocLefthand lh), rh) renClauses |>
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

  fun (m, i, c) ->
    M.fold (fun k (p, v) -> M.add (M.find k pm) (p, simplifyPCNF v)) m M.empty,
    (i, Puf.create (List.length i), c)

let solve x = x, (solve x)
