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


module GI = Graph.Persistent.Digraph.Concrete(Integer)
module MV = Map.Make(G.V)
module SV = Set.Make(G.V)
module TraverseGI = Graph.Traverse.Dfs(GI)
module TopologicalGI = Graph.Topological.Make(GI)

let extractCutpoints g =
  (* Unno's method. *)
  G.fold_vertex (fun v s ->
    if G.in_degree g v > 1 then SV.add v s else s) g SV.empty

let cutGraph g cutpoints =
  (* If no cutpoints are defined, do nothing. *)
  if SV.cardinal cutpoints = 0 then [g] else (

  (* Create a mapping from a vertex to an integer ID, and extract vertices to
     start traversal. They have no incoming edges. *)
  let _, ids, start = G.fold_vertex (fun v (i, m, s) ->
    (i + 1), (MV.add v i m),
    if G.in_degree g v = 0 then SV.add v s else s) g (0, MV.empty, SV.empty) in
  let lookup v = MV.find v ids in

  (* Create an Union-Find tree for decomposing tree. *)
  let p = Puf.create (G.nb_vertex g) in

  (* Compute connected components after cutting and relations between them. *)
  let rec step next visited puf link =
    if SV.is_empty next then
      (* If all the vertices are visited, return the result after converting
         vertex ID to its component ID. *)
      let find = Puf.find puf in
      MV.map find ids,
      List.map (fun (x, y) -> find x, find y) link
    else
      (* Randmoly pick one vertex to visit next as [u]. *)
      let u = SV.choose next in
      let next = SV.remove u next in
      let visited = SV.add u visited in

      (* Its successors are to be visited for future. *)
      let next, puf, link = G.fold_succ (fun v (next, puf, link) ->
        let next =
          if SV.mem v next || SV.mem v visited then next
          else SV.add v next in
        let puf, link =
          if SV.mem v cutpoints then puf, (lookup v, lookup u) :: link
          else Puf.union puf (lookup u) (lookup v), link in
        next, puf, link) g u (next, puf, link) in
      step next visited puf link in

  (* cmpMap will have a mapping from a vertex to a component ID which it belongs
     to. link will have a list of topological relations between components. *)
  let cmpMap, link = step start SV.empty p [] in

  (* Verify that those components don't have mutural dependency. *)
  let linkG = List.fold_left (fun g (x, y) -> GI.add_edge g x y) GI.empty link in
  if TraverseGI.has_cycle linkG then
    failwith "Invalid choice on cutting points. Mutural dependency introduced.";

  (* Fold over edges to create new graphs for each component. *)
  let components = G.fold_edges_e (fun e m ->
    let u = G.E.src e in
    let uid = MV.find u cmpMap in

    (* Adding an edge to a subgraph will also add the src and dst vertices of
       the edge. *)
    let gg =
      try MI.find uid m
      with Not_found -> G.empty in
    MI.add uid (G.add_edge_e gg e) m) g MI.empty in

  let components =
    (* NOTE: No need of List.rev *)
    TopologicalGI.fold (fun v l -> v :: l) linkG [] |>
    MI.fold (fun k _ l -> if List.mem k l then l else k :: l) components |>
    List.map (fun k -> MI.find k components) in

  (* Compute at each vertex linear expressions those are ancestors of it. *)
  let rec computeAncestors visited v =
    if MV.mem v visited then
      (* If the vertex is already visited, just return the saved result. *)
      visited, (MV.find v visited)
    else
      G.fold_succ_e (fun e (visited, la) ->
        (* Conjunction operation on Some. Similar to Maybe Monad. *)
        let (&&&) x = function
          | None -> Some x
          | Some y -> Some (x &&& y) in

        let u = G.E.dst e in
        match G.E.label e, G.V.label u with
          | None, LinearExpr ex ->
            (* No renaming should occur for linear expressions. *)
            visited, (ex &&& la)
          | Some rename, PredVar p ->
            let m = ref (
              List.fold_left (fun m (x, y) -> M.add x y m) M.empty rename) in
            if MV.mem u visited then
              let x = mapFormula (renameExpr m) (MV.find u visited) in
              visited, (x &&& la)
            else
              let visited', x = computeAncestors visited u in
              let x = mapFormula (renameExpr m) x in
              visited', (x &&& la)
      ) g v (visited, None) |>
      (function
        | _, None ->
          (* All nodes without incoming edges are linear expression nodes. *)
          assert false
        | visited, Some y ->
          (* Add traversal result. *)
          MV.add v y visited, y) in

  let rec step visited next =
    if SV.is_empty next then visited
    else
      let u = SV.choose next in
      let next = SV.remove u next in
      let visited, _ = computeAncestors visited u in
      step visited next in

  let leaves =
    step MV.empty cutpoints (*|>
    MV.filter (fun k _ -> SV.mem k cutpoints) *)in
  let u = MV.cardinal leaves in

  (* Attach ancestor linear expressions to cutpoints in every subgraph. *)
  let components = List.map (
    SV.fold (fun v g ->
      if G.mem_vertex g v && G.out_degree g v = 0 then (
        assert (MV.mem v leaves);
        let expr = MV.find v leaves in
        let u = G.V.create (LinearExpr expr) in
        G.add_edge g v u)
      else
        (* Other cases: Do nothing.
           not mem_vertex ... Doesn't belong to this subgraph.
           out_degree = 0 ... It's a root cutpoint.
           otherwise ........ Invalid cutpoint specification. Ignored. *)
        g)
      cutpoints) components in

  (* Return splitted graphs. *)
  components)

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
              M.map (fun v -> M.add exprId v M.empty) coef)
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

let reducePairs p =
  (* Use Jean-Christophe Filliâtre's Union-Find tree implementation. *)
  let m = ref M.empty in
  let puf = ref (Puf.create (2 * List.length p)) in
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
    ret) p

let tryUnify unify solution =
  List.fold_left (fun (fail, solution) pair ->
  if fail then (true, solution) else
    match tryUnify pair solution with
      | Some x -> (false, x)
      | None -> (true, solution)
    ) (false, solution) |> snd

let assignParameters assign (op, expr) = normalizeExpr (
  (M.fold (fun k v o -> if v <> 0 && M.findDefault EQ k op = LTE then
      (assert (v > 0); LTE) else o) assign EQ),
  M.map (fun v -> M.fold (fun k v -> (+) ((
    M.findDefault 1 k assign) * v)) v 0) expr)

let simplifyCNF =
  let simplifyDF =
    List.fold_left (fun (tautology, exprs) (op, coef as expr) ->
      if tautology then true, []
      else if M.cardinal coef = 0 then
        match op with
          | EQ | LTE | GTE -> true, []
          | NEQ | LT | GT -> false, exprs
      else if M.cardinal coef > 1 || not (M.mem Id.const coef) then
        false, expr :: exprs
      else (
        let c = M.find Id.const coef in
        match op with
          | EQ -> c = 0
          | LTE -> c <= 0
          | GTE -> c >= 0
          | NEQ -> c <> 0
          | LT -> c < 0
          | GT -> c > 0), exprs) (false, []) in

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
      if cntrdct then Expr (EQ, M.add Id.const 1 M.empty)
      else if List.length clauses = 0 then Expr (EQ, M.empty)
      else convertToFormula true clauses in
    params, formula) pexprs

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

  let g =
    List.map (fun (lh, rh) -> (preprocLefthand lh), rh) renClauses |>
    buildGraph in

  (* DEBUG: Show the constructed graph. *)
  let cycle = Traverser.has_cycle g in
  print_endline ("Cycle: " ^ (string_of_bool cycle));
  display_with_gv (Operator.mirror g);
  assert (not cycle);

  let cutpoints = extractCutpoints g in
  let cpl =
    SV.fold (fun x l ->
      let PredVar (p, _) = G.V.label x in
      Id.print p :: l
    ) cutpoints [] in
  print_endline ("Cutpoints: " ^ String.concat ", " cpl);
  let subgraphs = cutGraph g cutpoints in
  List.iter (Operator.mirror |- display_with_gv) subgraphs;

  flattenGraph g |>
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

let solve unify clauses =
  let sp = solve clauses in

  (* NYI: Unification *)
  let unify = reducePairs unify in
  if List.length unify <> 0 then
    failwith "NYI: Unification.";

  let sol = tryUnify unify sp |> getSolution in

  (* DEBUG: Solution verification. *)
  print_endline "\nVerification";
  assert (List.for_all (Z3interface.check_clause sol) clauses);
  print_newline ();

  sol
