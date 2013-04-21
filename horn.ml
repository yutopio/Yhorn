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

let cutGraph g =
  let cutpoints =
    G.fold_vertex (fun v s ->
      if G.in_degree g v > 1 then SV.add v s else s) g SV.empty in
  Types.Display.highlight_vertices := cutpoints;

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
    step MV.empty cutpoints |>
    MV.filter (fun k _ -> SV.mem k cutpoints) in
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

let solveTree g =
  (* Assign a template to all predicate variables. *)
  (* TODO: Currently supported template is only [1] in Module Template type.
           Any larger templates should be available in future. *)
  let templ =
    G.fold_vertex (fun v m ->
      match G.V.label v with
      | LinearExpr _ -> m
      | PredVar (p, param) ->
        let rename =
          List.fold_left (fun m x -> M.add x (Id.create ()) m) M.empty param |>
          M.add Id.const (Id.create ()) in
        M.add p (param, rename) m) g M.empty in

  let constrs = G.fold_vertex (fun v x ->
    let l1, l2 = G.fold_succ_e (fun e (l1, l2) ->
      match G.E.label e, G.V.label (G.E.dst e) with
      | None, LinearExpr e ->
        print_endline ("LinE  " ^ printFormula printExpr e);
        e :: l1, l2
      | Some rename, PredVar (p, param) ->
        l1,
        (* TODO: Currently all template are considered to be LTE. *)
        let rename = List.fold_left (fun m (a, b) ->
          M.add a b m) M.empty rename in
        let _, pm = M.find p templ in
        let pm = M.fold (fun k -> M.add (
          if k = Id.const then Id.const
          else M.find k rename)) pm M.empty in
        let pexpr = M.empty, M.map (fun x -> M.add x 1 M.empty) pm in
        (print_endline ("Pred  " ^ printPexpr pexpr);
        pm :: l2)
    ) g v ([], []) in

    if l1 = [] && l2 = [] then x else (

    let addPcoef = M.addDefault M.empty (fun m (k, v) -> M.add k v m) in

    let addLinear x =
      mapFormula normalizeExpr |-
      splitNegation |-
      convertToNF false |-

      (* TODO: Support of disjunctions.
         We now only consider first conjunction in DNF. *)
      (function
      | [x] -> x
      | [] -> assert false
      | x::_ ->
        print_endline "Omitting conjunctions..."; x) |-

      (* Filter the inserted tautologies 0=0 during the process. *)
      List.filter (fun x -> x <> (LTE, M.empty)) |-

      (* Add to the variable maps for applying Farkas' Lemma. *)
      List.fold_left (fun (m, pis) (op, coef) ->
        let pi = Id.create () in

        (* Building an coefficient mapping in terms of variables. *)
        (M.fold (fun k v -> addPcoef k (pi, v)) coef m),

        (* TODO: Linear expression must be normalized to LTE. No EQ allowed. *)
        (match op with
        | LTE -> pi :: pis
        | _ -> assert false)) x in

    let m, pis = List.fold_left addLinear (M.empty, []) l1 in

    let m = List.fold_left (fun m pcoef ->
      (* Building an coefficient mapping in terms of variables. *)
      (M.fold (fun k v -> addPcoef k (v, 1)) pcoef m))
      m l2 in

    let m =
      match G.V.label v with
      | LinearExpr e ->
        addLinear (m, []) (!!! e) |> fst
      | PredVar (p, param) ->
        (* TODO: Currently all template are considered to be LTE. *)
        let _, pcoef = M.find p templ in

        (* Building an coefficient mapping in terms of variables. *)
        M.fold (fun k v -> addPcoef k (v, -1)) pcoef m |>
        addPcoef Id.const (Id.const, 1) in

    (* Every linear inequality must be weighted non-negative. *)
    List.fold_left (fun l pi -> Expr (GTE, M.add pi 1 M.empty) :: l) x pis |>

    (* Additionally, add constraints to make totals on every
       coefficients zero. *)
    M.fold (fun k v c ->
      Expr ((if k = Id.const then GT else EQ), v) :: c) m
    )) g [] in

  M.map (fun (param, v) -> param,
    [[M.fold (fun _ v -> M.add v LTE) v M.empty,
      M.map (fun v -> M.add v 1 M.empty) v]]) templ,
  [ Id.create () ],
  MI.add 1 (And constrs) MI.empty

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

let tryUnify solution =
  List.fold_left (fun (fail, solution) pair ->
  if fail then (true, solution) else
    match tryUnify pair solution with
      | Some x -> (false, x)
      | None -> (true, solution)
    ) (false, solution) |- snd

let assignParameters assign (op, expr) = normalizeExpr (
  (M.fold (fun k v o -> if v <> 0 && M.findDefault EQ k op = LTE then
      LTE else o) assign EQ),
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

  print_endline ("Yhorn (" ^ Version.date ^ ")\n");
  print_newline ();

  let clauses, pm =
    if !Flags.rename_input then renameClauses clauses
    else clauses, M.empty in
  let pm = M.fold (fun k v -> M.add v k) pm M.empty in

  print_endline (String.concat "\n" (List.map printHorn clauses));
  print_newline ();

  let preprocLefthand = List.fold_left (fun (pvars, la) -> function
    | LinearExpr x -> pvars, Some (match la with
        | None -> x
        | Some y -> x &&& y)
    | PredVar pvar -> (pvar :: pvars), la) ([], None) in

  let g =
    List.map (fun (lh, rh) -> (preprocLefthand lh), rh) clauses |>
    buildGraph in

  (* We don't handle cyclic graphs. *)
  assert (not (Traverser.has_cycle g));

  (* Compute suitable cutpoints. *)
  let subgraphs = cutGraph g in

  (* DEBUG: Show the constructed graph. *)
  display_with_gv (Operator.mirror g);

  List.fold_left (fun sol g ->
    print_endline "Solving subgraph";
    display_with_gv (Operator.mirror g);

    (* Replace known nodes with linear expressions. *)
    let vReplace = G.fold_vertex (fun v m ->
      if G.in_degree g v = 0 then
        match G.V.label v with
        | PredVar (p, args) ->
          let (param, sol) = M.find p sol in
          let rename = ref (listFold2 (
            fun m u v -> M.add u v m) M.empty param args) in
          let body = LinearExpr (mapFormula (renameExpr rename) sol) in
          MV.add v (G.V.create body) m
        | _ -> m
      else m) g MV.empty in
    let g = MV.fold (fun k v ->
      G.fold_succ_e (fun e g' ->
        G.add_edge_e g' (G.E.create v (G.E.label e) (G.E.dst e))
      ) g k |-
      (fun g' -> G.remove_vertex g' k)
    ) vReplace g in

    print_endline "Replaced precomputed solution";
    display_with_gv (Operator.mirror g);

    solveTree g |>

    (fun (m, i, c) ->
      M.fold (fun k (p, v) -> M.add k (p, simplifyPCNF v)) m M.empty,
      (i, Puf.create (List.length i), c)) |>

    getSolution |>

    (* TODO: Simple merge is not appropriate here. *)
    M.simpleMerge sol |>

    (fun x -> print_endline (printHornSol x); x)
  ) M.empty subgraphs |>

  (fun x -> M.fold (fun k -> M.add (M.findDefault k k pm)) x M.empty)

let solve clauses unify =
  (* NYI: Unification [tryUnify] ? *)
  let unify = reducePairs unify in
  if List.length unify <> 0 then
    failwith "NYI: Unification.";
  let sol = solve clauses in

  (* DEBUG: Solution verification. *)
  List.iter (fun x ->
    print_endline (printHorn x);
    if not (Z3interface.check_clause sol x) then
      failwith "Verification failed") clauses;

  sol
