open Util
open Types
open MapEx

let maybeApply f = function
  | None -> None
  | Some x -> Some (f x)

let createRename = listFold2 (fun l a b -> (a, b) :: l) []

let preprocLefthand = List.fold_left (fun (pvars, la) ->
  function
  | LinearExpr x -> pvars, Some (
    match la with
    | None -> x
    | Some y -> x &&& y)
  | PredVar pvar -> (pvar :: pvars), la) ([], None)

let buildGraph clauses =
  let clauses = List.map (fun (lh, rh) -> (preprocLefthand lh), rh) clauses in

  (* Create predicate symbol vertices in advance. *)
  let addVp vp (p, l) =
    let ll = List.length l in
    if ll <> List.length (distinct l) then
      (* The parameter definition has the same name variable in the list.
         e.g. x=0->A(x,x). is illegal. *)
      failwith "Binder contains multiple appearance of the same variable."
    else if M.mem p vp then (
      (* A predicate symbol which is implied in multiple Horn clauses should
         have the same arity across them. *)
      let PredVar (p', l') = M.find p vp |> G.V.label in assert (p = p');
      if ll <> List.length l' then
        failwith ("Inconsistent arity for predicate variable " ^ Id.print p)
      else vp
    ) else
      (* Create a new predicate vertex and remember it. *)
      let binders = repeat (fun _ l -> (Id.create ()) :: l) ll [] in
      M.add p (G.V.create (PredVar (p, binders))) vp in

  (* Create vertices. *)
  let predVertices = List.fold_left (fun vp ((lh, _), rh) ->
    let vp =
      match rh with
      | PredVar pvar -> addVp vp pvar
      | _ -> vp in
    List.fold_left addVp vp lh) M.empty clauses in

  (* Add implication relations on the Horn graph. *)
  List.fold_left (fun g ((pvars, la) as lh, rh) ->
    let (pvars, la), src =
      match rh with
      | PredVar (p, binder) ->
        let src = M.find p predVertices in
        let PredVar (p', binder') = G.V.label src in assert (p = p');
        let rename =
          createRename binder binder' |>
          List.fold_left (fun m (a, b) -> M.add a b m) M.empty |> ref in
        ((List.map (fun (p, args) -> p, renameList rename args) pvars),
        (maybeApply (mapFormula (renameExpr rename)) la)), src
      | LinearExpr _ -> lh, G.V.create rh in
    let g = G.add_vertex g src in

    let dsts = List.fold_left (fun dsts (p, args) ->
      (* Get the predicate variable vertex and its binder. We will relate this
         vertex from newly-created predicate variable vertices that corrensponds
         to the application of such predicates. The edge will carry binding
         information. *)
      let dst = M.find p predVertices in
      let PredVar (p', binder) = G.V.label dst in assert (p = p');
      let rename = createRename binder args in

      (* Add a edge between origin *)
      (dst, Some rename) :: dsts
    ) [] pvars in

    (* If a linear expression exists on the left-hand, create a corresponding
       vertex. *)
    let dsts =
      match la with
      | None -> dsts
      | Some x -> (G.V.create (LinearExpr x), None) :: dsts in

    (* Add edges between all left-hand terms and right-hand term. *)
    List.fold_left (fun g (dst, label) ->
      G.add_edge_e g (G.E.create src label dst)) g dsts
  ) G.empty clauses

module EOpt(E: Graph.Sig.EDGE) = struct
  type t = E.t option
  let default = None
  let compare x y =
    match x, y with
    | None, None -> 0
    | Some _, None -> -1
    | None, Some _ -> 1
    | Some x, Some y -> E.compare x y
end

module GI = Graph.Persistent.Digraph.Concrete(Integer)
module GV = Graph.Persistent.Digraph.AbstractLabeled(G.V)(EOpt(G.E))
module MV = Map.Make(G.V)
module MVV = Map.Make(GV.V)
module ME = Map.Make(EOpt(G.E))
module SV = Set.Make(G.V)
module TopologicalGI = Graph.Topological.Make(GI)

let addRoot g =
  assert (not (G.is_empty g));

  let roots = G.fold_vertex (fun v s ->
    if G.in_degree g v = 0 then SV.add v s else s) g SV.empty in

  if SV.cardinal roots = 1 then
    g, (SV.choose roots)
  else
    let root = G.V.create (LinearExpr (Expr (EQ, M.empty))) in
    let g = SV.fold (fun v g -> G.add_edge g v root) roots g in
    g, root

let assignParameters assign (op, expr) = normalizeExpr (
  (M.fold (fun k v o -> if v <> 0 && M.findDefault EQ k op = LTE then
      LTE else o) assign EQ),
  M.map (fun v -> M.fold (fun k v -> (+) ((
    M.findDefault 1 k assign) * v)) v 0) expr)

let solveGraph (g, root) =
  let cutpoints =
    G.fold_vertex (fun v s ->
      if G.in_degree g v > 1 then SV.add v s else s) g SV.empty in
  (* DEBUG: *) Types.Display.highlight_vertices := cutpoints;

  (* Create a template for all predicate variable vertices. *)
  let templ = G.fold_vertex (fun v m ->
    match G.V.label v with
    | PredVar (p, param) ->
      (* Create a template. *)
      let pcoef =
        List.fold_left (fun m x ->
          M.add x (Id.create ()) m) M.empty param |>
        M.add Id.const (Id.create ()) in

      M.add p pcoef m
    | _ -> m) g M.empty in

  (* Create a mapping from a vertex to an integer ID. *)
  let _, ids = G.fold_vertex (fun v (i, m) ->
    (i + 1), (MV.add v i m)) g (0, MV.empty) in
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
  let cmpMap, link = step (SV.add root SV.empty) SV.empty p [] in

  (* Create a dependency graph between subtrees. *)
  let gi = GI.add_vertex GI.empty (lookup root) in
  let linkG = List.fold_left (fun g (x, y) -> GI.add_edge g x y) gi link in

  (* Fold over edges to create new graphs for each component. *)
  let components =
    let rid = MV.find root cmpMap in
    let gg = G.add_vertex G.empty root in
    MI.add rid gg MI.empty |>
    G.fold_edges_e (fun e m ->
      let u = G.E.src e in
      let uid = MV.find u cmpMap in
      let gg =
        try MI.find uid m
        with Not_found -> G.empty in
      (* Adding an edge to a subgraph will also add the src and dst vertices of
         the edge. *)
      let m = MI.add uid (G.add_edge_e gg e) m in

      let v = G.E.dst e in
      let vid = MV.find v cmpMap in
      let gg =
        try MI.find vid m
        with Not_found -> G.empty in
      MI.add vid (G.add_vertex gg v) m) g in

  (* Calculate roots. *)
  (* NOTE: To be precise, key values to add to the mapping should be evaluated
           through Puf.find. In this specific case, because of Puf's
           implementation, all values stay the same on Puf.union order
           (see line 142). *)
  let roots =
    MI.add (lookup root) root MI.empty |>
    SV.fold (fun v -> MI.add (lookup v) v) cutpoints in

  (* Make a list of subtrees. *)
  let linkOrder = TopologicalGI.fold (fun v l -> v :: l) linkG [] |> List.rev in
  let components = linkOrder |>
    List.map (fun k -> (MI.find k roots), (MI.find k components)) in

  (* For simplification purpose, travese the component link graph and compute
     appropriate quantifiers. *)
  let (fvs, use) = List.fold_left (fun (fvs, use) x ->
    let v = MI.find x roots in
    let fv =
      match G.V.label v with
      | LinearExpr _ -> [] (* TODO: Should consider? *)
      | PredVar (p, param) -> M.find p templ |> M.values in
    let use' = fv @ (MI.findDefault [] x use |> sort_distinct) in
    (MI.add x fv fvs),
    (GI.fold_succ (fun y -> MI.addDefault [] (@) y use') linkG x use)
  ) (MI.empty, MI.empty) linkOrder in
  let quant = List.fold_left (fun quant x ->
    let use = MI.findDefault [] x use in
    let dup = List.fold_left (fun m x ->
      M.addDefault 0 (+) x 1 m) M.empty use in
    let l1 = M.fold (fun k v l -> if v > 1 then k :: l else l) dup [] in
    let l2 = MI.find x fvs in
    let l3 =
      GI.fold_succ (fun y -> (@) (MI.find y quant)) linkG x [] |>
      List.filter (fun x -> List.mem x use) in
    MI.add x (sort_distinct (l1 @ l2 @ l3)) quant
  ) MI.empty (List.rev linkOrder) in

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

  (* TODO: Currently supported template is only [1] in Module Template type.
           Any larger templates should be available in future. *)

  (* Duplicating templates is done by simple renaming. *)
  let duplicate (pop, pcoef, constr) =
    let map = ref M.empty in
    M.fold (fun k -> M.add (renameVar map k)) pop M.empty,
    M.fold (fun k -> M.add (renameVar map k)) pcoef M.empty,
    mapFormula (renameExpr map) constr in

  (* Compute at each vertex linear expressions those are ancestors of it. *)
  let rec computeAncestors templs v e g =
    if MV.mem v templs then
      (* If the vertex is already registered in the template list, it is a
         forking predicate variable node. *)
      let deltaMap, defDelta, dup = MV.find v templs in

      (* If the predicate is specified for duplication, rename it. *)
      let delta =
        try ME.find e deltaMap
        with Not_found -> (if dup then duplicate else id) defDelta in
      MV.add v [e, delta] MV.empty
    else
      let ret, constrs, (m, pis) =
        G.fold_succ_e (fun e (ret, constrs, (m, pis)) ->
          let u = G.E.dst e in
          match G.E.label e, G.V.label u with
          | None, LinearExpr ex ->
            (* No renaming should occur for linear expressions. *)
            (* TODO: We should consider disjunctive linear expressions. *)
            ret, constrs, (addLinear (m, pis) ex)
          | Some rename, PredVar (p, param) ->
            let ret' = computeAncestors templs u (Some e) g in

            (* TODO: We should consider disjunctive templates. *)
            (* TODO: Support parameterized operators. *)
            let [_, (pop, pcoef, constr)] = MV.find u ret' in

            let rename = ref (
              List.fold_left (fun m (x, y) -> M.add x y m) M.empty rename) in
            let f k v = addPcoef (renameVar rename k) (v, 1) in

            (* Merging returning template. *)
            let ret = MV.merge (fun _ -> maybeAdd (@)) ret ret' in

            (* Building an coefficient mapping in terms of variables. *)
            ret, (maybeAdd (&&&) constrs (Some constr)),
            ((M.fold f pcoef m), pis)
          | _ -> assert false
        ) g v (MV.empty, None, (M.empty, [])) in

      let (m, pis), (pop, pcoef) =
        match G.V.label v with
        | LinearExpr e ->
          (* Add the current linear expression for Farkas' target. *)
          (addLinear (m, pis) (!!! e)),

          (* Should return tautology for performance; will be evaluated at
             the bottom node. *)
          (M.empty, M.empty)

        | PredVar (p, param) ->
          let pcoef = M.find p templ in

          (* Add the atomic current predicate template for Farkas' target. *)
          let m =
            M.fold (fun k v -> addPcoef k (v, -1)) pcoef m |>
            addPcoef Id.const (Id.const, 1) in

          (m, pis),
          (* TODO: Currently all template are considered to be LTE. *)
          (M.fold (fun _ v -> M.add v LTE) pcoef M.empty, pcoef) in

      let constrs =
        (* Every linear inequality must be weighted non-negative. *)
        List.fold_left (fun l pi ->
          Expr (GTE, M.add pi 1 M.empty) :: l) [] pis |>

        (* Additionally, add constraints to make totals on every
           coefficients zero. *)
        M.fold (fun k v c ->
          Expr ((if k = Id.const then GT else EQ), v) :: c) m |>

        fun x -> match constrs with
        | None -> And x
        | Some y -> (And x) &&& y
      in

      MV.add v [e, (pop, pcoef, constrs)] ret in

  let simplifyConstr = assert false in

  (* Create templates and constraints for all predicate variables over the
     graph. *)
  let rootTempls =
    List.fold_left (fun templ (root, g) ->
      let templ' = computeAncestors (MV.map fst templ) root None g in

      let [_, (pop, pcoef, constr)] = MV.find root templ' in
      let constr = simplifyConstr constr in

      MV.add root ((ME.empty, (pop, pcoef, constr), false), templ') templ
    ) MV.empty components in

  (* Generate split tree. *)
  let rootV = GV.V.create root in
  let st = GV.add_vertex GV.empty rootV in

  (* Traverse the split tree to generate root constraint. *)
  let rec step v =
    let mvv, me = GV.fold_succ_e (fun e (mvv, me) ->
      let u = GV.E.dst e in
      let mvv' = step u in
      MVV.simpleMerge mvv mvv',
      ME.addDefault [] (fun x y -> y :: x)
        (GV.E.label e) (GV.V.label u, MVV.find u mvv') me
    ) st v (MVV.empty, ME.empty) in

    let v' = GV.V.label v in
    let g' = List.assoc v' components in

    let me = ME.map (fun l ->
      let templs =
        List.fold_left (fun mv (v, me) ->
          (* NOTE: The same v won't appear more than once. *)
          let (_, templ, _) = MV.find v mv in
          let me = ME.map fst me in
          MV.add v (me, templ, true) mv
        ) (MV.map fst rootTempls) l in

      let templ' = computeAncestors templs v' None g' in

      let [_, (pop, pcoef, constr)] = MV.find v' templ' in
      (* TODO: Simplification will be done here.
         let constr = simplifyConstr constr in *)

      (pop, pcoef, constr), templ') me in
    MVV.add v me mvv
  in

  let constrTree = step rootV in
  let rec step v (op, coef) =
    let f v =
      let (_, x, _), templ = MV.find v rootTempls in
      (x, templ), MV.empty in
    let ((pop, pcoef, constr), templ), subprobl =
      match v with
      | `A (e, vv) ->
        let c = MVV.find vv constrTree in (
        try
          ME.find e c,
          GV.fold_succ_e (fun e' m ->
            if GV.E.label e' = e then
              let u = GV.E.dst e' in
              MV.add (GV.V.label u) (u, MVV.find u constrTree) m
            else m) st vv MV.empty
        with Not_found -> f (GV.V.label vv))
      | `B v -> f v in

    (* TODO: Fix the assignment. *)
    let constr = assert false in

    (* Once the root constraint become satisfiable, all subproblems should have
       a solution. *)
    let Some sol = Z3interface.integer_programming constr in

    MV.fold (fun k v predSol ->
      match G.V.label k with
      | LinearExpr _ -> (* predSol *) assert false
      | PredVar (p, param) ->
        List.fold_left (fun predSol (e, (pop, pexpr, _)) ->
          let pexpr = M.map (fun x -> M.add x 1 M.empty) pexpr in
          let expr = assignParameters sol (pop, pexpr) in
          let predSol = M.addDefault [] (fun a b -> b :: a) p expr predSol in

          if List.mem_assoc k components then
            (* This vertex is a cutpoint. *)
            let predSol' =
              try
                let vv, _ = MV.find k subprobl in
                step (`A (e, vv)) expr
              with Not_found -> step (`B k) expr in
            M.merge (fun _ -> maybeAdd (@)) predSol predSol'
          else predSol
        ) predSol v
    ) templ M.empty in
  step (`A (None, rootV)) (LTE, M.empty)

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

  (* Generate the problem graph. *)
  let g = buildGraph clauses in

  (* We don't handle cyclic graphs. *)
  assert (not (Traverser.has_cycle g));

  (* Generate constraints for solving the graph. *)
  let sol =
    addRoot g |>
    solveGraph |>
    M.map (fun (exprs) ->
      (* TODO: Predicate parameters. *)
      (assert false),
      (And (List.map (fun x -> Expr x) exprs))) in

  (* Rename back to original predicate variable names. *)
  M.fold (fun k -> M.add (M.findDefault k k pm)) sol M.empty

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
