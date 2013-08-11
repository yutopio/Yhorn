open Error
open Expr
open Formula
open ListEx
open MapEx
open MTypes
open Types
open Util

let bot = LinearExpr (Term (LTE, M.add Id.const 1 M.empty))

let createRename = List.fold_left2 (fun m k v -> M.add k v m) M.empty

let simplifyCNF clauses =
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
        | GT -> c > 0), exprs
    ) (false, []) in

  let contradiction, ret =
    List.fold_left (fun (contradiction, clauses) clause ->
      let tautology, exprs = simplifyDF clause in
      if tautology then contradiction, clauses
      else if contradiction || List.length exprs = 0 then true, []
      else false, (List.sort_distinct Expr.comp exprs) :: clauses
    ) (false, []) clauses in

  contradiction, List.sort_distinct (List.compare Expr.comp) ret

let preprocLefthand =
  Nf.dnf_of_formula |-
  List.map (fun x ->
    let pvars, la =
      List.fold_left (fun (pvars, la) ->
        function
        | LinearExpr x -> pvars, Some (
          let x = normalizeOperator x in
          match la with
          | None -> x
          | Some y -> x &&& y)
        | PredVar pvar -> (pvar :: pvars), la) ([], None) x in

    match la with
    | None -> [pvars, None]
    | Some la ->
      Nf.dnf_of_formula la |>
      List.map (fun x -> pvars, Some (And (List.map (fun x -> Term x) x)))) |-
  List.flatten

let buildGraph clauses =
  let (cs_p, cs_l) =
    List.map (fun (lh, rh) ->
      List.map (fun lh -> lh, rh) (preprocLefthand lh)) clauses |>
    (* TODO: Optimize starting here... *)
    List.flatten |>
    List.partition (fun (_, rh) ->
      match rh with
      | PredVar _ -> true
      | LinearExpr _ -> false) in

  (* Eliminate right-hand linear formula to contradiction. *)
  let cs_l =
    List.fold_left (fun ret ((pvars, la), LinearExpr e) ->
      normalizeOperator e |>
      Nf.cnf_of_formula |>
      simplifyCNF |>
      (function
      | true, _ -> [la]
      | false, exprs ->
        List.map (
          function
          | [] -> assert false
          | l ->
            let neg =
              match List.map (fun x -> Term (negateExpr x)) l with
              | [x] -> x
              | x -> And x in
            maybeAdd (&&&) la (Some neg)) exprs) |>
      List.map (fun la -> (pvars, la), bot) |>
      (@) ret) [] cs_l in
  let clauses = cs_p @ cs_l in
  (* TODO: Optimize ending here... *)

  (* Create predicate symbol vertices in advance. *)
  let addVp rh vp (p, l) =
    let ll = List.length l in
    if rh && ll <> List.length (List.distinct l) then
      (* The parameter definition has the same name variable in the list.
         e.g. x=0->A(x,x). is illegal. *)
      failwith illegal_binder
    else if M.mem p vp then (
      (* A predicate symbol which is implied in multiple Horn clauses should
         have the same arity across them. *)
      let HT (PredVar (p', l')) = M.find p vp |> G.V.label in assert (p = p');
      if ll <> List.length l' then
        failwith (invalid_arity p)
      else vp
    ) else
      (* Create a new predicate vertex and remember it. *)
      let binders = repeat (fun _ l -> (Id.create ()) :: l) ll [] |> List.rev in
      M.add p (G.V.create (HT (PredVar (p, binders)))) vp in

  (* Create vertices. *)
  (* TODO: Can be processed first for performance. *)
  let predVertices = List.fold_left (fun vp ((lh, _), rh) ->
    let vp =
      match rh with
      | PredVar pvar -> addVp true vp pvar
      | _ -> vp in
    List.fold_left (addVp false) vp lh) M.empty clauses in
  let preds = M.keys predVertices in

  (* Add implication relations on the Horn graph. *)
  let root = G.V.create (HT bot) in
  List.fold_left (fun g ((pvars, la) as lh, rh) ->
    let (pvars, la), src =
      match rh with
      | PredVar (p, binder) ->
        let src = M.find p predVertices in
        let HT (PredVar (p', binder')) = G.V.label src in assert (p = p');
        let rename = ref (createRename binder binder') in
        ((List.map (fun (p, args) -> p, renameList rename args) pvars),
        (maybeApply (Formula.map (renameExpr rename)) la)), src
      | LinearExpr _ -> lh, root in

    let arrow = G.V.create Arrow in
    let g = G.add_edge_e g (G.E.create src None arrow) in

    let dsts = List.fold_left (fun dsts (p, args) ->
      (* Get the predicate variable vertex and its binder. We will relate this
         vertex from newly-created predicate variable vertices that corrensponds
         to the application of such predicates. The edge will carry binding
         information. *)
      let dst = M.find p predVertices in
      let HT (PredVar (p', binder)) = G.V.label dst in assert (p = p');
      let rename = createRename binder args in

      (* Add a edge between origin *)
      (dst, Some rename) :: dsts
    ) [] pvars in

    (* If a linear expression exists on the left-hand, create a corresponding
       vertex. *)
    let dsts =
      match la with
      | None -> dsts
      | Some x ->
        let la = LinearExpr (Formula.map normalizeExpr x) in
        (G.V.create (HT la), None) :: dsts in

    (* Add edges between all left-hand terms and right-hand term. *)
    List.fold_left (fun g (dst, label) ->
      G.add_edge_e g (G.E.create arrow label dst)) g dsts
  ) G.empty clauses |>

  (* If a predicate variable does not have any assumption or any implication,
     assume Horn clause bot->P or P->top exists. *)
  M.fold (fun _ v g ->
    let HT (PredVar (_, binder)) = G.V.label v in
    let arity = List.length binder in
    let g =
      if G.in_degree g v = 0 then
        let dummy = repeat (fun _ k -> (Id.create ()) :: k) arity [] in
        let rename = Some (createRename binder dummy) in
        let top = G.V.create (HT (LinearExpr (Term (LTE, M.empty)))) in
        G.add_edge_e g (G.E.create top rename v)
      else g in
    let g =
      if G.out_degree g v = 0 then
        let bot = G.V.create (HT (LinearExpr (
          Term (LTE, M.add Id.const 1 M.empty)))) in
        G.add_edge_e g (G.E.create v None bot)
      else g in
    g) predVertices |>

  (* Return with the root and pred names. *)
  (fun g -> g, root, preds)

let rootE =
  let dummy = G.V.create (HT (LinearExpr (Term (EQ, M.empty)))) in
  ref (G.E.create dummy None dummy)
module EDef = struct
  type t = G.E.t
  let default = !rootE
  let compare x y = G.E.compare x y
end

module EL = struct
  type t = G.E.t list
  let default = []
  let compare = compare
end

module GI = Graph.Persistent.Digraph.Concrete(Integer)
module GV = Graph.Persistent.Digraph.AbstractLabeled(G.V)(EDef)
module MV = Map.Make(G.V)
module MVV = Map.Make(GV.V)
module ME = Map.Make(G.E)
module SEL = Set.Make(EL)
module MEL = Map.Make(EL)
module SV = Set.Make(G.V)
module TopologicalGI = Graph.Topological.Make(GI)

let assignParameters assign =
  M.map (fun v -> M.fold (fun k v -> (+) ((M.findDefault 1 k assign) * v)) v 0)

type constrTypes =
| LaWeight
| Coef of G.E.t list
| Simplified of G.V.t
| Binding
type constr = G.E.t list * constrTypes

exception Unsatisfiable of constr list
exception No_growth

let solveGraph (g, root) sol_templ =
  let cutpoints =
    G.fold_vertex (fun v s ->
      if G.in_degree g v > 1 then SV.add v s else s) g SV.empty in

  (* DEBUG: *)
  if !Flags.enable_gv then (
    Types.Display.highlight_vertices := cutpoints;
    display_with_gv (Operator.mirror g)
  );

  (* Create a template for all predicate variable vertices. *)
  let templ = G.fold_vertex (fun v m ->
    match G.V.label v with
    | HT (PredVar (p, param)) ->
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

  let addPcoef e =
    let add (es, m) (k, v) =
      (match e with None -> es | Some e -> e :: es),
      M.addDefault 0 (+) k v m in
    M.addDefault ([], M.empty) add in

  let addLinear e (m, pis) coef =
    (* Add to the variable maps for applying Farkas' Lemma. *)
    let pi = Id.create () in

    (* Building an coefficient mapping in terms of variables. *)
    (M.fold (fun k v -> addPcoef e k (pi, v)) coef m), pi :: pis in

  (* Duplicating templates is done by simple renaming. *)
  let duplicate (pcoef, constr) =
    let map = ref M.empty in
    M.fold (fun k v -> M.add k (renameVar map v)) pcoef M.empty,
    List.map (fun (x, y) -> x, Formula.map (renameExpr map) y) constr in

  let rec gen_constr ret v visited =
    if MV.mem v ret then
      (* If the vertex is already registered in the template list,
         simply return it. *)
      ret
    else
      let ret = G.fold_succ (fun arrow ret ->
        let ret, constrs, (m, pis) =
          G.fold_succ_e (fun e (ret, constrs, (m, pis as m_pis)) ->
            let u = G.E.dst e in
            match G.E.label e, G.V.label u with
            | None, HT (LinearExpr ex) ->
              (* TODO: Optimization *)
              let [x] = Nf.dnf_of_formula ex in
              assert (pis = []);
              let x = List.map snd x in (* Ignore LTE operator *)
              let m_pis = List.fold_left (addLinear (Some e)) m_pis x in

              (* No renaming should occur for linear expressions. *)
              ret, constrs, m_pis

            | Some rename, HT (PredVar (p, param)) ->
              let ret = gen_constr ret u visited in

              let constr = MV.find u ret in
              let constrs = constr @ constrs in

              let rename = ref rename in
              let f k v = addPcoef (Some e) (renameVar rename k) (v, 1) in

              (* Building an coefficient mapping in terms of variables. *)
              let pcoef = M.find p templ in
              ret, constrs, ((M.fold f pcoef m), pis)

            | _ -> assert false
          ) g arrow (ret, [], (M.empty, [])) in

        let m, la, quants =
          match G.V.label v with
          | HT (LinearExpr _) -> (* bot *)
	    m, true, []
          | HT (PredVar (p, param)) ->
            (* Add the atomic current predicate template for Farkas' target. *)
            let pcoef = M.find p templ in
            let m = M.fold (fun k v -> addPcoef None k (v, -1)) pcoef m in
            m, false, M.values pcoef
	  | _ -> assert false in

        let constrs =
          (* All left-hand linear inequalities must be weighted non-negative. *)
          List.map (fun pi ->
            (([], LaWeight), Term (GTE, M.add pi 1 M.empty))) pis |>

          (* Additionally, add constraints to make totals on every
             coefficients zero. *)
          M.fold (fun k (edges, coefs) c ->
            let op = if k = Id.const then if la then GT else GTE else EQ in
            let constr = ([], Coef edges), Term (op, coefs) in
            constr :: c) m |>

          (* Add constraints from predecessors. *)
          (@) constrs
        in

        MV.add arrow constrs ret
      ) g v ret in

    let constrs = G.fold_succ (fun arrow -> (@) (MV.find arrow ret)) g v [] in

    let quants =
      match G.V.label v with
      | HT (LinearExpr _) -> (* bot *) []
      | HT (PredVar (p, param)) -> M.find p templ |> M.values
      | _ -> assert false
    in

    let constr =
      if SV.mem v visited then
        (* No simplification. *)
        constrs
      else
        let quants = List.fold_left (fun a b -> S.add b a) S.empty quants in
        let constrs =
          And (List.map snd constrs) |>
          AtpInterface.integer_qelim quants in
        [([], Simplified v), constrs]
    in

    MV.add v constr ret
  in

  let visited = SV.add root SV.empty in
  let constrs = gen_constr MV.empty root visited in

  (* Initialize incremental check tree. *)
  let gen = G.add_vertex G.empty root in

  let split_tag =
    List.fold_left (fun (constrs, m) (tag, ex) ->
      let name = string_of_int (List.length m) in
      (name, ex) :: constrs,
      (name, tag) :: m) ([], []) in

  let root_constrs, symbol_map = MV.find root constrs |> split_tag in
  let sol =
    try Z3interface.solve root_constrs
    with Z3interface.Unsatisfiable x ->
      let uc_tags = List.map (fun x -> List.assoc x symbol_map) x in
      let unsat = List.sort_distinct compare uc_tags in
      assert false in
  assert false

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
  List.fold_left (fun (clauses, pm) clause ->
    let exec f (lh, rh) =
      let lh' = Formula.map f lh in
      let rh' = f rh in
      lh', rh' in

    let vm = ref M.empty in
    let pm = ref pm in
    let f = function
      | PredVar (p, l) ->
        let def = Id.from_string ("P" ^ string_of_int (M.cardinal !pm)) in
        let p' = M.findDefault def p !pm in
        pm := M.add p p' !pm;
        ignore(renameList vm l);
        PredVar (p', l)
      | LinearExpr e ->
        ignore(Formula.map (renameExpr vm) e);
        LinearExpr e in
    let clause = exec f clause in

    let i = ref 0 in
    let new_name _ = Id.from_string ("x" ^ string_of_int (incr i; !i)) in
    vm := M.map new_name !vm;

    let clause = exec (renameHornTerm vm) clause in
    clause :: clauses, !pm
  ) ([], M.empty)

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
  let g, root, preds = buildGraph clauses in
  rootE := G.E.create root None root;

  (* We don't handle cyclic graphs. *)
  assert (not (Traverser.has_cycle g));

  (* Create basic template for solution. *)
  let sol_templ = List.fold_left (fun m k -> M.add k (Term k) m) M.empty preds in

  (* Generate constraints for solving the graph. *)
  let params, exprs = solveGraph (g, root) sol_templ in
  let sol = M.merge (fun _ (Some param) (Some exprs) ->
      Some (param, (And (List.map (fun x -> Term x) exprs)))) params exprs in

  (* Rename back to original predicate variable names and simplify. *)
  let sol =
    M.fold (fun k -> M.add (M.findDefault k k pm)) sol M.empty |>
    M.map (fun (p, f) -> p,
      let (contradiction, cnf) = Nf.cnf_of_formula f |> simplifyCNF in
      if contradiction then Term (NEQ, M.empty)
      else Nf.cnf_to_formula cnf)
  in

  (* DEBUG: Solution verification. *)
  List.iter (fun x ->
    print_endline (printHorn x);
    if not (Z3interface.check_clause sol x) then
      failwith incorrect) clauses;

  sol
