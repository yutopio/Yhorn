open Error
open Expr
open Formula
open ListEx
open MapEx
open MTypes
open Types
open Util

let createRename = List.fold_left2 (fun m k v -> M.add k v m) M.empty

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

let buildGraph clauses =
  let bot = LinearExpr (Term (LTE, M.add Id.const 1 M.empty)) in
  let (cs_p, cs_l) =
    List.map (fun (lh, rh) ->
      List.map (fun lh -> lh, rh) (preprocLefthand lh)) clauses |>
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
  let predVertices = List.fold_left (fun vp ((lh, _), rh) ->
    let vp =
      match rh with
      | PredVar pvar -> addVp true vp pvar
      | _ -> vp in
    List.fold_left (addVp false) vp lh) M.empty clauses in

  (* Add implication relations on the Horn graph. *)
  let v_bot = G.V.create (HT bot) in
  List.fold_left (fun g ((pvars, la) as lh, rh) ->
    let (pvars, la), src =
      match rh with
      | PredVar (p, binder) ->
        let src = M.find p predVertices in
        let HT (PredVar (p', binder')) = G.V.label src in assert (p = p');
        let rename = ref (createRename binder binder') in
        ((List.map (fun (p, args) -> p, renameList rename args) pvars),
        (maybeApply (Formula.map (renameExpr rename)) la)), src
      | LinearExpr _ -> lh, v_bot in

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
    g) predVertices

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

let findRoot g =
  assert (not (G.is_empty g));

  let roots = G.fold_vertex (fun v s ->
    if G.in_degree g v = 0 then SV.add v s else s) g SV.empty in

  let _, root as ret =
    if SV.cardinal roots = 1 then
      g, (SV.choose roots)
    else
      let arrow = G.V.create Arrow in
      let root = G.V.create (HT (LinearExpr (Term (LTE, M.empty)))) in
      let g =
        G.add_edge g root arrow |>
        SV.fold (fun v g -> G.add_edge g arrow v) roots
      in
      g, root
  in

  rootE := G.E.create root None root;
  ret

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

let solveGraph (g, root) =
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

  (* For simplification purpose, travese the component link graph and compute
     appropriate quantifiers. *)
  let (fvs, use) = List.fold_left (fun (fvs, use) x ->
    let v = MI.find x roots in
    let fv =
      match G.V.label v with
      | HT (PredVar (p, param)) -> M.find p templ |> M.values
      | _ -> [] in
    let use' = fv @ (MI.findDefault [] x use |> List.sort_distinct Id.compare) in
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
    MI.add x (List.sort_distinct Id.compare (l1 @ l2 @ l3)) quant
  ) MI.empty (List.rev linkOrder) in

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

  (* Compute at each vertex linear expressions those are ancestors of it. *)
  let rec computeAncestors templs v e g =
    if MV.mem v templs then
      (* If the vertex is already registered in the template list, it is a
         forking predicate variable node. *)
      let deltaMap, defDelta, dup = MV.find v templs in

      (* If the predicate is specified for duplication, rename it. *)
      let pcoef, constrs =
        try duplicate (ME.find e deltaMap)
        with Not_found -> (if dup then duplicate else id) defDelta
      in

      if dup then
        let constrs = List.map (fun ((es, a), b) ->  (e :: es, a), b) constrs in
        MV.add v [e, (pcoef, constrs)] MV.empty
      else
        let exprs = List.map snd constrs |> List.reduce (&&&) in
        (* TODO: Simplification based on quantifiers *)
        MV.add v [e, (pcoef, [([], Simplified v), exprs])] MV.empty
    else
      let x = G.fold_succ_e (fun e () ->
        let arrow = G.E.dst e in
        let ret, constrs, (m, pis) =
          G.fold_succ_e (fun e (ret, constrs, (m, pis as m_pis)) ->
            let u = G.E.dst e in
            match G.E.label e, G.V.label u with
            | None, HT (LinearExpr ex) ->
              (* TODO: Optimization *)
              let [x] = Nf.dnf_of_formula ex in
	      assert (pis = []);
              let x = List.map snd x in
              let m_pis = List.fold_left (addLinear (Some e)) m_pis x in

              (* No renaming should occur for linear expressions. *)
              ret, constrs, m_pis

            | Some rename, HT (PredVar (p, param)) ->
              let ret' = computeAncestors templs u e g in

              (* TODO: We should consider disjunctive templates. *)
              let [_, (pcoef, constr)] = MV.find u ret' in

              (* Merging returning template. *)
              let ret = MV.merge (fun _ -> maybeAdd (@)) ret ret' in
              let constrs = constr @ constrs in

              let rename = ref rename in
              let f k v = addPcoef (Some e) (renameVar rename k) (v, 1) in

              (* Building an coefficient mapping in terms of variables. *)
              ret, constrs, ((M.fold f pcoef m), pis)

            | _ -> assert false
          ) g arrow (MV.empty, [], (M.empty, [])) in

        let m, pcoef, la =
          match G.V.label v with
          | HT (LinearExpr _) -> (* bot *)
	    m, M.empty, true
          | HT (PredVar (p, param)) ->
            (* Add the atomic current predicate template for Farkas' target. *)
            let pcoef = M.find p templ in
            let m = M.fold (fun k v -> addPcoef None k (v, -1)) pcoef m in
            m, pcoef, false
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
            constr :: c) m in

        ignore(MV.add v [e, (pcoef, constrs)] ret)
      ) g v () in

      assert false
  in

  (* Create templates and constraints for all predicate variables over the
     graph. *)
  let rootTempls =
    List.fold_left (fun templ (root, g) ->
      let templ' = computeAncestors (MV.map fst templ) root !rootE g in

      let [_, (pcoef, constrs)] = MV.find root templ' in

      MV.add root ((ME.empty, (pcoef, constrs), false), templ') templ
    ) MV.empty components in

  (* Generate split tree. *)
  let rootV = GV.V.create root in
  let st = GV.add_vertex GV.empty rootV in

  let trySolve st =
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

      let predTempls =
        let roots = List.map fst components in
        let keys = List.take (List.index_of v' roots) roots in
        MV.map fst rootTempls |>
        MV.filter (fun k _ -> List.mem k keys) in

      let me = ME.fold (fun e l me ->
        let templs =
          List.fold_left (fun mv (v, me) ->
            (* NOTE: The same v won't appear more than once. *)
            let (_, templ, _) = MV.find v mv in
            let me = ME.map fst me in
            MV.add v (me, templ, true) mv
          ) predTempls l in

        assert (not (MV.mem v' templs));
        let templ' = computeAncestors templs v' e g' in

        let [_, (pcoef, constr)] = MV.find v' templ' in

        ME.add e ((pcoef, constr), templ') me) me ME.empty in
      MVV.add v me mvv
    in

    let constrTree = step rootV in
    let rec step v (op, coef) first =
      let f v =
        let (_, x, _), templ = MV.find v rootTempls in
        v, (x, templ), MV.empty in
      let v, ((pcoef, constrs), templ), subprobl =
        match v with
        | `A (e, vv) ->
          let c = MVV.find vv constrTree in
          let v = GV.V.label vv in (
            try
              v,
              ME.find e c,
              GV.fold_succ_e (fun e' m ->
                if GV.E.label e' = e then
                  let u = GV.E.dst e' in
                  MV.add (GV.V.label u) (u, MVV.find u constrTree) m
                else m) st vv MV.empty
            with Not_found -> f v)
        | `B v -> f v in

      let constr =
        (* TODO: Parameterized operator. *)
        M.merge (fun _ p v ->
          match p, v with
          | None, None -> assert false
          | None, Some 0 -> None
          | None, Some v -> failwith no_sol
          | Some p, None
          | Some p, Some 0 -> Some (Term (EQ, M.add p 1 M.empty))
          | Some p, Some v ->
            Some (Term (EQ, M.add p 1 (M.add Id.const (-v) M.empty)))
        ) pcoef coef |>
        M.values in
      let constrs =
        if List.length constr = 0 then constrs
        else (([], Binding), And constr) :: constrs in

      let split_tag =
        List.fold_left (fun (constrs, m) (tag, ex) ->
          let name = string_of_int (List.length m) in
          (name, ex) :: constrs,
          (name, tag) :: m) ([], []) in

      (* Once the root constraint become satisfiable, all subproblems
         should have a solution. *)
      let constrs, symbol_map = split_tag constrs in
      let sol =
        try Z3interface.solve constrs
        with Z3interface.Unsatisfiable x ->
          let uc_tags = List.map (fun x -> List.assoc x symbol_map) x in
          raise (Unsatisfiable (List.sort_distinct compare uc_tags)) in

      MV.fold (fun k pexprs sols ->
        match G.V.label k; assert false with
        | LinearExpr _ -> sols
        | PredVar (p, param) ->
          List.fold_left (fun (params, predSol) (e, (pcoef, _)) ->
            let params =
              try assert (param = M.find p params); params
              with Not_found -> M.add p param params in
            let pcoef = M.map (fun x -> M.add x 1 M.empty) pcoef in
            let expr = LTE, (assignParameters sol pcoef) in
            let predSol = M.addDefault [] (fun a b -> b :: a) p expr predSol in

            if k <> v && List.mem_assoc k components then
              (* This vertex is a cutpoint. *)
              let params', predSol' =
                try
                  let vv, _ = MV.find k subprobl in
                  step (`A (e, vv)) expr false
                with Not_found -> step (`B k) expr false in
              (M.merge (fun _ -> maybeAdd (
                fun x y -> assert (x = y); x)) params params'),
              (M.merge (fun _ -> maybeAdd (@)) predSol predSol')
            else params, predSol
          ) sols pexprs
      ) templ (M.empty, M.empty) in
    step (`A (!rootE, rootV)) (LTE, M.empty) true in

  let rec step st =
    try
      trySolve st
    with Unsatisfiable x ->
      let m = List.fold_left (fun m (ges, tag) ->
        MEL.addDefault [] (fun a b -> b :: a) ges tag m
      ) MEL.empty x in

      let keys = MEL.fold (fun k _ s ->
        let x = List.rev k in
        match SEL.split k s with
        | _, true, _ -> s
        | sl, _, sr ->
          let ret =
            if SEL.is_empty sl then None
            else
              let slx = SEL.max_elt sl in
              if not (List.starts_with slx x) then None
              else Some (SEL.remove slx s |> SEL.add x) in
          match ret with
          | Some x -> x
          | None ->
            if SEL.is_empty sr then SEL.add x s
            else
              let srx = SEL.min_elt sr in
              if List.starts_with srx x then s
              else SEL.add x s) m SEL.empty in
      let keys = SEL.fold (fun x l -> List.rev x :: l) keys [] in

      let edge_check el dst e =
        GV.E.label e = el && GV.V.label (GV.E.dst e) = dst in

      let changed = ref false in
      let rec grow st x v = function
        | a::b::rest ->
          let v' =
            GV.succ_e st v |>
            List.filter (edge_check a (G.E.dst b)) |>
            List.hd |>
            GV.E.dst in
          grow st x v' (b::rest)
        | [e] ->
          if GV.succ_e st v |> List.exists (edge_check e x) then
            st (* Do nothing. *)
          else (
            changed := true;
            GV.add_edge_e st (GV.E.create v e (GV.V.create x))) in

      let f_key st key =
        (* Traverse st based on key. *)
        let path = (!rootE :: key) in
        let f_dst st dst = grow st dst rootV path in

        MEL.find key m |>
        List.fold_left (fun m ->
          function
          | Coef es -> List.fold_left (fun m e ->
            MV.addDefault 0 (+) (G.E.dst e) 1 m) m es
          | _ -> m) MV.empty |>
        MV.filter (fun k v -> v > 1 && List.mem_assoc k components) |>
        MV.keys |>
        List.fold_left f_dst st in
      let st = List.fold_left f_key st keys in
      if not !changed then raise No_growth;
      step st in
  step st

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
  let g = buildGraph clauses in

  (* We don't handle cyclic graphs. *)
  assert (not (Traverser.has_cycle g));

  (* Generate constraints for solving the graph. *)
  let g, root = findRoot g in

  let params, exprs = solveGraph (g, root) in
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
