open Types
open Util

type template = int list

let size_of_nf = List.fold_left (fun ret x -> ret + List.length x) 0
let template_of_nf x = List.sort compare (List.map List.length x)
let size_of_tmpl = reduce (+)

type 'a t1 =
  | Template of int * (int * int) list
  | Clause of 'a list

let enumerate_application f templ nf =
  let comp =
    List.fold_left (fun (i, l) x -> i + 1,
      match l with
        | [] -> [x, [i,0]]
        | (j, l')::rest ->
          if j = x then (j, (i,0)::l')::rest
          else (x, [i,0])::l
    ) (0, []) templ |>
    snd |>
    List.rev |>
    List.map (fun (x, l) -> x, Template (x, List.rev l)) in
  let clauses = mapi (fun i x -> List.length x, Clause x) nf in

  (* NOTE: Assume List.sort uses a stablem sort algorithm. *)
  let x =
    List.sort (fun (x, _) (y, _) -> x - y) (comp @ clauses) |>
    List.split |> snd in

  (* Ready for distribution tricks. *)
  let rec choose (vacant, clausesLeft, choosingVacant, templs, assigns) = function
    | [] ->
      assert (vacant == 0);
      f assigns
    | Template (size, indices) :: rest ->
      assert (not choosingVacant);
      let vacant = vacant + List.length indices in
      let templs = MI.add size indices templs in
      choose (vacant, clausesLeft, false, templs, assigns) rest
    | Clause pexprs :: rest ->
      let chooseVacant = vacant = clausesLeft in
      let clausesLeft = clausesLeft - 1 in
      if chooseVacant then
        let templs =
          if not choosingVacant then
            MI.map (List.filter (fun (_, l) -> l = 0)) templs |>
            MI.filter (fun _ indices -> List.length indices <> 0) 
          else templs in
        MI.iter (fun k ((place,_)::rest') ->
	  let vacant = vacant - 1 in
          let assigns = (place, pexprs) :: assigns in
          let templs = (
            if rest = [] then MI.remove k
            else MI.add k rest') templs in
          choose (vacant, clausesLeft, true, templs, assigns) rest) templs
      else
        MI.iter (fun k indices ->
          let rec g finished = function
            | [] -> ()
            | (place, count)::rest' ->
              let assigns = (place, pexprs) :: assigns in
              let templs = MI.add k (
                finished @ ((place, count+1)::rest')) templs in
              if count = 0 then
                let vacant = vacant - 1 in
                choose (vacant, clausesLeft, false, templs, assigns) rest
              else (
                choose (vacant, clausesLeft, false, templs, assigns) rest;
                g (finished @ [place, count]) rest') in
          g [] indices) templs in

  choose (0, List.length nf, false, MI.empty, []) x

type t2 =
  | Placeholder of int
  | Pexpr of pexpr

let unify_template constr pnfs templ =
  List.map (fun pnf -> 
    let ret = ref [] in
    enumerate_application (fun app -> ret := app :: !ret) templ pnf;
    !ret) pnfs |>
  directProduct |>
  List.map (List.flatten) |>
  tryPick (fun choice ->
    let m = List.fold_left (fun m (k, v) ->
      MI.addDefault [] (fun l x -> x::l) k v m) MI.empty choice in
    try
      Some (MI.fold (fun x clauses constr ->
        let size = List.nth templ x in
        let places = repeat (fun j k -> (Placeholder (size-j))::k) size [] in

        let choices =
          List.map (
            List.map (fun x -> Pexpr x) |-
            Combine.lists places |-
            List.map (
              List.map (fun ((Placeholder y)::terms) ->
                List.map (fun (Pexpr pexpr) -> y, pexpr) terms) |-
              List.flatten)) clauses |>
          directProduct |>
          List.map List.flatten in

        let ret = tryPick (fun choice ->
          let m = List.fold_left (fun m (k, v) ->
            MI.addDefault [] (fun l x -> x::l) k v m) MI.empty choice in
          try
            Some (MI.fold (fun _ -> Unify.generatePexprUnifyConstr) m constr)
          with Not_found -> None) choices in

        match ret with
          | Some x -> x
          | None -> raise Not_found) m constr)
    with Not_found -> None)

let rec incr_tmpl = function
  | [] -> assert false
  | [_] -> raise Not_found
  | x::rest ->
    try x::(incr_tmpl rest)
    with Not_found ->
      let x = x + 1 in
      let y = size_of_tmpl rest - 1 in
      if y < x then [x+y]
      else
        let z = y mod x in
        repeat (fun _ l -> x::l) ((y-z)/x) [x+z]

let rec repeat_tmpl f i max =
  assert (max > 0);
  if i > max then None else
  try
    let seed = repeat (fun _ l -> 1::l) i [] in
    let rec g current =
      print_endline ("Template: " ^ String.concat "," (List.map string_of_int current));
      try
        let Some x as sol = f current in sol
      with _ -> g (incr_tmpl current) in
    g seed
  with Not_found -> repeat_tmpl f (i + 1) max

let unify constr ?tmpl ?maxSize pnf =
  (* DEBUG: *)
  print_endline "Try unify:";
  List.iter (fun x ->
    print_endline (printFormula printPexpr (convertToFormula true x))) pnf;
  print_newline ();

  let maxSize =
    match maxSize with
      | Some x -> x
      | None -> reduce min (List.map size_of_nf pnf) in
  match tmpl with
    | Some x ->
      if size_of_tmpl x > maxSize then None
      else unify_template constr pnf x
    | None ->
      repeat_tmpl (unify_template constr pnf) 1 (maxSize + 1)

let simplify constr ?tmpl ?maxSize t =
  match tmpl with
  | Some x -> (
    match maxSize with
    | Some y -> unify constr ~tmpl:x ~maxSize:y [t]
    | None -> unify constr ~tmpl:x [t])
  | None -> (
    match maxSize with
    | Some y -> unify constr ~maxSize:y [t]
    | None -> unify constr [t])
