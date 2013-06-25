open ListEx
open Types
open Util

type template = int list

let size_of_nf x = List.fold_left (fun ret x -> ret + List.length x) 0 x
let template_of_nf x = List.sort compare (List.map List.length x)
let size_of_tmpl = List.reduce (+)

let print_template tmpl = String.concat "," (List.map string_of_int tmpl)

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
  let clauses = List.mapi (fun i x -> List.length x, Clause x) nf in

  let x =
    List.stable_sort (fun (x, _) (y, _) -> x - y) (comp @ clauses) |>
    List.split |> snd in

  (* Ready for distribution tricks. *)
  let rec choose (vacant, clausesLeft,
                  choosingVacant, templs, assigns) = function
    | [] ->
      if vacant == 0 then f assigns
    | Template (size, indices) :: rest ->
      if not choosingVacant then
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
            if rest' = [] then MI.remove k
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

type 'a t2 =
  | Placeholder of int
  | Pexpr of 'a

let rec unify_template unifier f value templ apps = function
  | x::rest ->
    enumerate_application (fun app ->
      unify_template unifier f value templ (app @ apps) rest
    ) templ x
  | [] ->
    let m = List.fold_left (fun m (k, v) ->
      MI.addDefault [] (fun l x -> x::l) k v m) MI.empty apps |>
      MI.bindings in
    let rec f_ value built = function
      | [] -> f value built
      | (x, clauses) :: rest ->
        let size = List.nth templ x in
        let places = repeat (fun j k -> (Placeholder (size-j))::k) size [] in

        let rec g_ apps = function
          | clause :: rest ->
            List.map (fun x -> Pexpr x) clause |>
            Combine.lists places |>
            List.map (
              List.map (fun ((Placeholder y)::terms) ->
                List.map (fun (Pexpr pexpr) -> y, pexpr) terms) |-
              List.flatten) |>
            List.iter (fun x -> g_ (x @ apps) rest)
          | [] ->
            let m = List.fold_left (fun m (k, v) ->
              MI.addDefault [] (fun l x -> x::l) k v m) MI.empty apps in
            let value =
              try Some (MI.fold (fun _ -> unifier) m value)
              with Not_found -> None in
            match value with
              | Some value -> f_ value ((MI.map List.hd m |>
		  MI.bindings |> List.split |> snd) :: built) rest
              | None -> () in
        g_ [] clauses in
    f_ value [] m
let unify_template a b c d = unify_template a b c d []

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
  if i > max then None
  else
    let seed = repeat (fun _ l -> 1::l) i [] in
    let rec g current =
      match f current with
        | Some x as sol -> sol
        | None ->
          let next =
            try Some (incr_tmpl current)
            with Not_found -> None in
          match next with
            | Some x -> g x
            | None -> repeat_tmpl f (i + 1) max in
    g seed

exception Stop
let unify unifier value ?tmpl ?maxSize nfs =
  let ret = ref ([], value) in
  let try_template templ =
    try unify_template unifier (fun x y ->
      ret := (y, x); raise Stop
    ) value templ nfs; None
    with Stop -> Some !ret in

  let maxSize =
    match maxSize with
      | Some x -> x
      | None -> List.reduce min (List.map size_of_nf nfs) in
  match tmpl with
    | Some x ->
      if size_of_tmpl x > maxSize then None else try_template x
    | None ->
      repeat_tmpl try_template 1 (maxSize + 1)
