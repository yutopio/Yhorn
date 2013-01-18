open Types
open Util

type template = int list

let size_of_nf = List.fold_left (fun ret x -> ret + List.length x) 0
let template_of_nf x = List.sort compare (List.map List.length x)
let size_of_tmpl = reduce (+)

let apply_template tmpl pexprNf =
  assert (List.length tmpl <= List.length pexprNf);
  Combine.lists
    (List.map (fun x -> `A x) tmpl)
    (List.map (fun x -> `B (List.map (fun x -> `D x) x)) pexprNf) |>
  List.fold_left (fun l combs ->
    try
      (* NOTE: Because of the implementation of module Combine, the first
         element in this case must be a template and others are parameterized
         epxressions. *)
      (mapi (fun i comb ->
        let hd::clauses = comb in
        let x = match hd with `A x -> x | `B _ -> assert false in
        let ids = repeat (fun j k -> (`C (i+1, (x-j)))::k) x [] in

        List.map (function
          | `A _ -> assert false
          | `B clause ->
            if List.length clause < x then raise Not_found;
            Combine.lists ids clause |>
            List.map (
              List.map (fun comb ->
                let hd::terms = comb in
                let x, y = match hd with
                  | `C x -> x
                  | `D _ -> assert false in
                List.map (function
                  | `C _ -> assert false
                  | `D pexpr -> pexpr, x, y) terms) |-
              List.flatten)
        ) clauses |> (* combinations , choices , clauses *)
	directProduct |>
        List.map List.flatten) combs |>
      directProduct |>
      List.map List.flatten)
      @ l
    with _ -> l
  ) []

module MII = MapEx.Make(
  struct
    type t = int * int
    let compare = compare
  end)

let unify_template constr pnf tmpl =
  let apps = List.map (apply_template tmpl) pnf in
  let choices = directProduct apps in
  tryPick (fun choice ->
    let m = List.fold_left (List.fold_left (fun m (pexpr, x, y) ->
      MII.addDefault [] (fun l x -> x::l) (x, y) pexpr m)) MII.empty choice in
    try
      MII.fold (fun (x,y) pexprs () ->
        print_endline ("Unify [" ^ (string_of_int x) ^ "," ^ (string_of_int y) ^ "]: {" ^
          String.concat "}, {" (List.map printPexpr pexprs) ^ "}")) m ();
      print_newline ();

      Some (MII.fold (fun _ -> Unify.generatePexprUnifyConstr) m constr)
    with Not_found ->
      None
  ) choices

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
