open Util

let compare x y =
  match List.length y - List.length x with
    | 0 -> listFold2 (fun ret x y ->
      match ret with
        | 0 -> (
          let diff = List.length y - List.length x in
          let cmp = listFold2 (fun ret x y ->
            match ret with
              | 0 -> compare x y
              | _ -> ret) 0 in
          let x, y =
            if diff > 0 then x, take (List.length x) y
            else if diff = 0 then x, y
            else take (List.length y) x, y in
          match cmp x y with
            | 0 -> diff
            | ret -> ret)
        | _ -> ret) 0 x y
    | ret -> ret

let current = ref []

let dump =
  List.map (
    List.map string_of_int |-
    String.concat "," |-
    (fun x -> "(" ^ x ^ ")")
  ) |-
  String.concat "," |-
  print_endline

let rec f2 f a b c = function
  | d::e ->
    if (List.fold_left max 0 b) < List.hd d then (
      let x = a @ [b @ d] @ c @ e in
      if (compare !current x) < 0 then (current := x; f x b d)
      else assert false);
    f2 f a b (c @ [d]) e
  | [] -> ()

let rec f1 f a = function
  | b::c ->
    if not (List.exists (fun x -> List.length x <> 1) c) then
      f2 f a b [] c;
    f1 f (a @ [b]) c
  | [] -> ()

let rec merge check n input =
  if n = 0 || List.length input = 0 then input else (
  let next = ref [] in
  List.iter (f1 (fun current m1 m2 ->
    if check current m1 m2 then next := current :: !next) []) input;
  merge check (n - 1) (List.rev !next))

let merge_main () =
  let a = int_of_string (read_line ()) in
  let b = int_of_string (read_line ()) in
  let (a, b) = (min a b), (max a b) in

  let check current m1 m2 =
    if a < b then
      if List.hd m2 < a then false
      else List.fold_left (fun r x ->
	if List.hd x < a then
	  if List.length x = 1 then r + 1 else r
	else r - 1) 0 current <= 0
    else (* a = b *)
      match m1, m2 with
	| [m1], [m2] -> m1 < a && m2 >= a
	| _ -> false in

  current := repeat (fun i r -> [i] :: r) (a + b) [];
  let output = merge check b [ !current ] in
  List.iter dump output
