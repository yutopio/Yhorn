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
      if (compare !current x) < 0 then (current := x; f x)
      else assert false);
    f2 f a b (c @ [d]) e
  | [] -> ()

let rec f1 f a = function
  | b::c ->
    if List.fold_left (fun f c -> f && List.length c = 1) true c then
      f2 f a b [] c;
    f1 f (a @ [b]) c
  | [] -> ()

let rec merge input =
  if List.length input = 0 then () else (
  print_endline "***";
  let next = ref [] in
  List.iter (fun x -> dump x; f1 (fun x -> next := x :: !next) [] x) input;
  merge (List.rev !next))

let merge_main () =
  let x = int_of_string (read_line ()) in
  current := repeat (fun i r -> [i] :: r) x [];
  merge [ !current ]
