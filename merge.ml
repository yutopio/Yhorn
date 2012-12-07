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

let rec f2 f a b c = function
  | d::e ->
    if reduce max b < List.hd d then
      f (a @ [b @ d] @ c @ e) b d;
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
    if check current m1 m2 then
      next := current :: !next) []) input;
  merge check (n - 1) (List.rev !next))

let rec merge_objLists a b =
  let [la;lb] = List.map List.length [a;b] in
  if la > lb then merge_objLists b a else (

  assert (la > 0);
  let a' = mapi (fun i x -> [i, x]) a in
  let b' = mapi (fun i x -> [i + la, x]) b in
  let [b_hd]::_ = b' in
  let input = a' @ b' in

  let check =
    if la < lb then fun current _ m2 ->
      if List.hd m2 < b_hd then false
      else List.fold_left (fun r x ->
        if List.hd x < b_hd then
          if List.length x = 1 then r + 1 else r
        else r - 1) 0 current <= 0
    else (* la = lb *) fun _ m1 m2 ->
      match m1, m2 with
        | [m1, _], [m2, _] -> m1 < la && m2 >= la
        | _ -> false in

  let output = merge check lb [ input ] in
  List.map (List.map (List.map (fun (_, x) -> x))) output)
