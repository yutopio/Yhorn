open Util

module MyInt = struct
  type t = int
  let compare = compare
end

module MI = MapEx.Make(MyInt)

module MyIntListList = struct
  type t = int list list
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
end

module S = Set.Make(MyIntListList)

let rec f2 f a b c = function
  | d::e ->
    if List.fold_left (fun m x -> max m x) 0 b < List.hd d then
      f (a @ [b @ d] @ c @ e) b d;
    f2 f a b (c @ [d]) e
  | [] -> ()

let rec f1 f a = function
  | b::c ->
    if not (List.exists (fun x -> List.length x <> 1) c) then
      f2 f a b [] c;
    f1 f (a @ [b]) c
  | [] -> ()

let rec combine eval n input =
  if n = 0 || S.cardinal input = 0 then input else (
    let next = ref S.empty in
    S.iter (fun k ->
      f1 (fun y b d ->
        if eval y b d then next := S.add y !next) [] k) input;
    combine eval (n - 1) !next)

let convL x = List.map x
let convLL x = List.map (convL x)
let convM x = S.elements |- List.map (fun k -> convLL x k)

let combine lookup eval n input =
  combine eval n (S.add input S.empty) |> convM lookup

let create_lookup x =
  let (_, (input, map)) = List.fold_left (fun (i, (l, map)) x ->
    i + 1, ([i] :: l, MI.add i x map)) (0, ([], MI.empty)) x in
  (List.rev input), (fun x -> MI.find x map)

let lists ((a, la), (b, lb)) =
  assert (la > 0);
  let input, lookup = create_lookup (a @ b) in

  let check =
    if la < lb then
      fun current m1 m2 ->
        if List.hd m1 >= la || List.hd m2 < la then false
        else List.fold_left (fun r x ->
          if List.hd x < la then
            if List.length x = 1 then r + 1 else r
          else r - 1) 0 current <= 0
    else (* la = lb *)
      fun _ m1 m2 ->
        match m1, m2 with
          | [m1], [m2] -> m1 < la && m2 >= la
          | _ -> false in
  combine lookup check lb input

(* Below are exposed functions. *)

let elements a n =
  let input, lookup = create_lookup a in
  let eval _ _ _ = true in
  combine lookup eval n input

let lists a b =
  (* Gurantee that a is shorter (or equal-length) than b. *)
  let [la;lb] = List.map List.length [a;b] in
  let a, b = (a, la), (b, lb) in
  lists (if la > lb then b, a else a, b)

