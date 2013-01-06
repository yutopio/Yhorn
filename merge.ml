open Util
open Types

let compare compare x y =
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

let combinationCheck lookup f a b c d e =
  let rec choose f a ((bi, bl) as b) c ((di, dl) as d) e = function
    | (i,x)::rest ->
      (choose f a (i, x::bl) c d e rest) &&
      (choose f a b c (i, x::dl) e rest)
    | [] ->
      bi < 0 || di < 0 || (
      List.sort (fun (x,_) (y,_) -> x-y) ([b;d] @ c) |>
      List.split |> (fun (_,x) -> f (a @ x @ e))) in
  let b' = List.map (fun x -> lookup x, x) b in
  let c' = List.map (fun x -> (List.hd x |> lookup), x) c in
  choose f a (-1, []) c' (-1, d) e (List.rev b')

let rec f2 l f a b c = function
  | d::e ->
    if List.fold_left (fun m x -> max m (l x)) 0 b < l (List.hd d) then
      f (a @ [b] @ c @ [d] @ e) (a @ [b @ d] @ c @ e) a b c d e;
    f2 l f a b (c @ [d]) e
  | [] -> ()

let rec f1 l f a = function
  | b::c ->
    if not (List.exists (fun x -> List.length x <> 1) c) then
      f2 l f a b [] c;
    f1 l f (a @ [b]) c
  | [] -> ()

module Merger(X: Map.OrderedType) = struct
  module Key = struct
    type t = X.t list list
    let compare = compare X.compare
  end

  module MX = MapEx.Make(X)
  module M = MapEx.Make(Key)

  let rec merge lookup eval n input =
    if n = 0 || M.cardinal input = 0 then input else (
    let next = ref M.empty in
    M.iter (fun k _ ->
      f1 lookup (fun x y a b c d e ->
        if combinationCheck lookup (
          fun x -> M.mem x input) a b c d e then
          match eval input x y a b c d e with
            | Some z -> next := M.add y z !next
            | None -> ()) [] k) input;
    merge lookup eval (n - 1) !next)

  let create_lookup x =
    let (_, (input, map)) = List.fold_left (fun (i, (l, map)) x ->
      i + 1, ([x] :: l, MX.add x i map)) (0, ([], MX.empty)) x in
    (List.rev input), (fun x -> MX.find x map)

  let merge_twoLists seed merger ((a, la), (b, lb)) =
    assert (la > 0);
    let input, lookup = create_lookup (a @ b) in

    let check =
      if la < lb then
        fun current _ m2 ->
          if lookup (List.hd m2) < la then false
          else List.fold_left (fun r x ->
            if lookup (List.hd x) < la then
              if List.length x = 1 then r + 1 else r
            else r - 1) 0 current <= 0
      else (* la = lb *)
        fun _ m1 m2 ->
          match m1, m2 with
            | [m1], [m2] -> lookup m1 < la && lookup m2 >= la
            | _ -> false in

    let merger input x y a b c d e =
      if check y b d then
        merger input x y a b c d e
      else None in

    merge lookup merger lb (M.add input seed M.empty)

  let merge seed merger a n =
    let input, lookup = create_lookup a in
    merge lookup merger n (M.add input seed M.empty)

  let merge_twoLists seed merger a b =
    (* Gurantee that a is shorter (or equal-length) than b. *)
    let [la;lb] = List.map List.length [a;b] in
    let a, b = (a, la), (b, lb) in
    merge_twoLists seed merger (if la > lb then b, a else a, b)

end
