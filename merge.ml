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

let rec f2 f a b c = function
  | d::e ->
    if reduce max b < List.hd d then
      f (a @ [b] @ c @ [d] @ e) (a @ [b @ d] @ c @ e) b d;
    f2 f a b (c @ [d]) e
  | [] -> ()

let rec f1 f a = function
  | b::c ->
    if not (List.exists (fun x -> List.length x <> 1) c) then
      f2 f a b [] c;
    f1 f (a @ [b]) c
  | [] -> ()

module Merger(X: Map.OrderedType) = struct
  module Key = struct
    type t = (int * X.t) list list
    let compare = compare (fun (a, _) (b, _) -> a - b)
  end

  module ResultKey = struct
    type t = X.t list list
    let compare = compare X.compare
  end

  module MK = MapEx.Make(Key)
  module MR = MapEx.Make(ResultKey)

  let rec merge eval n input =
    if n = 0 || MK.cardinal input = 0 then input else (
    let next = ref MK.empty in
    MK.iter (fun k _ ->
      f1 (fun origin current m1 m2 ->
        match eval (MK.find origin input) current m1 m2 with
          | Some x -> next := MK.add current x !next
          | None -> ()) [] k) input;
    merge eval (n - 1) !next)

  let merge_twoLists dft merger ((a, la), (b, lb)) =
    assert (la > 0);
    let a' = mapi (fun i x -> [i, x]) a in
    let b' = mapi (fun i x -> [i + la, x]) b in
    let [b_hd]::_ = b' in
    let input = a' @ b' in

    let check =
      if la < lb then
        fun current _ m2 ->
          if List.hd m2 < b_hd then false
          else List.fold_left (fun r x ->
            if List.hd x < b_hd then
              if List.length x = 1 then r + 1 else r
            else r - 1) 0 current <= 0
      else (* la = lb *)
        fun _ m1 m2 ->
          match m1, m2 with
            | [m1, _], [m2, _] -> m1 < la && m2 >= la
            | _ -> false in

    let merger originVal current m1 m2 =
      if check current m1 m2 then
        merger originVal
          (List.map (List.map snd) current)
          (List.map snd m1) (List.map snd m2)
      else None in

    let output = merge merger lb (MK.add input dft MK.empty) in
    MK.fold (fun k -> MR.add (List.map (List.map snd) k)) output MR.empty

  let merge_twoLists dft merger a b =
    let [la;lb] = List.map List.length [a;b] in
    let a, b = (a, la), (b, lb) in
    merge_twoLists dft merger (if la > lb then b, a else a, b)

end
