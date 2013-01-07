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

module M = MapEx.Make(MyIntListList)

let check input a b c d e =
  let c = List.map (fun x -> List.hd x, x) c in
  let rec choose (bi, bl as b) (di, dl as d) = function
    | x::rest ->
      (choose (x, x::bl) d rest) &&
      (choose b (x, x::dl) rest)
    | [] ->
      bi < 0 || di < 0 || (
      List.sort (fun (x,_) (y,_) -> x-y) ([b;d] @ c) |>
      List.split |> (fun (_,x) -> M.mem (a @ x @ e) input)) in
  choose (-1, []) (-1, d) (List.rev b)

let rec f2 f a b c = function
  | d::e ->
    if List.fold_left (fun m x -> max m x) 0 b < List.hd d then
      f (a @ [b] @ c @ [d] @ e) (a @ [b @ d] @ c @ e) a b c d e;
    f2 f a b (c @ [d]) e
  | [] -> ()

let rec f1 f a = function
  | b::c ->
    if not (List.exists (fun x -> List.length x <> 1) c) then
      f2 f a b [] c;
    f1 f (a @ [b]) c
  | [] -> ()

let rec combine eval n input =
  if n = 0 || M.cardinal input = 0 then input else (
    let next = ref M.empty in
    M.iter (fun k _ ->
      f1 (fun x y a b c d e ->
        if check input a b c d e then
          match eval input x y a b c d e with
            | Some z -> next := M.add y z !next
            | None -> ()) [] k) input;
    combine eval (n - 1) !next)

let convL x = List.map x
let convLL x = List.map (convL x)
let convM x = M.bindings |- List.map (fun (k, v) -> convLL x k, v)

let combine lookup eval n input seed =
  combine eval n (M.add input seed M.empty) |> convM lookup

let create_lookup x =
  let (_, (input, map)) = List.fold_left (fun (i, (l, map)) x ->
    i + 1, ([i] :: l, MI.add i x map)) (0, ([], MI.empty)) x in
  (List.rev input), (fun x -> MI.find x map)

let lists seed eval ((a, la), (b, lb)) =
  assert (la > 0);
  let input, lookup = create_lookup (a @ b) in

  let check =
    if la < lb then
      fun current _ m2 ->
        if List.hd m2 < la then false
        else List.fold_left (fun r x ->
          if List.hd x < la then
            if List.length x = 1 then r + 1 else r
          else r - 1) 0 current <= 0
    else (* la = lb *)
      fun _ m1 m2 ->
        match m1, m2 with
          | [m1], [m2] -> m1 < la && m2 >= la
          | _ -> false in

  (* I admit that this code is stupid... *)
  let convL, convLL = convL lookup, convLL lookup in
  let eval input x y a b c d e =
    if check y b d then
      eval (M.find x input) (convLL a) (convL b) (convLL c) (convL d) (convLL e)
    else None in

  combine lookup eval lb input seed

(* Below are exposed functions. *)

let elements seed eval a n =
  let input, lookup = create_lookup a in
  let convL, convLL = convL lookup, convLL lookup in
  let eval input x _ a b c d e =
    eval (M.find x input)
      (convLL a) (convL b) (convLL c) (convL d) (convLL e) in
  combine lookup eval n input seed

let lists seed eval a b =
  (* Gurantee that a is shorter (or equal-length) than b. *)
  let [la;lb] = List.map List.length [a;b] in
  let a, b = (a, la), (b, lb) in
  lists seed eval (if la > lb then b, a else a, b)
