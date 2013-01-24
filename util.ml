let id x = x

(* DEBUG: Copied from util.ml in VHorn ****************************************)

(** compose operator *)
let (-|) f g x = f (g x)
let (-||) f g x y = f (g x y)

(** reverse compose operator *)
let (|-) f g x = g (f x)
let (||-) f g x y = g (f x y)

(** pipeline operator *)
let (|>) x f = f x

(******************************************************************************)

(** Apply a function to each element in the list and pick the first result that
    is not None. *)
let tryPick f = List.fold_left (fun ret x -> if ret = None then f x else ret) None

let _id = ref 0
let new_id () = incr _id; !_id
let reset_id () = _id := 0
let new_name () = "$" ^ string_of_int (new_id ())

let gcd x y =
  let rec gcd x y =
    if y = 0 then x
    else gcd y (x mod y) in
  assert (x <> 0 && y <> 0);
  let x = if x > 0 then x else -x in
  let y = if y > 0 then y else -y in
  if x > y then gcd x y else gcd y x
let lcm x y = x * y / gcd x y

let distinct l =
    let rec internal l = function
        | x :: rest ->
            internal (l @ (if List.mem x l then [] else [x])) rest
        | [] -> l in
    internal [] l

let sorted_distinct l =
  List.rev (
    let rec f ret = function
      | [] -> ret
      | [x] -> x::ret
      | x::y::z -> f (if x = y then ret else x::ret) (y::z) in
    f [] l)

(** [reduce f [ x1 ; x2 ; ...; xn] ] returns f ... (f (f x1 x2) x3) ... xn. *)
let reduce f = function
    | x :: rest -> List.fold_left f x rest
    | _ -> assert false

(** Gets the all possible combinations of elements each of those are chosen from
    every list. For example, [directProduct [[A;B]; [C;D]] ] returns [ [A;C];
    [A;D]; [B;C]; [B;D] ]. *)
let directProduct input =
    let ret = ref [] in
    let rec inner current = function
        | [] -> ret := current :: !ret
        | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

let fold2 fold_left indexer f x a =
    let i = ref (-1) in
    fold_left (fun x -> f x (indexer a (incr i; !i))) x

let arrayFold2 a = fold2 Array.fold_left (fun a x -> a.(x)) a
let listFold2 a = fold2 List.fold_left List.nth a

let zip a =
    let a = ref a in
    List.map (fun y ->
        match !a with
        | x::rest -> a := rest; (x,y)
        | _ -> assert false)

let rec skip n x =
    assert (n >= 0);
    if n = 0 then x
    else match x with
        | [] -> []
        | a :: rest -> skip (n - 1) rest

let take n x =
    assert (n >= 0);
    let rec internal n x ret =
        if n = 0 then List.rev ret
        else match x with
            | [] -> ret
            | a :: rest -> internal (n - 1) rest (a :: ret) in
    internal n x []

let splitByN n x =
    assert (n > 0);
    let rec internal1 x ret =
        let rec internal2 n x ret =
            if n = 0 then (List.rev ret), x
            else match x with
                | [] -> ret, []
                | a :: rest -> internal2 (n - 1) rest (a :: ret) in
        let group, rest = internal2 n x [] in
        match rest with
        | [] -> List.rev (group :: ret)
        | _ -> internal1 rest (group :: ret) in
    internal1 x []

(* TODO: Since OCaml 4.00.0 *)
let mapi f l =
    let _, r = List.fold_left (fun (i, l) x -> i + 1, (f i x) :: l) (0, []) l in
    List.rev r

let rec repeat f n k =
  if n > 0 then
    let n = n - 1 in
    (repeat f n (f n k))
  else k

let comparePair (x1, y1) (x2, y2) =
  match compare x1 x2 with
    | 0 -> compare y1 y2
    | ret -> ret
