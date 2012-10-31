open Types

(** Apply a function to each element in the list and pick the first result that
    is not None. *)
let tryPick f = List.fold_left (fun ret x -> if ret = None then f x else ret) None

let new_id =
    let id = ref 0 in
    fun () -> (incr id; !id)

let distinct l =
    let rec internal l = function
        | x :: rest ->
            internal (l @ (if List.mem x l then [] else [x])) rest
        | [] -> l in
    internal [] l

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

let arrayFold2 f x a =
    let i = ref (-1) in
    Array.fold_left (fun x -> f x (a.(incr i; !i))) x

let rec skip n x =
    assert (n >= 0);
    if n = 0 then x
    else match x with
        | [] -> []
        | a :: rest -> skip (n - 1) rest

let take n x =
    let rec internal n x ret =
        assert (n >= 0);
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
