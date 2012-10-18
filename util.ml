
let new_id =
    let id = ref 0 in
    fun () -> (incr id; !id)

let distinct l =
    let rec internal l = function
        | x :: rest ->
            internal (l @ (if List.mem x l then [] else [x])) rest
        | [] -> l in
    internal [] l

let reduce f = function
    | x :: rest -> List.fold_left f x rest
    | _ -> assert false

let directProduct input =
    let ret = ref [] in
    let rec inner current = function
        | [] -> ret := current :: !ret
        | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

let join separator elements =
    let buf = Buffer.create 1 in
    let rec internal = function
    | [] -> ""
    | [x] ->
        Buffer.add_string buf x;
        Buffer.contents buf
    | x :: rest ->
        Buffer.add_string buf x;
        Buffer.add_string buf separator;
        internal rest in
    internal elements

let listToArray l =
    let len = List.length l in
    if len = 0 then [| |] else
    let ret = Array.make len (List.hd l) in
    let i = ref 0 in
    List.iter (fun x -> ret.(!i) <- x; incr i) l;
    ret

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
