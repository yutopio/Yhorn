
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