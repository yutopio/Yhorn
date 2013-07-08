
module List = struct
  include List

  let remove x =
    let rec inner ret =
      function
      | [] -> raise Not_found
      | y :: rest ->
        if x = y then rev_append ret rest
        else inner (y :: ret) rest in
    inner []

  let remove_at i l =
    assert (i < List.length l);
    let rec inner i ret (x :: rest) =
      match i with
      | 0 -> rev_append ret rest
      | _ -> inner (i - 1) (x :: ret) rest in
    inner i [] l

  let index_of x =
    let rec inner i =
      function
      | [] -> raise Not_found
      | y :: rest -> if x = y then i else inner (i + 1) rest in
    inner 0

  let reduce compare = function
    | [] -> failwith "reduce"
    | seed :: rest -> fold_left compare seed rest

  let max = function
    | [] -> failwith "max"
    | l -> reduce max l

  let min = function
    | [] -> failwith "min"
    | l -> reduce min l

  let try_pick f =
    List.fold_left (fun ret x -> if ret = None then f x else ret) None

  let distinct l =
    let rec internal l = function
      | x :: rest ->
        internal (l @ (if List.mem x l then [] else [x])) rest
      | [] -> l in
    internal [] l

  let sort_distinct l =
    let compare_neg x y = - (compare x y) in
    let sorted = List.fast_sort compare_neg l in
    let rec f ret = function
      | [] -> ret
      | [x] -> x::ret
      | x::y::z -> f (if x = y then ret else x::ret) (y::z) in
    f [] sorted

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

  let chop n x =
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

  (* NOTE: Provided in the standard library since OCaml 4.00.0 *)
  let mapi f l =
    let _, r = List.fold_left (fun (i, l) x -> i + 1, (f i x) :: l) (0, []) l in
    List.rev r

  let starts_with value target =
    let vl = length value in
    let tl = length target in
    (vl <= tl) && (take vl target = value)

  let ends_with value target =
    let vl = length value in
    let tl = length target in
    (vl <= tl) && (skip (vl - tl) target = value)

  let direct_product input =
    let ret = ref [] in
    let rec inner current = function
      | [] -> ret := current :: !ret
      | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

  let sorted_multimap compare f lists =
    (* Give IDs to lists. *)
    let (_, lists) =
      fold_left (fun (i, l) x -> (i + 1, [i, x] @ l)) (0, []) lists in

    let rec step acc lists =
      (* Sort given lists that empty ones come first followed by the rest in the
         order of the first association's key. *)
      let lists = fast_sort
        (fun (_, x) (_, y) ->
          match x, y with
            | [], [] -> 0
            | [], _ -> -1
            | _, [] -> 1
            | (x,_)::_, (y,_)::_ -> compare x y) lists in

      (* Skip empty lists in the beginning. *)
      let rec trunc_empty = function
        | (_, []) :: rest -> trunc_empty rest
        | l -> l in
      let lists = trunc_empty lists in

      (* Then take associations with the current smallest key. *)
      match lists with
        | (fst_id, (key, fst_val) :: fst_rest) :: rest ->

          (* Obtain each values from assoc lists. *)
          let rec iter_assoc f_param processed =

            (* Helper function to call f. *)
            let call_f acc =
              match (f key f_param) with
                | None -> acc
                | Some x -> (key, x) :: acc in

            function
              | (cur_id, (cur_key, cur_val) :: cur_rest) :: rest as l ->
                let cmp = compare key cur_key in
                if cmp = 0 then
                  (* Accumulate current association. *)
                  iter_assoc
                    ((cur_id, cur_val) :: f_param)
                    ((cur_id, cur_rest) :: processed)
                    rest
                else (
                  (* The next association must have a greater key. *)
                  assert (cmp > 0);
                  step (call_f acc) (l @ processed))
              | (_, []) :: _ -> assert false
              | [] ->
                step (call_f acc) processed in

          (* Call functions *)
          iter_assoc [fst_id, fst_val] [fst_id, fst_rest] rest

        | (_, []) :: _ -> assert false
        | [] -> rev acc (* All finish. *)
    in
    step [] lists

end
