
module List = struct
  include List

  let reduce compare = function
    | [] -> failwith "reduce"
    | seed :: rest -> fold_left compare seed rest

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
