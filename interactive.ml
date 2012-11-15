open Yint.Types
open Yint.Parser
open Yint.Lexer
open Yint.Main

let main _ =
  let input = inputUnit token (Lexing.from_channel stdin) in
  let predAssignments = solve input in
    
  MP.iter (fun k v ->
  print_endline ("***** " ^ k ^ " *****");
    (match v with
    | Some space -> (
        match getInterpolant space with
        | Some t ->
            print_string "Solution:\n\t";
            print_endline (printFormula printExpr t)
        | None -> print_endline "No solution (no interpolant)")
    | None -> print_endline "No solution (no space)");
  print_newline ()) predAssignments;

    ignore (Yint.Z3py.close ())

let _ = main ()
