open Yint.Types
open Yint.Parser
open Yint.Lexer
open Yint.Main

let main _ =
    let formulae = inputUnit token (Lexing.from_channel stdin) in
    let space = interpolate formulae in

    (match space with
    | Some space -> (
        match getInterpolant space with
        | Some t ->
            print_string "Solution:\n\t";
            print_endline (printFormula printExpr t)
        | None -> print_endline "No solution (no interpolant)")
    | None -> print_endline "No solution (no space)");

    ignore (Yint.Z3py.close ())

let _ = main ()
