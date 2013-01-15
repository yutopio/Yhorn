open Types

let main _ =
  let input =
    match Array.length (Sys.argv) with
      | 1 -> stdin
      | 2 -> let filename = Sys.argv.(1) in open_in (filename)
      | _ -> assert false in
    let [a;b] = Parser.inputUnit Lexer.token (Lexing.from_channel input) in

    print_string "A: ";
    print_endline (printFormula printExpr a);
    print_string "B: ";
    print_endline (printFormula printExpr b);

    let space = Interpolation.interpolate (a, b) in

    let t = Interpolation.getInterpolant space in
    Interpolation.verifyInterpolant (a, b) t;
    print_string "Solution:\n\t";
    print_endline (printFormula printExpr t)

let _ = main ()
