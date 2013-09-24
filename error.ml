
(*** Lexer ***)
let unrecToken token = "Unrecognized token: " ^ token
let nonTermCom = "End-of-file found, '*/' expected"

(*** Z3 Interface ***)
let z3_error msg = "Z3 error: " ^ msg
let z3_solver_undef msg = "Z3 returned L_UNDEF: " ^ msg

(*** Horn ***)
let illegal_binder = "Binder contains multiple appearance of the same variable."
let invalid_arity p = "Inconsistent arity for predicate variable " ^ Id.print p
let no_sol = "No solution"
let incorrect = "Verification failure (incorrect solution; program bugs?)"
let disjunctive_constr = "Disjunction exists in constraints (program bugs?)"
