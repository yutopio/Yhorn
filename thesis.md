Introduction
===

Automated theorem proving plays an important role in the modern program verification. Particularly in the context of verification with model checking techniques, an automated theorem prover is used to abstract an infinite set of program states into a finite one so that the model checker can virtually explore all possible program execution paths.

One of the most common methods of such abstraction is predicate abstraction. An automated theorem prover finds appropriate predicates for specific program locations. An execution state at each location is then expressed by a Boolean valuation of the given predicates. If the abstraction is too coarse and a model checker discovers an infeasible error execution path in an abstract system, the prover computes an additional predicate at a specific program location to refine the abstraction. The additional predicate must be satisfied at the location under the execution in the concrete model along the discovered path, and the execution does not lead to the program failure by the same path. After the refinement, the infeasible path is ruled out and no longer found by the model checker.

In order to obtain such a refinement predicate at the specific program location along the infeasible counterexample, one class of automated theorem provers, called an interpolating theorem prover, computes a Craig interpolant between two sets of constraints; the one consists of the constraints from the program entry point to the location, and the other consists of the constraints from the location to the program failure. Those constraints include variable assignments and assertions to be satisfied originated from conditional branches.

However, existing interpolating theorem provers may return too complex a solution which is heavily affected by the specific path constraints. This causes the model checker to discover similar paths infinitely which pass the same program location by loops or recursion calls, and not to terminate.

To avoid such undesired situation, it is required to use an invariant for the predicate abstraction. Based on the hypothesis that program’s invariants tend to be simple formulas, we propose a new interpolating algorithm which tries to minimize the number of conjunctions and disjunctions in a solution.
