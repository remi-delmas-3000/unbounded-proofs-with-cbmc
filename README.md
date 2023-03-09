# unbounded-proofs-with-cbmc

This project is an experiment that uses recursive predicates, dynamic frames and
program instrumentation to prove memory safety of functions that manipulate
unbounded singly and doubly linked lists.

The program transformation uses bounded unrollings of the recursive predicates
describing the data structures, reifies assumptions about opaque pointers
as data in the program which allows us to perform unbounded reasoning using only
bounded unrollings and inductive invariants.

The program instrumentation is performed by hand in this example but can be
implemented as a goto-instrument pass.

Tested with cbmc 5.78.0 and the kissat sat solver as external sat solver
(Minisat2 does not work too well on these problems).
