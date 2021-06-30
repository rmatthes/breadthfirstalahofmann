Since Coq 8.11, one can selectively switch off positivity checks. This is used in important ways in the code for BreadthFirst.v (tested with Coq 8.13.2, compiled with OCaml 4.10.0).

[ historic comments ]

in previous versions, the code in BreadthFirst.v depended on the TypingFlags plugin by Simon Boulier

https://github.com/SimonBoulier/TypingFlags

One has to compile it and to *install* it, usually the latter with sudo make install or make install, depending on the system configuration.

Then, one can compile the .v file with coqc without further options or just use ProofGeneral to study it interactively.

(tested again with Coq 8.9.0, compiled with OCaml 4.07.0;
 tested again with Coq 8.9.1, compiled with OCaml 4.07.1)
 ]
