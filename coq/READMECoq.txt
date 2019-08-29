the code in BreadthFirst.v depends on the TypingFlags plugin by Simon Boulier

https://github.com/SimonBoulier/TypingFlags

One has to compile it and to *install* it, usually the latter with sudo make install or make install, depending on the system configuration.

Then, one can compile the .v file with coqc without further options or just use ProofGeneral to study it interactively.

(tested again with Coq 8.9.0, compiled with OCaml 4.07.0;
 tested again with Coq 8.9.1, compiled with OCaml 4.07.1)
