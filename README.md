# Coq-RiDE

These files contain an implementation of RiDE grammar in Coq for further research and formalization.

To run and check this, you have to get [Coq](https://coq.inria.fr/). 
At the moment, nothing is guaranteed to work with any versions other than 8.7.2.

Compilation:
```
coqc Grammar.v
coqc GrammarNotation.v
coqc Example.v
```
Other files need not to be checked (for now).

You can edit `Example.v` to test your own examples with cool notation; 
you might want to use CoqIDE or Emacs with [ProofGeneral](https://proofgeneral.github.io/) for that.
