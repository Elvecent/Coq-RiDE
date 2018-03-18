Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Grammar.
Require Import GrammarNotation.
Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.


Check (span "a" "b").
Check !tree @ (span "a" "b").
Check (!tree @ (span "a" "b") (span "c" "g")).
Check (tree @ (span "a" "b")).
Check (tree @ (span "a" "b") (span "c" "d")).
Check ref @ "a".
Check ref @ "a" "b".
Check get (ref @ "a").
Check !ref @ "a".

Check run
      "a"
      (get (ref @ "")).
Check bind (!ref @ "") "a".


Definition prog : Program :=
  [
    bind
      (!ref @ "a")
      (tree @ (span "a" "z")) ;

    run
      (get (ref @ "a"))
      "a" ;

    bind
      (!ref @ "a" "b")
      "wtf"
  ].