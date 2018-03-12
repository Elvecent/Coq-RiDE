Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Definition ale (a b : ascii) := nat_of_ascii a <= nat_of_ascii b.

Reserved Notation "s1 ⋞ s2" (at level 10).

Inductive sle : string -> string -> Prop :=
| LexEmpty : forall s, EmptyString ⋞ s
| LexChar :
    forall (a1 a2 : ascii) (s1 s2 : string),
      ale a1 a2 ->
      (a1 = a2 -> s1 ⋞ s2) -> 
      (String a1 s1) ⋞ (String a2 s2)
                     
where "s1 ⋞ s2" := (sle s1 s2) : lex_scope.