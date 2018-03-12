Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Grammar.
Require Import LexString.

Open Scope lex_scope.

Inductive type : Type :=
| HoleT : type
| OrT : nelist string -> type
| SpanT : string -> string -> type.

Inductive context : list syncat -> Type :=
| CNil : context nil
| CCons : forall {sc l}, term sc * type -> context l -> context (sc :: l).

Reserved Notation "s ∈ T" (at level 10).

Inductive sIn : string -> type -> Prop :=
| InHole : forall s, s ∈ HoleT
| InOr1 : forall s l, s ∈ (OrT (s ::: l))
| InOr : forall s h l, In s l -> s ∈ (OrT (h ::: l))
| InSpan : forall s s1 s2, s1 ⋞ s -> s ⋞ s2 -> s ∈ (SpanT s1 s2)
                  
where "s ∈ T" := (sIn s T).