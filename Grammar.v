Inductive syncat :=
| TREE
| WTREE
| SPAN
| HOLE
| ENUM
| WREF
| CELL
| VAR
.

Require Import Coq.Strings.String.

Definition nelist a : Type := a * (list a).

Inductive term : syncat -> Type :=
| TRoot :
    term TREE
| TTree : forall {sc1 sc2}, Tree sc1 -> list string -> Span sc2 ->
    term TREE
| TWRoot :
    term WTREE
| TWTree : forall {sc1 sc2}, WTree sc1 -> list string -> Span sc2 ->
    term WTREE
| TSpan : string -> string ->
    term SPAN
| THole :
    term HOLE
| TOr : nelist string ->
    term ENUM
| TWCell : forall {sc}, WTree sc -> nelist string ->
    term WREF
| TCell : forall {sc}, Tree sc -> nelist string ->
    term CELL
| TVar : forall s : string,
    term VAR
                                             
with WTree : syncat -> Type :=
     | WTWT : term WTREE -> WTree WTREE
     | WTV : term VAR -> WTree VAR

with Span : syncat -> Type :=
     | SS : term SPAN -> Span SPAN
     | SH : term HOLE -> Span HOLE
     | SE : term ENUM -> Span ENUM

with Tree : syncat -> Type :=
     | TT : term TREE -> Tree TREE
     | TV : term VAR -> Tree VAR
.

Notation "#" := (TT TRoot) : term_scope.
Notation "'tree'" := (fun t l s => TT (TTree t l s)) : term_scope.
Notation "@" := (WTWT TWRoot) : term_scope.
Notation "'!tree'" := (fun w l s => WTWT (TWTree w l s)) : term_scope.
Notation "⃞" := (SH THole) : term_scope.
Notation "'!var'" := (fun s => WTV (TVar s)) : term_scope.
Notation "'var'" := (fun s => TV (TVar s)) : term_scope.
Notation "'span'" := (fun s1 s2 => SS (TSpan s1 s2)) : term_scope.
Notation "'or'" := (fun l => SE (TOr l)) : term_scope.
Notation "a ::: l" :=
  (a, l)
    (at level 100, right associativity) : term_scope.
Notation "'!cell'" := TWCell : term_scope.
Notation "'cell'" := TCell : term_scope.

Import Coq.Lists.List.ListNotations.

Open Scope term_scope.
Open Scope list_scope.
Open Scope string_scope.

Print term.

Definition WTREE_ex1 : WTree WTREE :=
  !tree
    (!tree
      @
      ["a"; "b"]
      (span "c" "d"))
    ["e"]
    ⃞.

Definition WTREE_ex2 : WTree WTREE :=
  !tree
    (!var "x")
    ["a"]
    (or ("c" ::: ["d"])).

Definition CELL_ex : term CELL :=
  cell
    (tree
       #
       nil
       ⃞)
    ("a" ::: ["b"]).

Definition WREF_ex : term WREF :=
  !cell
   (!tree
     @
     ["a"]
     ⃞)
   ("b" ::: ["c"]).

Definition TREE_ex1 : Tree TREE :=
  tree
    #
    ["a"]
    (or ("b" ::: [])).

Definition TREE_ex2 : Tree TREE :=
  tree
    (var "x")
    []
    ⃞.
