Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Grammar.
Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.

(* Name *)

Coercion name := fun (s : string) => s : Name.

(* Span *)

Coercion name_span := fun n : Name =>  SEName n : SpanExp.
Notation "'span'" := (fun a b => (SESpan (SSpan a b)) : SpanExp) (at level 9).

(* WTree *)

Notation "'@'" := WTRoot (at level 6).
Notation "'!tree' t a" := (WTTree t (a, nil)) (at level 9,
                                              t at level 9,
                                              right associativity).
Notation "'!tree' t a b .. z" := (WTTree t (a, cons b .. (cons z nil) ..))
                                   (at level 9,
                                    t at level 9,
                                    a at level 9,
                                    b at level 9).

(* RTree *)

Notation "'tree' t a" := (RTTree t (a, [])) (at level 9,
                                             t at level 9,
                                             right associativity).
Notation "'tree' t a b .. z" := (RTTree t (a, cons b .. (cons z nil) ..))
                                  (at level 9,
                                   t at level 9,
                                   a at level 9,
                                   b at level 9).

Coercion RTree : ReadableTree >-> Tree.
Coercion WTree : WriteableTree >-> Tree.

(* RRef *)

Notation "'ref' t n" := (RRRef t (n, [])) (at level 9,
                                           t at level 9,
                                           right associativity).
Notation "'ref' t a b .. z" := (RRRef t (a, cons b .. (cons z nil) ..))
                                  (at level 9,
                                   t at level 9,
                                   a at level 9,
                                   b at level 9).

(* Request *)

Notation "'get' r" := (Get r) (at level 9).

(* Bindablevalue *)

Coercion rref_bv := fun (r : RRef) => BVRef r : BindableValue.
Coercion rtree_bv := fun (t : ReadableTree) => BVTree t : BindableValue.
Coercion name_bv := fun (n : Name) => BVName n : BindableValue.

(* WRef *)

Notation "'!ref' t n" := (WRRef t (n, [])) (at level 9,
                                           t at level 9,
                                           right associativity).
Notation "'!ref' t a b .. z" := (WRRef t (a, cons b .. (cons z nil) ..))
                                  (at level 9,
                                   t at level 9,
                                   a at level 9,
                                   b at level 9).

(* Writeablereference *)

Coercion wref_wr := fun (wr : WRef) => WRWRef wr : WriteableReference.
Coercion wtree_wr := fun (t : WriteableTree) => WRWTree t : WriteableReference.

(* Expression *)


Coercion wrexp := fun (wr : WriteableReference) =>
                    EWR wr : Expression.
Coercion bvexp := fun (bv : BindableValue) =>
                    EBV bv : Expression.
Coercion rexp := fun (r : Request) =>
                   ER r : Expression.
Coercion nexp := fun (n : Name) =>
                   EN n : Expression.


(* Run *)

Module AuxForRun.
  
  Lemma list_to_nelist : forall X (l : list X), l <> nil -> nelist X.
  Proof.
    intros. destruct l.
    - congruence.
    - split; assumption.
  Qed.
  
  Inductive expList :=
  | elNil : expList
  | elCons : Expression -> expList -> expList.
  
  Fixpoint expList_to_list (l : expList) : list Expression :=
    match l with
    | elNil => nil
    | elCons a l => cons a (expList_to_list l)
    end.
  
  Definition expList_to_nelist (l : expList) :
    l <> elNil -> nelist Expression.
  Proof.
    intros. apply list_to_nelist with (expList_to_list l).
    destruct l.
    - congruence.
    - simpl. congruence.
  Qed.
  
  Lemma elCons_neq_elNil : forall {a l}, elCons a l <> elNil.
  Proof.
    intros a l c.
    inversion c.
  Qed.
  
End AuxForRun.

Import AuxForRun.

Notation "'run' a" := (Run (expList_to_nelist
                              (elCons a elNil)
                              elCons_neq_elNil ))
                        (at level 9,
                         right associativity).

Notation "'run' a b .. z" := (Run (expList_to_nelist
                                     (elCons
                                        a
                                        (elCons
                                           b ..
                                           (elCons z elNil) ..))
                                     elCons_neq_elNil))
                                   (at level 9,
                                    a at level 9,
                                    b at level 9).

(* Bind *)

Notation "'bind' wre bve" := (Bind wre bve) (at level 9,
                                             wre at level 9).