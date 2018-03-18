Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Grammar.
Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.

(* Name *)

Coercion name := fun (s : string) => s : Name.

(* Span *)

Coercion SEName : Name >-> SpanExp.
Notation "'span'" := (fun a b => SESpan (SSpan a b)) (at level 9).

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

Coercion BVRef : RRef >-> BindableValue.
Coercion BVTree : ReadableTree >-> BindableValue.
Coercion BVName : Name >-> BindableValue.

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

Coercion WRWRef : WRef >-> WriteableReference.
Coercion WRWTree : WriteableTree >-> WriteableReference.

(* Expression *)

Coercion EWR : WriteableReference >-> Expression.
Coercion EBV : BindableValue >-> Expression.
Coercion ER : Request >-> Expression.
Coercion EN : Name >-> Expression.

(* Run *)

Lemma list_to_nelist : forall X (l : list X), l <> nil -> nelist X.
Proof.
  intros. destruct l.
  - congruence.
  - split; assumption.
Qed.

Close Scope nat_scope.

Definition exp := WriteableReference + BindableValue + Request + Name.

Coercion wrexp := fun (wr : WriteableReference) => inl (inl (inl wr)) : exp.
Coercion bvexp := fun (bv : BindableValue) => inl (inl (inr bv)) : exp.
Coercion rexp := fun (r : Request) => inl (inr r) : exp.
Coercion nexp := fun (n : Name) => inr n : exp.

Definition exp_to_expression (e : exp) : Expression.
Proof.
  destruct e. destruct s. destruct s.
  - apply EWR. assumption.
  - apply EBV. assumption.
  - apply ER. assumption.
  - apply EN. assumption.
Qed.

Inductive expList :=
| elNil : expList
| elCons : exp -> expList -> expList.

Fixpoint expList_to_list (l : expList) : list Expression :=
  match l with
  | elNil => nil
  | elCons a l => cons (exp_to_expression a) (expList_to_list l)
  end.

Definition expList_to_nelist (l : expList) :
  l <> elNil -> nelist Expression.
Proof.
  intros. apply list_to_nelist with (expList_to_list l).
  destruct l.
  - congruence.
  - simpl. intros contra. congruence.
Qed.

Lemma elCons_neq_elNil : forall a l, elCons a l <> elNil.
Proof.
  intros a l c.
  inversion c.
Qed.

Notation "'run' a" := (Run (a, [])) (at level 9,
                                     right associativity).
Notation "'run' a b .. z" := (Run (expList_to_nelist
                                     (elCons a (elCons b .. (elCons z elNil) ..))
                                     (elCons_neq_elNil a _)))
                                   (at level 9,
                                    a at level 9,
                                    b at level 9).

(* Bind *)

Notation "'bind' wre bve" := (Bind wre bve) (at level 9,
                                             wre at level 9).