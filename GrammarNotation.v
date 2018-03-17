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

Notation "'run' a" := (Run (a, [])) (at level 9,
                                     right associativity).
Notation "'run' a b .. z" := (Run (a, cons b .. (cons z nil) ..))
                               (at level 9,
                                a at level 9,
                                b at level 9).

(* Bind *)

Notation "'bind' wre bve" := (Bind wre bve) (at level 9,
                                             wre at level 9).