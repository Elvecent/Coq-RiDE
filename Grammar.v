Require Import Coq.Strings.String.
Import Coq.Lists.List.ListNotations.

Open Scope string_scope.
Open Scope list_scope.

Definition Name := string.

Coercion name := fun (s : string) => s : Name.

(* Non-empty list is a pair: an element and a list of elements *)
Definition nelist A := (A * list A)%type.

Inductive Span :=
| SSpan : Name -> Name -> Span.

Inductive SpanExp :=
| SESpan : Span -> SpanExp
| SEName : Name -> SpanExp.

Coercion SEName : Name >-> SpanExp.

Notation "'span'" := (fun a b => SESpan (SSpan a b)) (at level 9).

Check (span "a" "b") : SpanExp.

Inductive WriteableTree :=
| WTRoot : WriteableTree
| WTTree : WriteableTree -> nelist SpanExp -> WriteableTree.

Notation "'@'" := WTRoot (at level 6).
Notation "'!tree' t a" := (WTTree t (a, [])) (at level 9,
                                              t at level 9,
                                              right associativity).
Notation "'!tree' t a b .. z" := (WTTree t (a, cons b .. (cons z nil) ..))
                                   (at level 9,
                                    t at level 9,
                                    a at level 9,
                                    b at level 9).

Check !tree @ (span "a" "b").
Check (!tree @ (span "a" "b") (span "c" "g")).

Inductive Tree :=
| RTree : ReadableTree -> Tree
| WTree : WriteableTree -> Tree

with ReadableTree :=
     | RTTree : Tree -> nelist SpanExp -> ReadableTree.

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

Check (tree @ (span "a" "b")).
Check (tree @ (span "a" "b") (span "c" "d")).

Inductive RRef :=
| RRRef : Tree -> nelist Name -> RRef.

Notation "'ref' t n" := (RRRef t (n, [])) (at level 9,
                                           t at level 9,
                                           right associativity).
Notation "'ref' t a b .. z" := (RRRef t (a, cons b .. (cons z nil) ..))
                                  (at level 9,
                                   t at level 9,
                                   a at level 9,
                                   b at level 9).

Check ref @ "a".

Check ref @ "a" "b".

Inductive Request :=
| Get : RRef -> Request.

Notation "'get' r" := (Get r) (at level 9).
Check get (ref @ "a").

Inductive BindableValue :=
| BVRef : RRef -> BindableValue
| BVTree : ReadableTree -> BindableValue
| BVName : Name -> BindableValue.

Coercion BVRef : RRef >-> BindableValue.
Coercion BVTree : ReadableTree >-> BindableValue.
Coercion BVName : Name >-> BindableValue.

Inductive WRef :=
| WRRef : WriteableTree -> nelist Name -> WRef.

Notation "'!ref' t n" := (WRRef t (n, [])) (at level 9,
                                           t at level 9,
                                           right associativity).
Notation "'!ref' t a b .. z" := (WRRef t (a, cons b .. (cons z nil) ..))
                                  (at level 9,
                                   t at level 9,
                                   a at level 9,
                                   b at level 9).

Check !ref @ "a".

Inductive WriteableReference :=
| WRWRef : WRef -> WriteableReference
| WRWTree : WriteableTree -> WriteableReference.

Coercion WRWRef : WRef >-> WriteableReference.
Coercion WRWTree : WriteableTree >-> WriteableReference.

Inductive Expression :=
| EWR : WriteableReference -> Expression
| EBV : BindableValue -> Expression
| ER : Request -> Expression
| EN : Name -> Expression.

Coercion EWR : WriteableReference >-> Expression.
Coercion EBV : BindableValue >-> Expression.
Coercion ER : Request >-> Expression.
Coercion EN : Name >-> Expression.
                
Inductive Command : Type :=
| Run : nelist Expression -> Command
| Bind : WRef -> BindableValue -> Command.

Notation "'run' a" := (Run (a, [])) (at level 9,
                                     right associativity).
Notation "'run' a b .. z" := (Run (a, cons b .. (cons z nil) ..))
                               (at level 9,
                                a at level 9,
                                b at level 9).
Notation "'bind' wre bve" := (Bind wre bve) (at level 9,
                                            wre at level 9).


(* For mysterious reasons all run constructions have to be 
   supplied with ": Expression" for their arguments. *)
Check run
      ("a" : Expression)
      (get (ref @ "") : Expression).
Check bind (!ref @ "") "a".

Definition Program := list Command.

Definition prog : Program :=
  [
    bind
      (!ref @ "a")
      (tree @ (span "a" "z")) ;

    run
      (get (ref @ "a") : Expression)
      ("a" : Expression) ;

    bind
      (!ref @ "a" "b")
      "wtf"
  ].