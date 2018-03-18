Require Import Coq.Strings.String.
Import Coq.Lists.List.ListNotations.

Open Scope string_scope.
Open Scope list_scope.
Close Scope nat_scope.

Definition Name := string.

(* Non-empty list is a pair: an element and a list of elements *)
Definition nelist A := (A * list A)%type.

Inductive Span :=
| SSpan : Name -> Name -> Span.

Inductive SpanExp :=
| SESpan : Span -> SpanExp
| SEName : Name -> SpanExp.

Inductive WriteableTree :=
| WTRoot : WriteableTree
| WTTree : WriteableTree -> nelist SpanExp -> WriteableTree.

Inductive Tree :=
| RTree : ReadableTree -> Tree
| WTree : WriteableTree -> Tree

with ReadableTree :=
     | RTTree : Tree -> nelist SpanExp -> ReadableTree.

Inductive RRef :=
| RRRef : Tree -> nelist Name -> RRef.

Inductive Request :=
| Get : RRef -> Request.

Inductive BindableValue :=
| BVRef : RRef -> BindableValue
| BVTree : ReadableTree -> BindableValue
| BVName : Name -> BindableValue.

Inductive WRef :=
| WRRef : WriteableTree -> nelist Name -> WRef.

Inductive WriteableReference :=
| WRWRef : WRef -> WriteableReference
| WRWTree : WriteableTree -> WriteableReference.

Inductive Expression :=
| EWR : WriteableReference -> Expression
| EBV : BindableValue -> Expression
| ER : Request -> Expression
| EN : Name -> Expression.
              
Inductive Command : Type :=
| Run : nelist Expression -> Command
| Bind : WRef -> BindableValue -> Command.

Definition Program := list Command.
