From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Import ListNotations.
From WS  Require Import Basics.
From WS  Require Import Tactics.
From WS  Require Import States.
From WS  Require Import Lists.
From WS  Require Import Multi.
From WS  Require Import Imp.
From WS  Require Import Basics.
From WS  Require Import AwaitDepth.
From WS  Require Import Contexts.
From WS  Require Import PartialCorrectness.

Reserved Notation "[| a -> n |]"
  (at level 0, a custom com at level 99).
Inductive ASemantics : aexp -> nat -> pairsP state :=
  | SmId : forall a n, [| a -> n |] []
  where "[| a -> n |]" := (ASemantics a n).
#[global] Hint Constructors ASemantics : core.

Reserved Notation "[| b |]t"
  (at level 0, b custom com at level 99).
Reserved Notation "[| b |]f"
  (at level 0, b custom com at level 99).
Inductive BSemantics : bexp -> bool -> pairsP state :=
  | SmTrue : forall s,
    LP({[(s, s)]}^) |= [|true|]t
    
  where "[| b |]t" := (BSemantics b true)
  and   "[| b |]f" := (BSemantics b false).
#[global] Hint Constructors BSemantics : core.


Reserved Notation "[| c |]"
  (at level 0, c custom com at level 99).
Inductive CSemantics : com -> pairsP state :=
  | SmSkip : forall s ts,
    LP({[(s, s)]}^) ts
      ->
    [|skip|] ts
  | SmAsgn : forall i a n s ts,
    [| a -> n |] ts
      ->
    LP({ts ++ [(s, (i |-> n; s))]}^) ts
      ->
    [|i := a|] ts
  | SmSeq : forall c1 c2 ts,
    LP([|c1|]; [|c2|]) ts
      ->
    [|c1; c2|] ts
  | SmIfTrue : forall b c1 c2 ts,
    LP([|b|]t ; [|c1|]) ts
      ->
    [|if b then c1 else c2 end|] ts
  | SmIfFasle : forall b c1 c2 ts,
    LP([|b|]f ; [|c2|]) ts
      ->
    [|if b then c1 else c2 end|] ts
  | SmWhile : forall b c ts,
    LP(([|b|]t ; [|c|])* ; [|b|]f) ts (* star does not include ^, unlike Brookes*)
      ->
    [|while b do c end|] ts
  | SmPar : forall c1 c2 ts,
    LP([|c1|] || [|c2|]) ts
      ->
    [|c1 || c2|] ts
  | SmAwait : forall b c s s' ts,
    [|b|]t [(s, s)]
      ->
    [|c|] [(s, s')]
      ->
    LP({[(s, s')]}^) ts
      ->
    [|await b then c end|] ts
  where "[| c |]" := (CSemantics c).
#[global] Hint Constructors CSemantics : core.


