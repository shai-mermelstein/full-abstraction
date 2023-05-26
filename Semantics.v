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

Reserved Notation "[| a ~> n |]"
  (at level 0, a custom com at level 99).
Inductive ASemantics : aexp -> n -> pairsP state :=
  | SmId : forall a n, [| a ~> n |] []
  where "[| a ~> n |]" := ASemantics a n.

Reserved Notation "[| c |]"
  (at level 0, c custom com at level 99).
Inductive CSemantics : com -> pairsP state :=
  | SmSkip : forall s ts,
    LP(Id [(s, s)] ^) ts
      ->
    [|skip|] ts
  (*  *)
  | SmSeq : forall c1 c2 ts,
    LP([|c1|]; [|c2|]) ts
      ->
    [|c1; c2|] ts
  (*  *)
  | SmPar : forall c1 c2 ts,
    LP([|c1|] || [|c2|]) ts
      ->
    [|c1 || c2|] ts
  where "[| c |]" := (CSemantics c).
#[global] Hint Constructors Semantics : core.


