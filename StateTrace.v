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

(* 
  Equivalent to Brookes def. 4.2 of φ⟦-⟧
  with the additional requirement that 
    φ⟦-⟧s_0...s_k -> k > 0
  (this is needed to insure that φ⟦skip⟧ = φ⟦skip; skip⟧)
*)
Inductive ST : com -> states -> Prop :=
  | ST_Term : forall c s s',
    c / s -->* <{skip}> / s' 
      ->
    ST c [s; s']
  | ST_Step : forall c c' s s' ss,
    c / s -->* c' / s'
      ->
    ST c' (s' :: ss)
      ->
    ST c (s :: s' :: ss).
#[global] Hint Constructors ST : core.

(*
  Equivalent to Brookes definition of ⊑_φ
*)
Definition STpreorder c d := ST c =>> ST d.
Notation "c '[st' d" := (STpreorder c d) 
  (at level 50).
Notation "c '~st' d" := (c [st d /\ d [st c)
  (at level 50).
#[global] Hint Transparent STpreorder : core.

(*
  Equivalent to Brookes definition of ≤_φ and =_φ
*)
Definition STorder c d :=
  forall cxt, plug cxt c [st plug cxt d.
Notation "c '<st' d" := (STorder c d) 
  (at level 50).
Notation "c '=st' d" := (c <st d /\ d <st c)
  (at level 50).
Notation "c '/st' d" := (~(c =st d))
  (at level 50).
#[global] Hint Transparent STorder : core.
