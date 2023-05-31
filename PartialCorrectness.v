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

(* 
  Equivalent to def. 4.1 in Brookes of M⟦-⟧
*)
Definition PC c (t : transition) :=
  match t with (s0, sw) =>
    c / s0 -->* <{skip}> / sw
  end.
#[global] Hint Transparent PC : core.

(*
  Equivalent to Brookes definition of ⊑_M
*)
Definition PCpreorder c d := PC c |= PC d.
Notation "c '[pc' d" := (PCpreorder c d) 
  (at level 50).
Notation "c '~pc' d" := (c [pc d /\ d [pc c)
  (at level 50).
#[global] Hint Transparent PCpreorder : core.

(*
  Equivalent to Brookes definition of ≤_M and =_M
*)
Definition PCorder c d :=
  forall cxt, plug cxt c [pc plug cxt d.
Notation "c '<pc' d" := (PCorder c d) 
  (at level 50).
Notation "c '=pc' d" := (c <pc d /\ d <pc c)
  (at level 50).
Notation "c '/pc' d" := (~(c =pc d))
  (at level 50).
#[global] Hint Transparent PCorder : core.

