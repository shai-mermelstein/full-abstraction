From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Coq Require Import FinFun.
Import ListNotations.

Definition implies {A} (P1 P2 : A -> Prop) 
  : Prop :=
  forall (a : A), P1 a -> P2 a.
Infix "|=" := implies (at level 90).
#[global] Hint Transparent implies : core.

Definition equiv {A} (P1 P2 : A -> Prop) 
  : Prop :=
  forall (a : A), P1 a <-> P2 a.
Infix "~" := equiv (at level 90).
#[global] Hint Transparent equiv : core.

Definition ID {A} (a : A) (a' : A) := a = a'.

Lemma equiv_refl :
  forall A (P : A -> Prop), P ~ P.
Proof.
  intros. intro a. split; auto.
Qed.

Lemma implies_refl :
  forall A (P : A -> Prop), P |= P.
Proof.
  intros. intro a. intros. assumption.
Qed.


