From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Coq Require Import FinFun.
Import ListNotations.
From WS Require Import Tactics.
From WS Require Import Basics.
From WS Require Import Lists.

(* 
  This file defines our domain, states, and proves
    some basic lemma about them.
  Note that we assume a finite domain, s.t. we can
    decide equality on it. This is a reasonable 
    assumption, as any program may contain at most 
    finitely-many identifiers,  and in order to resolve 
    it we must be able to compare identifiers.
*)

Parameter identifier : Type.
Definition identifiers := list identifier.

Parameter ieq : identifier -> identifier -> bool.
Notation "i '=?' j" := (ieq i j)
  (at level 70, no associativity).
Axiom ieq_iff_eq :
  forall i j,
    i =? j = true <-> i = j.

Parameter dom : identifiers.
Axiom dom_full : Full dom.

Parameter X : identifier.
Parameter Y : identifier.
Parameter Z : identifier.
Parameter W : identifier.

Definition state := identifier -> nat.
Definition states := list state.
#[global] Hint Transparent state states : core.

Definition empty_s : state := 
  fun _ => 0.
Definition update_s s j n : state :=
  fun i => if i =? j then n else s i.
Notation "i '|->' n ';' s" :=  (update_s s i n)
  (at level 100, n at next level, right associativity).
Notation "i '|->' n" := (i |-> n ; empty_s) 
  (at level 100).
#[global] Hint Transparent empty_s update_s : core.

Definition transition : Type := state * state.
Definition transitions := list transition.
#[global] Hint Transparent transition transitions : core.


(* claims *)

Lemma ieq_iff_neq :
  forall i j,
    i =? j = false <-> i <> j.
Proof with ellipsis.
  intros. split; intros.
  - intro C.
    apply ieq_iff_eq in C.
    rewrite H in C...
  - destruct (i =? j) eqn:E...
    apply_contra H.
    apply ieq_iff_eq...
Qed.

Lemma identifier_eq_dec : 
  forall (i j : identifier),
    i = j \/ i <> j.
Proof with ellipsis.
  intros.
  destruct (i =? j) eqn:E.
  - apply ieq_iff_eq in E...
  - apply ieq_iff_neq in E...
Qed.

Lemma in_identifiers_dec :
  forall (i : identifier) is,
    i <: is \/ i /: is.
Proof with ellipsis.
  intros. induction is as [ |j]...
  destruct IHis...
  assert (i = j \/ i <> j)
    by apply identifier_eq_dec.
  destruct H0...
  right. intros []...
Qed.

Lemma update_s_eq :
  forall s i n,
    (i |-> n; s) i = n.
Proof with eauto.
  intros. unfold update_s.
  destruct (i =? i) eqn:E...
  apply ieq_iff_neq in E.
  apply_contra E...
Qed.

Lemma update_s_neq :
  forall s i j n,
    j <> i
      ->
    (i |-> n; s) j = s j.
Proof with ellipsis. 
  intros. unfold update_s. 
  apply ieq_iff_neq in H. 
  rewrite H...
Qed. 

Lemma states_equal_by_dom : 
  forall (s s' : state), 
    s = s' 
      <-> 
    forall i, i <: dom -> s i = s' i.
Proof with ellipsis.
  intros. split; intros...
  apply functional_extensionality. intros j.
  apply H. apply dom_full.
Qed.

Lemma states_equal :
  forall (s1 s2 : state),
    s1 = s2 <-> forall v, s1 v = s2 v.
Proof with ellipsis.
  intros. split; intros...
  apply functional_extensionality...
Qed.