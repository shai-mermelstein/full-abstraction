From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Import ListNotations.
From WS  Require Import Basics.
From WS  Require Import Tactics.
From WS  Require Import States.
From WS  Require Import Lists.
From WS  Require Import Multi.
From WS  Require Import Imp.
From WS  Require Import AwaitDepth.
From WS  Require Import Semantics.
From WS  Require Import StepsTo.
From WS  Require Import STequivPC.
From WS  Require Import PartialCorrectness.
From WS  Require Import StateTrace.
From WS  Require Import TransitionTrace.
From WS  Require Import TTequivSemantics.
From WS  Require Import Contexts.
From WS  Require Import FullAbstraction.

(* 
  This file contains as assortment of examples 
    form Brookes or similar to his.
*)

(* 
  Brookes uses <{X := 1; X := X + 1}> & <{X := 2}>
    for this end. 
  However, proving that using fine-grained semantics
    is not simple, and it is also unnecessary,
    as demonstrated.
*)
Example PC_doesn't_imply_PC :
  <{X := 1; X := 2}> [pc <{X := 2}>
    /\
  ~ <{X := 1; X := 2}> [st <{X := 2}>.
Proof with ellipsis.
  split; intros.
  - intros [s0 sw] H. unfold PC in *.
    invert H. invert H0. invert H5...
    invert H1. invert H...
    invert H0. invert H...
    invert H1...
    assert (
      (X |-> 2; X |-> 1; s0)
        =
      (X |-> 2; s0)
    )...
    + apply states_equal. intros.
      unfold update_s. 
      destruct (v =? X)...
    + rewrite H...
  - intros C.
    assert (ST <{X := 2}> [empty_s ; (X |-> 1); (X |-> 2)]).
    + apply C.
      apply ST_Step with <{X := 2}>...
      replace (X |-> 2) with (X |-> 2; X |-> 1)...
      apply states_equal. intros.
      unfold update_s.  destruct (v =? X)...
    + clear C.
      invert H. invert H3.
      * assert (empty_s X = (X |-> 1) X)...
        unfold empty_s, update_s in H.
        destruct (X =? X) eqn:E...
        eapply ieq_iff_neq...
      * invert H... invert H0...
        assert ((X |-> 2) X = (X |-> 1) X)...
        unfold update_s in H.
        destruct (X =? X) eqn:E...
        eapply ieq_iff_neq...
Qed.
    