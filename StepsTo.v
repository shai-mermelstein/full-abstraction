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
From WS  Require Import Basics.
From WS  Require Import AwaitDepth.

(* aexp *)

Lemma plus_steps_to :
  forall a1 a2 a s,
    <{a1 + a2}> / s -->a* a
      ->
    (
      exists a1',
        a1 / s -->a* a1'
          /\
        a = <{a1' + a2}>
    )
      \/
    (
      exists (n1 : nat) a2',
        a1 / s -->a* n1
          /\
        a2 / s -->a* a2'
          /\
        a = <{n1 + a2'}>
    )
      \/
    (
      exists (n1 n2 : nat),
        a1 / s -->a* n1
          /\
        a2 / s -->a* n2
          /\
        a = n1 + n2
    ).
Proof with ellipsis.
  intros.
  remember <{a1 + a2}> as a0.
  generalize dependent a2.
  generalize dependent a1.
  clean_induction H.
  invert H.
  - assert (<{a1' + a2}> = <{a1' + a2}>)...
    clean_apply_in IHmulti H.
    destruct H; [left|destruct H; right; [left|right]].
    + destruct H as [a1'' []]...
    + destruct H as [n1 [a2' []]]...
    + destruct H as [n1 [n2 []]]...
  - invert H3.
    assert (<{n + a2'}> = <{n + a2'}>)...
    clean_apply_in IHmulti H.
    destruct H; right; [left|destruct H; [left|right]].
    + destruct H as [a1' []]. invert H...
    + destruct H as [n1 [a2'' []]]. exists n1, a2''...
    + destruct H as [n1 [n2 []]]. exists n1, n2...
  - clear IHmulti. right. right. invert H0...
Qed.

Lemma minus_steps_to :
  forall a1 a2 a s,
    <{a1 - a2}> / s -->a* a
      ->
    (
      exists a1',
        a1 / s -->a* a1'
          /\
        a = <{a1' - a2}>
    )
      \/
    (
      exists (n1 : nat) a2',
        a1 / s -->a* n1
          /\
        a2 / s -->a* a2'
          /\
        a = <{n1 - a2'}>
    )
      \/
    (
      exists (n1 n2 : nat),
        a1 / s -->a* n1
          /\
        a2 / s -->a* n2
          /\
        a = n1 - n2
    ).
Proof with ellipsis.
  intros.
  remember <{a1 - a2}> as a0.
  generalize dependent a2.
  generalize dependent a1.
  clean_induction H.
  invert H.
  - assert (<{a1' - a2}> = <{a1' - a2}>)...
    clean_apply_in IHmulti H.
    destruct H; [left|destruct H; right; [left|right]].
    + destruct H as [a1'' []]...
    + destruct H as [n1 [a2' []]]...
    + destruct H as [n1 [n2 []]]...
  - invert H3.
    assert (<{n - a2'}> = <{n - a2'}>)...
    clean_apply_in IHmulti H.
    destruct H; right; [left|destruct H; [left|right]].
    + destruct H as [a1' []]. invert H...
    + destruct H as [n1 [a2'' []]]. exists n1, a2''...
    + destruct H as [n1 [n2 []]]. exists n1, n2...
  - clear IHmulti. right. right. invert H0...
Qed.

Lemma mult_steps_to :
  forall a1 a2 a s,
    <{a1 * a2}> / s -->a* a
      ->
    (
      exists a1',
        a1 / s -->a* a1'
          /\
        a = <{a1' * a2}>
    )
      \/
    (
      exists (n1 : nat) a2',
        a1 / s -->a* n1
          /\
        a2 / s -->a* a2'
          /\
        a = <{n1 * a2'}>
    )
      \/
    (
      exists (n1 n2 : nat),
        a1 / s -->a* n1
          /\
        a2 / s -->a* n2
          /\
        a = n1 * n2
    ).
Proof with ellipsis.
  intros.
  remember <{a1 * a2}> as a0.
  generalize dependent a2.
  generalize dependent a1.
  clean_induction H.
  invert H.
  - assert (<{a1' * a2}> = <{a1' * a2}>)...
    clean_apply_in IHmulti H.
    destruct H; [left|destruct H; right; [left|right]].
    + destruct H as [a1'' []]...
    + destruct H as [n1 [a2' []]]...
    + destruct H as [n1 [n2 []]]...
  - invert H3.
    assert (<{n * a2'}> = <{n * a2'}>)...
    clean_apply_in IHmulti H.
    destruct H; right; [left|destruct H; [left|right]].
    + destruct H as [a1' []]. invert H...
    + destruct H as [n1 [a2'' []]]. exists n1, a2''...
    + destruct H as [n1 [n2 []]]. exists n1, n2...
  - clear IHmulti. right. right. invert H0...
Qed.

(* bexp *)

Lemma eq_steps_to :
  forall a1 a2 b s,
    <{a1 = a2}> / s -->b* b
      ->
    (
      exists a1',
        a1 / s -->a* a1'
          /\
        b = <{a1' = a2}>
    )
      \/
    (
      exists (n1 : nat) a2',
        a1 / s -->a* n1
          /\
        a2 / s -->a* a2'
          /\
        b = <{n1 = a2'}>
    )
      \/
    (
      exists (n1 n2 : nat),
        a1 / s -->a* n1
          /\
        a2 / s -->a* n2
          /\
        b = bool_bexp (n1 =? n2)%nat
    ).
Proof with ellipsis.
  intros.
  remember <{a1 = a2}> as b0.
  generalize dependent a2.
  generalize dependent a1.
  clean_induction H.
  invert H.
  - assert (<{a1' = a2}> = <{a1' = a2}>)...
    clean_apply_in IHmulti H.
    destruct H; [left|destruct H; right; [left|right]].
    + destruct H as [a1'' []]...
    + destruct H as [n1 [a2' []]]...
    + destruct H as [n1 [n2 []]]...
  - invert H3.
    assert (<{n = a2'}> = <{n = a2'}>)...
    clean_apply_in IHmulti H.
    destruct H; right; [left|destruct H; [left|right]].
    + destruct H as [a1' []]. invert H...
    + destruct H as [n1 [a2'' []]]. exists n1, a2''...
    + destruct H as [n1 [n2 []]]. exists n1, n2...
  - clear IHmulti. right. right. invert H0.
    destruct (v1 =? v2)%nat...
Qed.

Lemma le_steps_to :
  forall a1 a2 b s,
    <{a1 <= a2}> / s -->b* b
      ->
    (
      exists a1',
        a1 / s -->a* a1'
          /\
        b = <{a1' <= a2}>
    )
      \/
    (
      exists (n1 : nat) a2',
        a1 / s -->a* n1
          /\
        a2 / s -->a* a2'
          /\
        b = <{n1 <= a2'}>
    )
      \/
    (
      exists (n1 n2 : nat),
        a1 / s -->a* n1
          /\
        a2 / s -->a* n2
          /\
        b = bool_bexp (n1 <=? n2)
    ).
Proof with ellipsis.
  intros.
  remember <{a1 <= a2}> as b0.
  generalize dependent a2.
  generalize dependent a1.
  clean_induction H.
  invert H.
  - assert (<{a1' <= a2}> = <{a1' <= a2}>)...
    clean_apply_in IHmulti H.
    destruct H; [left|destruct H; right; [left|right]].
    + destruct H as [a1'' []]...
    + destruct H as [n1 [a2' []]]...
    + destruct H as [n1 [n2 []]]...
  - invert H3.
    assert (<{n <= a2'}> = <{n <= a2'}>)...
    clean_apply_in IHmulti H.
    destruct H; right; [left|destruct H; [left|right]].
    + destruct H as [a1' []]. invert H...
    + destruct H as [n1 [a2'' []]]. exists n1, a2''...
    + destruct H as [n1 [n2 []]]. exists n1, n2...
  - clear IHmulti. right. right. invert H0.
    destruct (v1 <=? v2)...
Qed.

Lemma not_steps_to :
  forall b1 b s,
    <{~b1}> / s -->b* b
      ->
    (
      exists b',
        b1 / s -->b* b'
          /\
        b = <{~b'}>
    )
      \/
    (
      exists v,
        b1 / s -->b* bool_bexp v
          /\
        b = bool_bexp (negb v)
    ).
Proof with ellipsis.
  intros.
  remember <{~ b1}> as b0.
  generalize dependent b1.
  clean_induction H.
  invert H.
  - assert (<{~b1'}> = <{~b1'}>)...
    clean_apply_in IHmulti H.
    destruct H; [left|right].
    + destruct H as [b' []]. exists b'...
    +  destruct H as [v []]. exists v...
  - invert H0... clear IHmulti.
    right. exists true...
  - invert H0... clear IHmulti.
    right. exists false...
Qed.

Lemma and_steps_to :
  forall b1 b2 b s,
    <{b1 && b2}> / s -->b* b
      ->
    (
      exists b1',
        b1 / s -->b* b1'
          /\
        b = <{b1' && b2}>
    )
      \/
    (
      b1 / s -->b* <{false}>
        /\
      b = <{false}>
    )
      \/
    (
      b1 / s -->b* <{true}>
        /\
      b2 / s -->b* b
    ).
Proof with ellipsis.
  intros.
  remember <{b1 && b2}> as b0.
  generalize dependent b2.
  generalize dependent b1.
  clean_induction H.
  invert H.
  - assert (<{b1' && b2}> = <{b1' && b2}>)...
    clean_apply_in IHmulti H.
    destruct H as [ |[]]; 
      [left|right;left|right;right]...
    destruct H as [b' []]. exists b'...
  - invert H0...
Qed.
      
