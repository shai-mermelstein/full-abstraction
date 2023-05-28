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

