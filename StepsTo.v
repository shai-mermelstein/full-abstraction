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

(* 
  This file contains characterizations of the 
    configurations a given program may step to 
    (in an arbitrary amount of steps).
  Used in TTequivSemantics.v.
*)

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
      
Lemma asgn_steps_to :
  forall i a c1 s0 s1,
    <{i:=a}> / s0 -->* c1 / s1
      ->
    (
      exists a',
        a / s0 -->a* a'
          /\
        c1 = <{i:=a'}>
          /\
        s0 = s1
    )
      \/
    (
      exists (n : nat),
        a / s0 -->a* n
          /\
        c1 = <{skip}>
          /\
        s1 = (i |-> n; s0)
    ).
Proof with ellipsis.
  intros.
  remember (<{i:=a}>, s0) as cf0 eqn:E0.
  remember (c1, s1) as cf1 eqn:E1.
  generalize dependent a.
  induction H; intros; subst...
  clean_inversion H.
  - assert ((c1, s1) = (c1, s1))...
    apply IHmulti with a1' in H... clear IHmulti.
    destruct H; destruct H...
  - clean_inversion H0.
    clean_inversion H.
Qed.

Lemma seq_steps_to :
  forall c1 c2 c s0 s1,
    <{ c1; c2 }> / s0 -->* c / s1
      ->
    (
      (
        exists c1',
          c1 / s0 -->* c1' / s1
            /\
          c = <{c1'; c2}>
      )
        \/
      (
        exists s',
          c1 / s0 -->* <{skip}> / s'
            /\
          c2 / s' -->* c / s1
      )
    ).
Proof with eauto.
  intros.
  remember (<{ c1; c2 }>, s0) as cf0 eqn:E0.
  remember (c, s1) as cf1 eqn:E1.
  generalize dependent s1.
  generalize dependent s0.
  generalize dependent c.
  generalize dependent c2.
  generalize dependent c1.
  induction H; intros; subst; try clean_inversion E1.
  destruct y as [c' s'].
  clean_inversion H.
  specialize IHmulti with c1' c2 c s' s1.
  assert ((<{ c1'; c2 }>, s') = (<{ c1'; c2 }>, s'))...
  apply IHmulti in H... clear IHmulti.
  destruct H; destruct H; destruct H; subst...
Qed.

Lemma if_steps_to :
  forall b c1 c2 c s0 s1,
    <{if b then c1 else c2 end}> / s0 -->* c / s1
      ->
    (
      exists b',
        b / s0 -->b* b'
          /\
        c = <{if b' then c1 else c2 end}>
          /\
        s1 = s0
    )
      \/
    (
      b / s0 -->b* <{true}>
        /\
      c1 / s0 -->* c / s1
    )
      \/
    (
      b / s0 -->b* <{false}>
        /\
      c2 / s0 -->* c / s1
    ).
Proof with eauto.
  intros.
  remember (<{ if b then c1 else c2 end }>, s0) 
    as cf0 eqn:E0.
  remember (c, s1) as cf1 eqn:E1.
  generalize dependent b.
  induction H; intros; subst.
  - clean_inversion E0.
  - clean_inversion H.
    assert ((c, s1) = (c, s1))...
    apply IHmulti with b1' in H...
    destruct H; destruct H; destruct H...
Qed.
