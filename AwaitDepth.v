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

(* 
  This file includes useful definitions and lemmas
  for dealing with induction on command-steps that
  involve await statements. 
*)

(* 
  A function for extracting the maximum await depth of
  a program.
  E.g. 
  - await_depth <{skip}> = 0, 
  - await_depth <{await true then skip end}> = 1
*)
Fixpoint await_depth (c : com) :=
  match c with
  | CSkip       => 0
  | CAsgn i a   => 0
  | CSeq c1 c2  => max (await_depth c1) (await_depth c2)
  | CIf b c1 c2 => max (await_depth c1) (await_depth c2)
  | CWhile b c1 => await_depth c1
  | CPar c1 c2  => max (await_depth c1) (await_depth c2)
  | CAwait b c1 => S (await_depth c1)
  end.

(* 
  As a program runs (i.e. step to other programs),
    the maximum await depth cannot increase.
*)
Lemma await_depth_monotone :
  forall c0 cw s0 sw,
    c0 / s0 -->* cw / sw 
      ->
    await_depth cw <= await_depth c0.
Proof with ellipsis.
  intros.
  remember (c0, s0) as cf0 eqn:E0.
  remember (cw, sw) as cfw eqn:Ew.
  generalize dependent sw.
  generalize dependent s0.
  generalize dependent cw.
  generalize dependent c0.
  induction H; intros; subst;
    try clean_inversion Ew...
  destruct y as [c1 s1].
  assert (await_depth cw <= await_depth c1)...
  assert (await_depth c1 <= await_depth c0)...
  clear IHmulti H0 H1 cw sw.
  remember (c0, s0) as cf0 eqn:E0.
  remember (c1, s1) as cf1 eqn:E1.
  generalize dependent s1.
  generalize dependent s0.
  generalize dependent c1.
  generalize dependent c0.
  induction H; intros; subst;
    clean_inversion E0;
    clean_inversion E1...
  - assert (await_depth c1' 
        <= await_depth c1)...
  - assert (await_depth c1' 
        <= await_depth c1)...
  - assert (await_depth c2' 
        <= await_depth c2)...
Qed.

(* 
  Lemma for proving a property of commands
  using strong induction on the command's 
  maximum await depth.
*)
Lemma await_depth_induction :
  forall (P : com -> Prop),
    (
      forall c,
        (
          forall c',
            await_depth c' < await_depth c
              ->
            P c'
        )
          ->
        P c
    )
      ->
    forall c, P c.
Proof with ellipsis.
  intros.
  remember (await_depth c) as m.
  assert (await_depth c <= m)... clear Heqm.
  generalize dependent c.
  induction m; intros; apply H...
  intros. apply IHm...
Qed.