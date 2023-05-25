From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Import ListNotations.

Ltac clean_inversion H := 
  inversion H; subst; eauto; clear H.
Ltac invert H := clean_inversion H.

Ltac clean_induction H :=
  induction H; intros; subst; eauto.

Ltac clean_apply_in H1 H2 :=
  eapply H1 in H2; clear H1; eauto.

Ltac clean_apply H :=
  eapply H; clear H; eauto.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      clean_inversion H;
      match n with S (S (?n')) => subst; 
        solve_by_inverts (S n') end 
    ]
  end end.

Ltac solve_by_invert :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [ clean_inversion H ]
  end end.

Ltac ellipsis' := try solve 
  [
    eauto; intros; repeat esplit; 
    intros; subst; simpl in *; subst; eauto;
    try lia
  ].

Ltac ellipsis := try solve 
  [
    eauto; intros; repeat esplit; 
    intros; subst; simpl in *; subst; eauto;
    try lia; solve_by_invert
  ].

Ltac apply_contra  H := exfalso; apply H.
Ltac eapply_contra H := exfalso; eapply H.





