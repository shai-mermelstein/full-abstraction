From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Import ListNotations.
From WS  Require Import Tactics.

(* 
  This file defines the transitive closure of a relation.
*)

Definition relation (X : Type) := X -> X -> Prop.

(* 
  multi R is the transitive closure of R.
*)
Inductive multi {X} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), 
    multi R x x
  | multi_step : forall (x y z : X),
    R x y 
      -> 
    multi R y z 
      -> 
    multi R x z.
#[global] Hint Constructors multi : core.

Theorem multi_R : 
  forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
    multi R x y  -> multi R y z -> multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - assumption.
    - apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

