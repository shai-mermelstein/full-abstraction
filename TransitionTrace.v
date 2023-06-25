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
From WS  Require Import PartialCorrectness.
From WS  Require Import StateTrace.

(* 
  Equivalent to Brookes def. of T⟦-⟧ 
    for arithmetic expressions (found in section 9).
*)
Inductive aTT (n : nat) : aexp -> transitions -> Prop :=
  | aTT_Term :  forall a0 s,
    a0 / s -->a* n
      ->
    aTT n a0 [(s, s)]
  | aTT_Step : forall a0 a1 s ts, 
    a0 / s -->a* a1
      ->
    aTT n a1 ts
      ->
    aTT n a0 ((s, s) :: ts).
#[global] Hint Constructors aTT : core.

(* 
  Equivalent to Brookes def. of T⟦-⟧ 
    for Boolean expressions (found in section 9).
*)
Inductive bTT v : bexp -> transitions -> Prop :=
  | bTT_Term :  forall b0 s,
    b0 / s -->b* (bool_bexp v)
      ->
    bTT v b0 [(s, s)]
  | bTT_Step : forall b0 b1 s ts, 
    b0 / s -->b* b1
      ->
    bTT v b1 ts
      ->
    bTT v b0 ((s, s) :: ts).
#[global] Hint Constructors bTT : core.

(* 
  Equivalent to Brookes def. of T⟦-⟧ for
    commands (found in section 6).
*)
Inductive TT : com -> transitions -> Prop :=
  | TT_Term :  forall c0 s0 s1,
    c0 / s0 -->* <{skip}> / s1
      ->
    TT c0 [(s0, s1)]
  | TT_Step : forall c0 c1 s0 s1 ts, 
    c0 / s0 -->* c1 / s1
      ->
    TT c1 ts
      ->
    TT c0 ((s0, s1) :: ts).
#[global] Hint Constructors TT : core.

(*
  Equivalent to Brookes definition of ≤_T and =_T
*)
Definition TTorder c c' :=
  forall ps, TT c ps -> TT c' ps.
Notation " c '<tt' c'" := 
  (TTorder c c') (at level 50).
Definition TTequivalence c c' :=
  c <tt c' /\ c' <tt c.
Notation " c '=tt' c'" := 
  (TTequivalence c c') (at level 50).
Notation " c '~=tt' c'" := 
  (~(c =tt c')) (at level 50).
#[global] Hint Unfold TTorder TTequivalence : core.

(* auxiliary definitions *)

(* 
  Used in ST_from_TT below.
*)
Fixpoint trace_to_tt (ss : list state) :=
  match ss with
  | nil      => nil
  | s1 :: ss => match ss with
    | nil     => nil
    | s2 :: _ => (s1, s2) :: trace_to_tt ss
    end
  end.

(* claims *)

(* 
  Observation made by Brookes in section 6.
*)
Theorem PC_from_TT :
  forall c t,
    PC c t <-> TT c [t].
Proof with ellipsis.
  intros c [s0 sw]. 
  split; intros...
  solve_by_inverts 2.
Qed.

(* 
  Observation made by Brookes in section 6.
*)
Theorem ST_from_TT :
  forall c ss,
    ST c ss <-> TT c (trace_to_tt ss).
Proof with ellipsis.
  intros. split; intros.
  - generalize dependent c.
    induction ss...
  - generalize dependent c.
    induction ss; intros...
    destruct ss... destruct ss...
Qed.

(* 
  Showing that transition traces are closed under
    stutters and mumbled.
  Brookes makes this claim 
    in section 6 for commands, and 9 for 
    expressions.
*)

Theorem aTT_stuttery_mumbly: 
  forall n a, 
    stuttery_mumbly (aTT n a).
Proof with ellipsis.
  intros n a ts H. induction H...
  - remember (l1 ++ l2) as l.
    generalize dependent l1.
    clean_induction IHstutter_mumble_closure.
    + destruct l1... invert Heql. destruct l1...
    + induction l1...
  - clear H.
    remember (l1 ++ [(x, y); (y, z)] ++ l2) as l.
    generalize dependent l1.
    clean_induction IHstutter_mumble_closure.
    + destruct l1... invert Heql. destruct l1...
    + destruct l1... invert Heql. simpl.
      invert IHstutter_mumble_closure.
      * eapply aTT_Term. eapply multi_trans...
      * eapply aTT_Step. eapply multi_trans...
        auto.
Qed.

Theorem bTT_stuttery_mumbly: 
  forall v b, 
    stuttery_mumbly (bTT v b).
Proof with ellipsis.
  intros v b ts H. induction H...
  - remember (l1 ++ l2) as l.
    generalize dependent l1.
    clean_induction IHstutter_mumble_closure.
    + destruct l1... invert Heql. destruct l1...
    + induction l1...
  - clear H.
    remember (l1 ++ [(x, y); (y, z)] ++ l2) as l.
    generalize dependent l1.
    clean_induction IHstutter_mumble_closure.
    + destruct l1... invert Heql. destruct l1...
    + destruct l1... invert Heql. simpl.
      invert IHstutter_mumble_closure.
      * eapply bTT_Term. eapply multi_trans...
      * eapply bTT_Step. eapply multi_trans...
        auto.
Qed.

Theorem TT_stuttery_mumbly: 
  forall c, 
    stuttery_mumbly (TT c).
Proof with ellipsis.
  intros c ts H. induction H...
  - remember (l1 ++ l2) as l.
    generalize dependent l1.
    clean_induction IHstutter_mumble_closure.
    + destruct l1... invert Heql. destruct l1...
    + induction l1...
  - clear H.
    remember (l1 ++ [(x, y); (y, z)] ++ l2) as l.
    generalize dependent l1.
    clean_induction IHstutter_mumble_closure.
    + destruct l1... invert Heql. destruct l1...
    + destruct l1... invert Heql. simpl.
      invert IHstutter_mumble_closure.
      * eapply TT_Term. eapply multi_trans...
      * eapply TT_Step. eapply multi_trans...
        auto.
Qed.

