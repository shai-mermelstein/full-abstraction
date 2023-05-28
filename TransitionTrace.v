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

Fixpoint trace_to_tt (ss : list state) :=
  match ss with
  | nil      => nil
  | s1 :: ss => match ss with
    | nil     => nil
    | s2 :: _ => (s1, s2) :: trace_to_tt ss
    end
  end.

(* claims *)

Theorem PC_from_TT :
  forall c t,
    PC c t <-> TT c [t].
Proof with ellipsis.
  intros c [s0 sw]. 
  split; intros...
  solve_by_inverts 2.
Qed.

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

(* aTT equiv Semantics *)

Lemma aTT_equiv_semantics_num :
  forall n m,
    aTT n (ANum m) ~ [|(ANum m) -> n|].
Proof with ellipsis.
  intros n m ts. split; intros.
  - remember (ANum m) as a. 
    assert (m = n).
    { induction H; invert H... } 
    rewrite H0 in *. clear H0. 
    clean_induction H.
    + eapply SmNum. apply sm_self...
    + invert H...
      apply ASemantics_stuttery_mumbly.
      rewrite cons_to_app...
  - invert H.
    apply aTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear. intros ts H...
Qed.

Lemma aTT_equiv_semantics_id :
  forall n i,
    aTT n (AId i) ~ [|(AId i) -> n|].
Proof with ellipsis.
  intros n i ts. split; intros.
  - remember (AId i) as a.
    clean_induction H.
    + invert H. invert H0. invert H1...
      eapply SmId. apply sm_self...
    + invert H.
      * apply ASemantics_stuttery_mumbly.
        rewrite cons_to_app...
      * invert H1. clear IHaTT.
        remember (s i) as m.
        assert (a1 = <{m}>).
        { invert H2. invert H. }
        rewrite H in *. clear H.
        assert (n = m); subst.
        { apply aTT_equiv_semantics_num in H0... }
        apply SmId.
        remember (s i) as n. clear Heqn H2 i a1.
        remember (s, s) as t.
        assert (LP{[t]^} (t :: ts))... 
        clear Heqt.
        induction H0.
        -- replace [t; (s0, s0)] 
            with ([t] ++ [(s0, s0)] ++ [])...
          apply sm_stuttery. apply sm_self...
        -- replace (t :: (s0, s0) :: ts) 
            with ([t] ++ [(s0, s0)] ++ ts)...
  - invert H.
    apply aTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear. intros ts H...
Qed.

Lemma aTT_plus_substitutive :
  forall n a1 a2 ts,
    aTT n <{a1 + a2}> ts
      <->
    (
      exists n1 n2,
        LP{(aTT n1 a1) ; (aTT n2 a2)} ts
          /\
        n = n1 + n2
    ).
Proof with ellipsis.
  intros n a1 a2 ts. split; intros.
  - remember <{a1 + a2}> as a.
    generalize dependent a2.
    generalize dependent a1.
    clean_induction H.
    + apply plus_steps_to in H.
      destruct H; [ |destruct H].
      * destruct H as [a1' []]...
      * destruct H as [n1 [a2' [H []]]]...
      * destruct H as [n1 [n2 [H []]]].
        exists n1, n2. repeat split...
        apply mumble_1_stutter.
        apply sm_self...
    + apply plus_steps_to in H.
      destruct H; [ |destruct H].
      * destruct H as [a1' []].
        clean_apply_in IHaTT H1.
        destruct H1 as [n1 [n2 []]].
        exists n1, n2. repeat split...
        clear H0 H2 n.
        clean_induction H1; 
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H0 []]]].
        apply sm_self. 
        exists ((s, s) :: l1), l2... 
      * destruct H as [n1 [a2' [H []]]].
        clean_apply_in IHaTT H2.
        destruct H2 as [n1' [n2 []]].
        assert (n1 = n1').
        {
          remember (aTT n2 a2') as P.
          clear H H1 H3 H0 
            HeqP n a1 a2 a3 a2' n2 s.
          induction H2...
          destruct H as [l1 [_ [H _]]].
          remember (ANum n1) as a.
          clean_induction H; solve_by_inverts 2.
        }
        subst.
        exists n1', n2. repeat split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self.
        exists [(s, s)], ((s, s) :: ts).
        repeat split...
        clear H0 a1 H a2.
        apply aTT_stuttery_mumbly.
        clean_induction H2; 
          try rewrite cons_to_app3_assoc_cons...
        destruct H as [l1 [l2 [H []]]]. subst.
        apply sm_self.
        apply aTT_Step with a2'... clear H1.
        induction l1... simpl.
        invert H.
        apply aTT_Step with a2'...
        apply IHl1.
        solve_by_inverts 2.
      * clear IHaTT.
        destruct H as [n1 [n2 [H []]]].
        assert (n = n1 + n2); subst.
        {
          clear H H1.
          remember (ANum (n1 + n2)) as a.
          clean_induction H0;
            solve_by_inverts 2.
        }
        exists n1, n2. repeat split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self.
        exists [(s, s)], ((s, s) :: ts).
        repeat split...
        apply aTT_Step with n2...
        clear H H1.
        remember (ANum (n1 + n2)) as a.
        clean_induction H0.
        eapply aTT_Step... apply IHaTT.
        solve_by_inverts 2.
  - destruct H as [n1 [n2 []]].
    apply aTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    intros ts [ts1 [ts2 [H []]]]. subst.
    induction H.
    + simpl. apply aTT_Step with <{n1 + a2}>.
      * clear H1. induction H...
      * clear H. induction H1...
        -- apply aTT_Term.
          remember (ANum n2) as a2.
          clean_induction H...
        -- apply aTT_Step with <{n1 + a2}>...
          induction H...
    + simpl. apply aTT_Step with <{a1 + a2}>...
      induction H...
Qed.

Lemma aTT_minus_substitutive :
  forall n a1 a2 ts,
    aTT n <{a1 - a2}> ts
      <->
    (
      exists n1 n2,
        LP{(aTT n1 a1) ; (aTT n2 a2)} ts
          /\
        n = n1 - n2
    ).
Proof with ellipsis.
  intros n a1 a2 ts. split; intros.
  - remember <{a1 - a2}> as a.
    generalize dependent a2.
    generalize dependent a1.
    clean_induction H.
    + apply minus_steps_to in H.
      destruct H; [ |destruct H].
      * destruct H as [a1' []]...
        Unshelve. apply O. apply O.
      * destruct H as [n1 [a2' [H []]]]...
        Unshelve. apply O. apply O.
      * destruct H as [n1 [n2 [H []]]].
        exists n1, n2. repeat split...
        apply mumble_1_stutter.
        apply sm_self...
    + apply minus_steps_to in H.
      destruct H; [ |destruct H].
      * destruct H as [a1' []].
        clean_apply_in IHaTT H1.
        destruct H1 as [n1 [n2 []]].
        exists n1, n2. repeat split...
        clear H0 H2 n.
        clean_induction H1; 
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H0 []]]].
        apply sm_self. 
        exists ((s, s) :: l1), l2... 
      * destruct H as [n1 [a2' [H []]]].
        clean_apply_in IHaTT H2.
        destruct H2 as [n1' [n2 []]].
        assert (n1 = n1').
        {
          remember (aTT n2 a2') as P.
          clear H H1 H3 H0 
            HeqP n a1 a2 a3 a2' n2 s.
          induction H2...
          destruct H as [l1 [_ [H _]]].
          remember (ANum n1) as a.
          clean_induction H; solve_by_inverts 2.
        }
        subst.
        exists n1', n2. repeat split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self.
        exists [(s, s)], ((s, s) :: ts).
        repeat split...
        clear H0 a1 H a2.
        apply aTT_stuttery_mumbly.
        clean_induction H2; 
          try rewrite cons_to_app3_assoc_cons...
        destruct H as [l1 [l2 [H []]]]. subst.
        apply sm_self.
        apply aTT_Step with a2'... clear H1.
        induction l1... simpl.
        invert H.
        apply aTT_Step with a2'...
        apply IHl1.
        solve_by_inverts 2.
      * clear IHaTT.
        destruct H as [n1 [n2 [H []]]].
        assert (n = n1 - n2); subst.
        {
          clear H H1.
          remember (ANum (n1 - n2)) as a.
          clean_induction H0;
            solve_by_inverts 2.
        }
        exists n1, n2. repeat split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self.
        exists [(s, s)], ((s, s) :: ts).
        repeat split...
        apply aTT_Step with n2...
        clear H H1.
        remember (ANum (n1 - n2)) as a.
        clean_induction H0.
        eapply aTT_Step... apply IHaTT.
        solve_by_inverts 2.
  - destruct H as [n1 [n2 []]].
    apply aTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    intros ts [ts1 [ts2 [H []]]]. subst.
    induction H.
    + simpl. apply aTT_Step with <{n1 - a2}>.
      * clear H1. induction H...
      * clear H. induction H1...
        -- apply aTT_Term.
          remember (ANum n2) as a2.
          clean_induction H...
        -- apply aTT_Step with <{n1 - a2}>...
          induction H...
    + simpl. apply aTT_Step with <{a1 - a2}>...
      induction H...
Qed.

Lemma aTT_mult_substitutive :
  forall n a1 a2 ts,
    aTT n <{a1 * a2}> ts
      <->
    (
      exists n1 n2,
        LP{(aTT n1 a1) ; (aTT n2 a2)} ts
          /\
        n = n1 * n2
    ).
Proof with ellipsis.
  intros n a1 a2 ts. split; intros.
  - remember <{a1 * a2}> as a.
    generalize dependent a2.
    generalize dependent a1.
    clean_induction H.
    + apply mult_steps_to in H.
      destruct H; [ |destruct H].
      * destruct H as [a1' []]...
        Unshelve. apply O. apply O.
      * destruct H as [n1 [a2' [H []]]]...
        Unshelve. apply O. apply O.
      * destruct H as [n1 [n2 [H []]]].
        exists n1, n2. repeat split...
        apply mumble_1_stutter.
        apply sm_self...
    + apply mult_steps_to in H.
      destruct H; [ |destruct H].
      * destruct H as [a1' []].
        clean_apply_in IHaTT H1.
        destruct H1 as [n1 [n2 []]].
        exists n1, n2. repeat split...
        clear H0 H2 n.
        clean_induction H1; 
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H0 []]]].
        apply sm_self. 
        exists ((s, s) :: l1), l2... 
      * destruct H as [n1 [a2' [H []]]].
        clean_apply_in IHaTT H2.
        destruct H2 as [n1' [n2 []]].
        assert (n1 = n1').
        {
          remember (aTT n2 a2') as P.
          clear H H1 H3 H0 
            HeqP n a1 a2 a3 a2' n2 s.
          induction H2...
          destruct H as [l1 [_ [H _]]].
          remember (ANum n1) as a.
          clean_induction H; solve_by_inverts 2.
        }
        subst.
        exists n1', n2. repeat split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self.
        exists [(s, s)], ((s, s) :: ts).
        repeat split...
        clear H0 a1 H a2.
        apply aTT_stuttery_mumbly.
        clean_induction H2; 
          try rewrite cons_to_app3_assoc_cons...
        destruct H as [l1 [l2 [H []]]]. subst.
        apply sm_self.
        apply aTT_Step with a2'... clear H1.
        induction l1... simpl.
        invert H.
        apply aTT_Step with a2'...
        apply IHl1.
        solve_by_inverts 2.
      * clear IHaTT.
        destruct H as [n1 [n2 [H []]]].
        assert (n = n1 * n2); subst.
        {
          clear H H1.
          remember (ANum (n1 * n2)) as a.
          clean_induction H0;
            solve_by_inverts 2.
        }
        exists n1, n2. repeat split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self.
        exists [(s, s)], ((s, s) :: ts).
        repeat split...
        apply aTT_Step with n2...
        clear H H1.
        remember (ANum (n1 * n2)) as a.
        clean_induction H0.
        eapply aTT_Step... apply IHaTT.
        solve_by_inverts 2.
  - destruct H as [n1 [n2 []]].
    apply aTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    intros ts [ts1 [ts2 [H []]]]. subst.
    induction H.
    + simpl. apply aTT_Step with <{n1 * a2}>.
      * clear H1. induction H...
      * clear H. induction H1...
        -- apply aTT_Term.
          remember (ANum n2) as a2.
          clean_induction H...
        -- apply aTT_Step with <{n1 * a2}>...
          induction H...
    + simpl. apply aTT_Step with <{a1 * a2}>...
      induction H...
Qed.

Theorem aTT_equiv_semantics :
  forall n a,
    aTT n a ~ [|a -> n|].
Proof with ellipsis.
  intros n a ts. split; intros.
  - generalize dependent ts.
    generalize dependent n.
    clean_induction a.
    + apply aTT_equiv_semantics_num...
    + apply aTT_equiv_semantics_id...
    + apply aTT_plus_substitutive in H.
      destruct H as [n1 [n2 []]].
      apply ASemantics_stuttery_mumbly.
      eapply sm_closure_inner_implication;
        [ |apply H].
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H1.
      apply SmPlus. apply sm_self...
    + apply aTT_minus_substitutive in H.
      destruct H as [n1 [n2 []]].
      apply ASemantics_stuttery_mumbly.
      eapply sm_closure_inner_implication;
        [ |apply H].
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H1.
      apply SmMinus. apply sm_self...
    + apply aTT_mult_substitutive in H.
      destruct H as [n1 [n2 []]].
      apply ASemantics_stuttery_mumbly.
      eapply sm_closure_inner_implication;
        [ |apply H].
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H1.
      apply SmMult. apply sm_self...
  - apply ASemantics_equiv' in H.
    apply aTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear. intros ts H.
    generalize dependent ts.
    generalize dependent n.
    clean_induction a; invert H...
    + destruct H4 as [ts1 [ts2 [H []]]]. subst.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H0.
      apply aTT_plus_substitutive.
      exists n1, n2. repeat split...
      apply sm_self...
    + destruct H4 as [ts1 [ts2 [H []]]]. subst.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H0.
      apply aTT_minus_substitutive.
      exists n1, n2. repeat split...
      apply sm_self...
    + destruct H4 as [ts1 [ts2 [H []]]]. subst.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H0.
      apply aTT_mult_substitutive.
      exists n1, n2. repeat split...
      apply sm_self...
Qed.
      
(* bTT equiv Semantics *)

Lemma bTT_eq_substitutive :
  forall v a1 a2 ts,
    bTT v <{a1 = a2}> ts
      <->
    (
      exists n1 n2,
        LP{(aTT n1 a1) ; (aTT n2 a2)} ts
          /\
        v = (n1 =? n2)%nat
    ).
Proof with ellipsis.
  intros. split; intros.
  - remember <{a1 = a2}> as b.
    generalize dependent a2.
    generalize dependent a1.
    clean_induction H.
    + apply eq_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [a1' []]. 
        destruct v...
        Unshelve. 
          apply O. apply O. apply O. apply O.
      * destruct H as [n1 [a2' [H []]]].
        destruct v...
        Unshelve. 
          apply O. apply O. apply O. apply O.
      * destruct H as [n1 [n2 [H []]]].
        exists n1, n2. split.
        -- apply mumble_1_stutter.
          apply sm_self...
        -- destruct (n1 =? n2)%nat;
          destruct v...
    + apply eq_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [a1' []].
        clean_apply_in IHbTT H1.
        destruct H1 as [n1 [n2 []]].
        exists n1, n2. split...
        clear H0 H2.
        induction H1;
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H0 []]]].
        apply sm_self...
      * destruct H as [n1 [a2' [H []]]].
        clean_apply_in IHbTT H2.
        destruct H2 as [n1' [n2 []]].
        assert (n1 = n1'); subst.
        {
          remember (aTT n2 a2') as P.
          clear H H0 H1 a1 a2 s b1 
            HeqP n2 a2'.
          induction H2...
          destruct H as [l1 [_ [H _]]].
          remember (ANum n1) as a.
          clean_induction H;
            solve_by_inverts 2.
        }
        exists n1', n2. split...
        clear H0.
        induction H2;
          try rewrite cons_to_app3_assoc_cons...
        rewrite cons_to_app.
        apply sm_mumbly with s.
        apply sm_self.
        simpl.
        exists [(s, s)]. repeat esplit...
        apply aTT_Step with a2'...
        clear H H1 a1 s b1.
        destruct H0 as [l1 [l2 [H []]]].
        subst. induction l1... simpl.
        solve_by_inverts 3.
      * clear IHbTT.
        destruct H as [n1 [n2 [H []]]].
        assert (v = (n1 =? n2)%nat); subst.
        {
          clear H H1 a1 a2.
          destruct (n1 =? n2)%nat;
            destruct v; ellipsis; 
            exfalso; simpl in *.
          - remember <{true}> as T.
            clean_induction H0; 
              solve_by_inverts 2.
          - remember <{false}> as F.
            clean_induction H0; 
              solve_by_inverts 2.
        }
        exists n1, n2. split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self. 
        exists [(s, s)]. repeat esplit...
        eapply aTT_Step...
        remember (n1 =? n2)%nat as v.
        clear H H1 Heqv.
        remember (bool_bexp v) as b.
        clean_induction H0.
        eapply aTT_Step... apply IHbTT.
        destruct v; solve_by_inverts 2.
  - destruct H as [n1 [n2 []]].
    apply bTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    intros ts [ts1 [ts2 [H []]]]. subst.
    induction H.
    + simpl. apply bTT_Step with <{n1 = a2}>.
      * clear H1. induction H...
      * clear H. induction H1...
        -- apply bTT_Term.
          remember (ANum n2) as a2.
          clean_induction H...
        -- apply bTT_Step with <{n1 = a2}>...
          induction H...
    + simpl. apply bTT_Step with <{a1 = a2}>...
      induction H...
Qed.

Lemma bTT_le_substitutive :
  forall v a1 a2 ts,
    bTT v <{a1 <= a2}> ts
      <->
    (
      exists n1 n2,
        LP{(aTT n1 a1) ; (aTT n2 a2)} ts
          /\
        v = (n1 <=? n2)%nat
    ).
Proof with ellipsis.
  intros. split; intros.
  - remember <{a1 <= a2}> as b.
    generalize dependent a2.
    generalize dependent a1.
    clean_induction H.
    + apply le_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [a1' []]. 
        destruct v...
        Unshelve. 
          apply O. apply O. apply O. apply O.
      * destruct H as [n1 [a2' [H []]]].
        destruct v...
        Unshelve. 
          apply O. apply O. apply O. apply O.
      * destruct H as [n1 [n2 [H []]]].
        exists n1, n2. split.
        -- apply mumble_1_stutter.
          apply sm_self...
        -- destruct (n1 <=? n2)%nat;
          destruct v...
    + apply le_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [a1' []].
        clean_apply_in IHbTT H1.
        destruct H1 as [n1 [n2 []]].
        exists n1, n2. split...
        clear H0 H2.
        induction H1;
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H0 []]]].
        apply sm_self...
      * destruct H as [n1 [a2' [H []]]].
        clean_apply_in IHbTT H2.
        destruct H2 as [n1' [n2 []]].
        assert (n1 = n1'); subst.
        {
          remember (aTT n2 a2') as P.
          clear H H0 H1 a1 a2 s b1 
            HeqP n2 a2'.
          induction H2...
          destruct H as [l1 [_ [H _]]].
          remember (ANum n1) as a.
          clean_induction H;
            solve_by_inverts 2.
        }
        exists n1', n2. split...
        clear H0.
        induction H2;
          try rewrite cons_to_app3_assoc_cons...
        rewrite cons_to_app.
        apply sm_mumbly with s.
        apply sm_self.
        simpl.
        exists [(s, s)]. repeat esplit...
        apply aTT_Step with a2'...
        clear H H1 a1 s b1.
        destruct H0 as [l1 [l2 [H []]]].
        subst. induction l1... simpl.
        solve_by_inverts 3.
      * clear IHbTT.
        destruct H as [n1 [n2 [H []]]].
        assert (v = (n1 <=? n2)%nat); subst.
        {
          clear H H1 a1 a2.
          destruct (n1 <=? n2)%nat;
            destruct v; ellipsis; 
            exfalso; simpl in *.
          - remember <{true}> as T.
            clean_induction H0; 
              solve_by_inverts 2.
          - remember <{false}> as F.
            clean_induction H0; 
              solve_by_inverts 2.
        }
        exists n1, n2. split...
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self. 
        exists [(s, s)]. repeat esplit...
        eapply aTT_Step...
        remember (n1 <=? n2)%nat as v.
        clear H H1 Heqv.
        remember (bool_bexp v) as b.
        clean_induction H0.
        eapply aTT_Step... apply IHbTT.
        destruct v; solve_by_inverts 2.
  - destruct H as [n1 [n2 []]].
    apply bTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    intros ts [ts1 [ts2 [H []]]]. subst.
    induction H.
    + simpl. apply bTT_Step with <{n1 <= a2}>.
      * clear H1. induction H...
      * clear H. induction H1...
        -- apply bTT_Term.
          remember (ANum n2) as a2.
          clean_induction H...
        -- apply bTT_Step with <{n1 <= a2}>...
          induction H...
    + simpl. apply bTT_Step with <{a1 <= a2}>...
      induction H...
Qed.
        
Lemma bTT_not_substitutive :
  forall v b ts,
    bTT v <{~b}> ts
      <->
    bTT (negb v) b ts.
Proof with ellipsis.
  intros. split; intros.
  - remember <{~b}> as b0.
    generalize dependent b.
    clean_induction H.
    + apply not_steps_to in H.
      destruct H.
      * destruct H as [b' []].
        destruct v...
      * destruct H as [v' []].
        destruct v; destruct v'...
    + apply not_steps_to in H.
      destruct H.
      * destruct H as [b' []]...
      * destruct H as [v' []].
        eapply bTT_Step...
        clear IHbTT H b. subst.
        remember (bool_bexp (negb v')) as b.
        clean_induction H0; 
          destruct v'; destruct v;
          solve_by_inverts 2.
  - induction H.
    + apply bTT_Term.
      remember (bool_bexp (negb v)) as bw.
      clean_induction H.
      destruct v...
    + apply bTT_Step with <{~b1}>...
      induction H...
Qed.

Lemma bTT_and_substitutive :
  forall v b1 b2 ts,
    bTT v <{b1 && b2}> ts
      <->
    (
      bTT false b1 ts
        /\
      v = false
    )
      \/
    (
      LP{bTT true b1 ; bTT v b2} ts
    ).
Proof with ellipsis.
  intros. split; intros.
  - remember <{b1 && b2}> as b.
    generalize dependent b2.
    generalize dependent b1.
    clean_induction H.
    + apply and_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [b1' []].
        destruct v...
      * destruct H. destruct v...
      * right. destruct H.
        apply mumble_1_stutter.
        apply sm_self...
    + apply and_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [b1' []].
        clean_apply_in IHbTT H1.
        destruct H1 as [[]| ]...
        right. clear H0.
        induction H1;
          try rewrite cons_to_app3_assoc_cons...
        apply sm_self.
        destruct H0 as [l1 [l2 [H0 []]]]. subst.
        replace ((s, s) :: l1 ++ l2)
          with (((s, s) :: l1) ++ l2)...
      * clear IHbTT. destruct H. subst.
        left.
        assert (v = false)...
        clear H.
        remember <{false}> as F.
        clean_induction H0;
          destruct v; auto; 
          solve_by_inverts 2.
      * clear IHbTT. destruct H. subst.
        right.
        rewrite cons_to_app.
        apply sm_mumbly with s. simpl.
        apply sm_self. exists [(s, s)]...
  - destruct H as [[]| ]; subst.
    + induction H.
      * apply bTT_Term; simpl in *.
        apply multi_trans
          with <{false && b2}>...
        induction H...
      * apply bTT_Step with <{b1 && b2}>...
        induction H...
    + apply bTT_stuttery_mumbly.
      eapply sm_closure_inner_implication...
      clear ts H. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      induction H; simpl in *.
      * apply bTT_Step
          with <{true && b2}>...
        induction H...
      * apply bTT_Step
          with <{b1 && b2}>...
        induction H...
Qed.

Theorem bTT_equiv_semantics :
  forall v b,
    bTT v b ~ [|b ->b v|].
Proof with ellipsis.
  intros v b ts. split; intros.
  - generalize dependent ts.
    generalize dependent v.
    clean_induction b.
    + remember <{true}> as T.
      clean_induction H.
      * invert H; destruct v...
        eapply SmTrue. eapply sm_self...
      * invert H...
        rewrite cons_to_app.
        apply BSemantics_stuttery_mumbly...
    + remember <{false}> as F.
      clean_induction H.
      * invert H; destruct v...
        eapply SmFalse. eapply sm_self...
      * invert H...
        rewrite cons_to_app.
        apply BSemantics_stuttery_mumbly...
    + apply bTT_eq_substitutive in H.
      destruct H as [n1 [n2 []]].
      apply BSemantics_stuttery_mumbly.
      eapply sm_closure_inner_implication;
        [ |apply H].
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      apply aTT_equiv_semantics in H.
      apply aTT_equiv_semantics in H1.
      apply SmEq. apply sm_self...
    + apply bTT_le_substitutive in H.
      destruct H as [n1 [n2 []]].
      apply BSemantics_stuttery_mumbly.
      eapply sm_closure_inner_implication;
        [ |apply H].
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      apply aTT_equiv_semantics in H.
      apply aTT_equiv_semantics in H1.
      apply SmLe. apply sm_self...
    + apply bTT_not_substitutive in H.
      remember (negb v) as v'.
      replace v with (negb v') in *
        by (subst; destruct v; auto).
      apply SmNot...
    + apply bTT_and_substitutive in H.
      destruct H as [[]| ]; subst.
      * apply SmAndFalse...
      * apply SmAndTrue...
        eapply sm_closure_inner_implication...
        clear H ts.
        intros ts [ts1 [ts2 [H []]]]. subst.
        clean_apply_in IHb1 H.
        clean_apply_in IHb2 H0...
  - apply BSemantics_equiv' in H.
    apply bTT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear. intros ts H.
    generalize dependent ts.
    generalize dependent v.
    clean_induction b; invert H...
    + destruct H4 as [ts1 [ts2 [H []]]]. subst.
      apply sm_self in H.
      apply ASemantics_equiv' in H.
      apply aTT_equiv_semantics in H.
      apply sm_self in H0.
      apply ASemantics_equiv' in H0.
      apply aTT_equiv_semantics in H0.
      apply bTT_eq_substitutive.
      exists n1, n2. repeat split...
      apply sm_self...
    + destruct H4 as [ts1 [ts2 [H []]]]. subst.
      apply sm_self in H.
      apply ASemantics_equiv' in H.
      apply aTT_equiv_semantics in H.
      apply sm_self in H0.
      apply ASemantics_equiv' in H0.
      apply aTT_equiv_semantics in H0.
      apply bTT_le_substitutive.
      exists n1, n2. repeat split...
      apply sm_self...
    + clean_apply_in IHb H1.
      apply bTT_not_substitutive.
      destruct v0...
    + clean_apply_in IHb1 H4.
      apply bTT_and_substitutive...
    + destruct H4 as [ts1 [ts2 [H []]]]. subst.
      clean_apply_in IHb1 H.
      clean_apply_in IHb2 H0.
      apply bTT_and_substitutive. right.
      apply sm_self...
Qed.

(* com *)

Theorem TT_asgn_substitutive : 
  forall i a ts,
    TT <{i:=a}> ts 
      <->
    exists n s,
      LP{aTT n a ; [(s, i |-> n; s)]} ts.
Proof with ellipsis.
intros; split; intros.
  - remember <{ i := a }> as c.
    generalize dependent a.
    induction H; intros; subst.
    + remember (<{i:=a}>, s0) as cf0 eqn:E0.
      remember (<{ skip }>, s1) as cf1 eqn:E1.
      generalize dependent a.
      induction H; intros; subst; try clean_inversion E0.
      clean_inversion H.
      * apply asgn_steps_to in H0...
        destruct H0; destruct H; destruct H; 
          destruct H0; clean_inversion H0.
        subst. clear IHmulti. 
        rename x into n. exists n, s0.
        replace [(s0, i |-> n; s0)]
          with ([] ++ [(s0, i |-> n; s0)] ++ [])...
        apply sm_mumbly with s0. simpl.
        apply sm_self...
      * invert H0...        
        exists n, s0.
        replace [(s0, i |-> n; s0)]
          with ([] ++ [(s0, i |-> n; s0)] ++ [])...
        apply sm_mumbly with s0. simpl.
        apply sm_self.
        exists [(s0, s0)]...
        Unshelve.
          apply O. auto.
    + apply asgn_steps_to in H.
      destruct H; destruct H; destruct H; destruct H1...
      * subst.
        assert (<{ i := x }> = <{ i := x }>)...
        apply IHTT in H1... clear IHTT.
        destruct H1 as [n].
        exists n.
        destruct H1 as [s].
        exists s.
        clear H0.
        induction H1;
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H0 []]]]. subst.
        apply sm_self...
      * rename x into n. exists n. 
        clear IHTT. subst.
        exists s0.
        replace ((s0, i |-> n; s0) :: ts)
          with ([] ++ [(s0, i |-> n; s0)] ++ ts)...
        apply sm_mumbly with s0. simpl.
        remember <{skip}> as c.
        clean_induction H0.
        -- invert H0...
          replace 
            [(s0, s0); (s0, i |-> n; s0); (s2, s2)]
          with
            ([(s0, s0); (s0, i |-> n; s0)] ++ [(s2, s2)] ++ [])...
          apply sm_stuttery. simpl.
          apply sm_self...
        -- invert H0...
          replace
            ((s0, s0) :: (s0, i |-> n; s0) :: (s2, s2) :: ts)
          with
            ([(s0, s0); (s0, i |-> n; s0)] ++ [(s2, s2)] ++ ts)...
  - destruct H as [n [s]].
    apply TT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear. intros ts [ts1 [ts2 [H []]]].
    invert H0.
    induction H.
    + apply TT_Step with <{i:=n}>...
      induction H...
    + apply TT_Step with <{i:=a1}>...
      induction H...
Qed.


Theorem TT_seq_substitutive :
  forall c1 c2 ts,
    TT <{c1; c2}> ts
      <->
    LP{TT c1 ; TT c2} ts.
Proof with ellipsis.
  intros. split; intros.
  - remember <{ c1; c2 }> as c.
    generalize dependent c2.
    generalize dependent c1.
    induction H; intros; subst.
    + apply seq_steps_to in H.
      destruct H; destruct H; destruct H...
      rewrite cons_to_app.
      apply sm_mumbly with x. simpl.
      apply sm_self...
    + rename c1 into c.
      rename c2 into c1.
      rename c3 into c2.
      apply seq_steps_to in H.
      destruct H; destruct H; destruct H...
      * rename x into c1'.
        apply IHTT in H1. 
        clear IHTT H0 c.
        induction H1;
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H0 []]]]. subst.
        apply sm_self.
        exists ((s0, s1) :: l1). esplit...
      * rename x into s'. clear IHTT.
        rewrite cons_to_app.
        apply sm_mumbly with s'. simpl.
        apply sm_self.
        exists [(s0, s')]. esplit...
  - apply TT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    intros ts [ts1 [ts2 [H []]]]. subst.
    induction H; simpl...
    + apply TT_Step with c2...
      remember (c0, s0) as cf0.
      remember (<{skip}>, s1) as cf1.
      generalize dependent s0.
      generalize dependent c0.
      clean_induction H...
    + eapply TT_Step...
      clear IHTT H1 H0.
      remember (c0, s0) as cf0.
      remember (c1, s1) as cf1.
      generalize dependent s0.
      generalize dependent c0.
      clean_induction H...
Qed.

Theorem TT_if_substitutive :
forall c1 c2 b ts,
    TT <{if b then c1 else c2 end}> ts
      <->
    (
      LP{bTT true b; TT c1} ts
        \/
      LP{bTT false b; TT c2} ts
    ).
Proof with ellipsis.
  intros; split; intros.
  - remember <{ if b then c1 else c2 end }> as c.
    generalize dependent b.
    induction H; intros; subst.
    + apply if_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [b' [H []]]...
      * destruct H. left.
        rewrite cons_to_app.
        apply sm_mumbly with s0. simpl.
        apply sm_self...
      * destruct H. right.
        rewrite cons_to_app.
        apply sm_mumbly with s0. simpl.
        apply sm_self...
    + apply if_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [b' [H []]]. subst.
        assert (<{ if b' then c1 else c2 end }> 
          = <{ if b' then c1 else c2 end }>)...
        clean_apply_in IHTT H1. destruct H1.
        -- left.
          clear H0.
          induction H1; subst;
            try rewrite cons_to_app3_assoc_cons...
          destruct H0 as [l1 [l2 [H0 []]]]. subst.
          apply sm_self...
        -- right.
          clear H0.
          induction H1; subst;
            try rewrite cons_to_app3_assoc_cons...
          destruct H0 as [l1 [l2 [H0 []]]]. subst.
          apply sm_self...
      * destruct H. clear IHTT. left.
        rewrite cons_to_app.
        apply sm_mumbly with s0... simpl.
        apply sm_self. exists [(s0, s0)]...
      * destruct H. clear IHTT. right.
        rewrite cons_to_app.
        apply sm_mumbly with s0... simpl.
        apply sm_self. exists [(s0, s0)]...
  - destruct H.
    + apply TT_stuttery_mumbly.
      eapply sm_closure_inner_implication...
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      induction H; simpl...
      * apply TT_Step with c1...
        simpl in H.
        remember <{true}> as T.
        clean_induction H...
      * eapply TT_Step; [ |apply IHbTT]...
        induction H...
    + apply TT_stuttery_mumbly.
      eapply sm_closure_inner_implication...
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      induction H; simpl...
      * apply TT_Step with c2...
        simpl in H.
        remember <{false}> as T.
        clean_induction H...
      * eapply TT_Step; [ |apply IHbTT]...
        induction H...
Qed.

Theorem TT_par_substitutive :
  forall c1 c2 ts,
    TT <{c1||c2}> ts 
      <->
    LP{TT c1 || TT c2} ts.
Proof with ellipsis.
  intros; split; intros.
  - remember <{c1 || c2}> as c'.
    generalize dependent c1.
    generalize dependent c2.
    induction H; intros; subst.
    + remember (<{c1 || c2}>, s0) as cf0 eqn:E0.
      remember (<{ skip }>, s1) as cf1 eqn:E1.
      generalize dependent s0.
      generalize dependent c2.
      generalize dependent c1.
      induction H; intros; subst...
      clean_inversion H.
      * assert (LP{TT c1' || TT c2} [(s', s1)])...
        clear IHmulti H0.
        rewrite cons_to_app.
        apply sm_mumbly with s'. simpl.
        induction H;
          try rewrite cons_to_app3_assoc_cons...
        destruct H as [l1 [l2 [H []]]].
        apply sm_self.
        exists ((s0, s') :: l1), l2... 
      * assert (LP{TT c1 || TT c2'} [(s', s1)])...
        clear IHmulti H0.
        rewrite cons_to_app.
        apply sm_mumbly with s'. simpl.
        induction H;
          try rewrite cons_to_app3_assoc_cons...
        destruct H as [l1 [l2 [H []]]].
        apply sm_self.
        exists l1, ((s0, s') :: l2)... 
      * clean_inversion H0...
        clear IHmulti.
        apply mumble_1_stutter.
        apply sm_self...
    + remember (<{c3 || c2}>, s0) as cf0 eqn:E0.
      remember (c1, s1) as cf1 eqn:E1.
      generalize dependent s0.
      generalize dependent c2.
      generalize dependent c3.
      induction H; intros; subst.
      * clean_inversion E0.
        assert (<{ c3 || c2 }> = <{ c3 || c2 }>)...
        clean_apply_in IHTT H.
        rewrite cons_to_app...
      * clean_inversion H.
        -- assert ((c1, s1) = (c1, s1))...
          specialize IHmulti 
            with c1' c2 s'.
          clean_apply_in IHmulti H.
          clear IHTT H1 H0.
          rewrite cons_to_app.
          apply sm_mumbly with s'. simpl.
          induction H;
            try rewrite cons_to_app3_assoc_cons...
          destruct H as [l1 [l2 [H []]]].
          apply sm_self.
          exists ((s0, s') :: l1), l2...
        -- assert ((c1, s1) = (c1, s1))...
          specialize IHmulti 
            with c3 c2' s'.
          clean_apply_in IHmulti H.
          clear IHTT H1 H0.
          rewrite cons_to_app.
          apply sm_mumbly with s'. simpl.
          induction H;
            try rewrite cons_to_app3_assoc_cons...
          destruct H as [l1 [l2 [H []]]].
          apply sm_self.
          exists l1, ((s0, s') :: l2)...
        -- invert H1... 
          clear IHmulti IHTT.
          apply sm_self.
          exists [(s1, s1)]. repeat esplit...
          clear.
          apply int_cons1.
          induction ts...
  - apply TT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear. intros ts [ts1 [ts2 [H []]]]. subst.
    generalize dependent c2.
    generalize dependent c1.
    clean_induction H1...
    + invert H.
      * apply TT_Step with <{skip||c2}>.
        -- remember (c1, s0) as cf eqn:E.
          remember (<{skip}>, s1) as cf' eqn:E'.
          generalize dependent s0.
          generalize dependent c1.
          clean_induction H4...
        -- clear IHinterwoven H4 c1 s0 s1. 
          assert (l2 = l); subst.
          {
            clear H0 c2.
            remember [] as n.
            clean_induction H1...
            assert (l2 = l)...
          }
          clear H1.
          induction H0.
          ++ apply TT_Term.
            remember (c0, s0) as cf0.
            remember (<{skip}>, s1) as cf1.
            generalize dependent s0.
            generalize dependent c0.
            clean_induction H...
          ++ eapply TT_Step...
            remember (c0, s0) as cf0.
            remember (c1, s1) as cf1.
            generalize dependent s0.
            generalize dependent c0.
            clean_induction H...
      * eapply TT_Step...
        remember (c1, s0) as cf eqn:E.
        remember (c3, s1) as cf' eqn:E'.
        generalize dependent s0.
        generalize dependent c1.
        clean_induction H5...
    + invert H0.
      * apply TT_Step with <{c1||skip}>.
        -- remember (c2, s0) as cf eqn:E.
          remember (<{skip}>, s1) as cf' eqn:E'.
          generalize dependent s0.
          generalize dependent c2.
          clean_induction H4...
        -- clear IHinterwoven H4 c2 s0 s1. 
          assert (l1 = l); subst.
          {
            clear H c1.
            remember [] as n.
            clean_induction H1...
            assert (l1 = l)...
          }
          clear H1.
          induction H.
          ++ apply TT_Term.
            remember (c0, s0) as cf0.
            remember (<{skip}>, s1) as cf1.
            generalize dependent s0.
            generalize dependent c0.
            clean_induction H...
          ++ eapply TT_Step...
            remember (c0, s0) as cf0.
            remember (c1, s1) as cf1.
            generalize dependent s0.
            generalize dependent c0.
            clean_induction H...
      * eapply TT_Step...
        remember (c2, s0) as cf eqn:E.
        remember (c3, s1) as cf' eqn:E'.
        generalize dependent s0.
        generalize dependent c2.
        clean_induction H5...
Qed.
          
Theorem TT_await_substitutive :
  forall c b ts,
    TT <{await b then c end}> ts
      <->
    (
      exists s0 s1,
        b / s0 -->b* <{true}>
          /\
        c / s0 -->* <{skip}> / s1
          /\
        LP{[(s0, s1)]^} ts
    ).
Proof with ellipsis.
  intros. split; intros.
  - remember <{ await b then c end }> as c'.
    clean_induction H...
    + remember (<{ await b then c end }>, s0) as cf0.
      remember (<{ skip }>, s1) as cf1.
      clean_induction H...
      invert H.
      assert (s' = s1) by solve_by_inverts 2.
      exists s0, s'.
      repeat split... apply sm_self...
      subst...
      Unshelve.
      auto. auto.
    + remember (<{ await b then c end }>, s0) as cf0.
      remember (c1, s1) as cf1.
      clean_induction H.
      * clean_inversion Heqcf1.
        assert (<{await b then c end}>
            = <{await b then c end}>)...
        clean_apply_in IHTT H.
        destruct H as [s0 [s2 [H []]]].
        exists s0, s2. repeat split...
        replace ((s1, s1) :: ts)
          with ([] ++ [(s1, s1)] ++ ts)...
      * clean_inversion H.
        clear IHmulti.
        clean_inversion H1...
         exists s0, s1. repeat split...
        clear IHTT H6 H7 c.
        remember <{skip}> as c.
        clean_induction H0.
        -- invert H...
          replace [(s0, s1); (s3, s3)]
            with ([(s0, s1)] ++ [(s3, s3)] ++ nil)...
          apply sm_stuttery.
          apply sm_self...
        -- invert H...
          replace ((s0, s1) :: (s3, s3) :: ts)
            with ([(s0, s1)] ++ [(s3, s3)] ++ ts)...
  - destruct H as [s0 [s1 [H []]]].
    apply TT_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H1 ts. intros ts H1...
Qed.