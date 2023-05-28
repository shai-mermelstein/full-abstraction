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
From WS  Require Import Contexts.
From WS  Require Import PartialCorrectness.
From WS  Require Import StateTrace.
From WS  Require Import Semantics.
From WS  Require Import StepsTo.

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

Definition bool_bexp (v : bool) : bexp :=
  if v then <{true}> else <{false}>.

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
      
      


(* 
Lemma plus_steps_to :
  forall a1 a2 a s,
    <{a1 + a2}> / s -->a* a
      ->
    (
      exists a1',
        a1 / s -->* a1'
          /\
        a = <{a1' + a2}>
    )
      \/
    (
      exists n1 a2',
        a1 / s -->* n1
          /\
        a2 / s -->* n2
          /\
        a = <{a1' + a2}>
    )

Lemma aTT_equiv_semantics_plus :
  forall n a1 a2,
    aTT n <{a1 + a2}> ~ [|a1 + a2 -> n|].
Proof with ellipsis.
  intros n a1 a2 ts. split; intros.
  - remember <{a1 + a2}> as a.
    generalize dependent a2.
    generalize dependent a1.
    clean_induction H.
    + admit.
    + 



Theorem aTT_equiv_semantics :
  forall n a,
    aTT n a ~ [|a -> n|].
Proof with ellipsis.
  intros n a ts. split; intros.
  - induction a.
    + remember (ANum n0) as a. 
      assert (n0 = n).
      { induction H; invert H... } 
      rewrite H0 in *. clear H0. 
      clean_induction H.
      * eapply SmNum. apply sm_self...
      * invert H...
        apply ASemantics_stuttery_mumbly.
        rewrite cons_to_app...
    + remember (AId i) as a.
      clean_induction H.
      * invert H. invert H0.
        invert H1...
        eapply SmId. apply sm_self...
      * invert H.
        -- apply ASemantics_stuttery_mumbly.
          rewrite cons_to_app...
        -- invert H1.
          assert (a1 = n).
          {

          }
          eapply SmId. with s.
      


      assert (n0 = n).
      { induction H; invert H... } 
      rewrite H0 in *. clear H0. 
      clean_induction H.
      * eapply SmNum. apply sm_self...
      * invert H...
        apply ASemantics_stuttery_mumbly.
        rewrite cons_to_app...
       
      induction H.
      * clean_induction H...
        apply SMNum
    
    
    induction H.
    + induction a0.
      * remember n0 as a.
        induction H.
         eapply SmNum. 

 *)
