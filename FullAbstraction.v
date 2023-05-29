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
From WS  Require Import TransitionTrace.
From WS  Require Import TTequivSemantics.

(* auxiliary destinations *)

(* Fixpoint is_state is (s : state) :=
  match is with
  | nil     => <{true}>
  | i :: is => <{i = (s i) && (is_state is s)}>
  end. *)

Fixpoint make_state is (s : state) :=
  match is with
  | nil     => <{skip}>
  | i :: is => <{i := (s i); (make_state is s)}>
  end.

Fixpoint do_tt is (ts : transitions) :=
  match ts with
  | nil             => <{skip}>
  | (s0, s0') :: ts => match ts with
    | nil            => <{skip}>
    | (s1, s1') :: _ => <{
        await (is_state is s0') then 
          (make_state is s1) 
        end; 
        do_tt is ts
      }>
    end
  end.

(* claims *)

Lemma make_state_self :
  forall s0 s1,
    make_state dom s1 / s0 -->* <{skip}> / s1.
Proof with ellipsis.
  intros.
  assert (forall i, i /: dom -> s0 i = s1 i).
  { intros. apply_contra H. apply dom_full. }
  generalize dependent s0.
  induction dom as [ |i is]; intros; 
    simpl in *.
  - assert (s0 = s1)... apply states_equal.
    intros...
  - eapply multi_step... eapply multi_step...
    apply IHis. intros j H0.
    assert (j = i \/ j <> i) 
      by apply identifier_eq_dec.
    destruct H1; subst.
    + apply update_s_eq.
    + replace (s1 j) with (s0 j);
        try apply update_s_neq...
      apply H. intros [C|C]...
Qed.

Lemma make_state_makes :
  forall s s1 s2,
    make_state dom s1 / s -->* <{skip}> / s2
      ->
    s1 = s2.
Proof with ellipsis.
  intros. apply states_equal. intros j.
  assert (j <: dom) by apply dom_full.
  generalize dependent s.
  induction dom as [ |i is]; intros; subst...
  simpl in H0. destruct H0; subst; simpl in *.
  - remember (s1 j) as n. clear Heqn.
    invert H. invert H0. invert H5...
    invert H1. invert H... 
    assert (j <: is \/ j /: is) 
      by apply in_identifiers_dec.
    destruct H...
    replace n with ((j |-> n; s) j)
      by apply update_s_eq.
    remember (j |-> n; s) as s'. 
    clear Heqs' IHis n s.
    generalize dependent s'.
    clean_induction is; simpl in *.
    + solve_by_inverts 2.
    + invert H0. invert H1. invert H6...
      invert H2. invert H0...
      assert ((a |-> s1 a; s') j = s' j)...
      apply update_s_neq...
  - eapply IHis...
    invert H. invert H1. invert H6...
    invert H2. invert H...
Qed.

Lemma TT_from_PC :
  forall c s0 s0' sw sw' ts,
    TT c ((s0, s0') :: ts ++ [(sw, sw')])
      <->
    PC <{
      c
        ||
      do_tt dom ((s0, s0') :: ts ++ [(sw, sw')])
    }> (s0, sw').
Proof with ellipsis.
  intros; split; intros;
    replace ((s0, s0') :: ts ++ [(sw, sw')])
      with  (((s0, s0') :: ts) ++ [(sw, sw')]) 
      in H by ellipsis;
    remember ((s0, s0') :: ts) as ts';
    generalize dependent ts;
    generalize dependent s0';
    generalize dependent s0;
    generalize dependent c;
    clean_induction ts'; ellipsis;
    invert Heqts'.
  - simpl in H. invert H; 
      destruct ts as [ |[s1 s1'] ts]...
    + invert H5...
      apply multi_trans with (
        <{
          c1
            ||
          do_tt dom ((s0, s0') :: [] ++ [(sw, sw')])
        }>,
        s0'
      ); try apply multi_step_par1...
      eapply multi_step.
      * apply CS_Par2. simpl.
        apply CS_SeqStep.
        apply CS_AwaitTrue.
        -- apply is_state_self.
        -- apply make_state_self.
      * apply multi_trans with (
          <{skip||skip;skip}>, sw'
        )...
        apply multi_step_par1...
    + invert H5...
      { destruct ts... }
      apply multi_trans with (
        <{
          c1
            ||
          do_tt dom ((s0, s0') :: ((s1, s1') :: ts) 
              ++ [(sw, sw')])
        }>,
        s0'
      ); try apply multi_step_par1...
      eapply multi_step; [ |eapply multi_step].
      * apply CS_Par2. simpl.
        apply CS_SeqStep.
        apply CS_AwaitTrue.
        -- apply is_state_self.
        -- apply make_state_self.
      * apply CS_Par2. apply CS_SeqFinish.
      * apply IHts'...
  - unfold PC in H.
    remember <{
      c 
        || 
      do_tt dom (((s0, s0') :: ts) ++ [(sw, sw')])
    }> as c0.
    remember (c0, s0) as cf0 eqn:E0.
    remember (<{skip}>, sw') as cfw eqn:Ew.
    generalize dependent s0'.
    generalize dependent s0.
    generalize dependent c0.
    generalize dependent c.
    clean_induction H...
    invert H.
    + specialize IHmulti with (c:=c1') (s0:=s').
      assert ((<{skip}>, sw') = (<{skip}>, sw'))...
      clean_apply_in IHmulti H...
    + destruct ts as [ |[s1 s1'] ts]; simpl in H5.
      * invert H5. invert H1. clear IHmulti.
        apply is_state_is in H3.
        apply make_state_makes in H7. subst.
        eapply TT_Step... simpl.
        apply par2_skip_seq_normilization 
          in H0...
        apply par_bottleneck in H0.
        apply multi_step_par_skip in H0...
      * invert H5. invert H1. clear IHmulti.
        apply is_state_is in H3.
        apply make_state_makes in H7. subst.
        eapply TT_Step... simpl.
        apply IHts'... simpl.
        apply par2_skip_seq_normilization 
          in H0...
    + destruct ts as [ |[s1 s1'] ts]...
Qed.