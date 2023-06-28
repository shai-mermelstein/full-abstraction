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
From WS  Require Import Contexts.

(* 
  This file is roughly equivalent to section 7
    (Full Abstraction) in Brookes's paper.
  It will show that the semantics defined in
    'Semantics.v' are fully abstract.
*)

(* auxiliary destinations *)

(* 
  Equivalent to Brookes IS_s
  Copied from STequivPC.v for reference.

Fixpoint is_state is (s : state) :=
  match is with
  | nil     => <{true}>
  | i :: is => <{i = (s i) && (is_state is s)}>
  end. 
*)

(* 
  Corresponds to the MAKE_s command defined by
    Brookes. Explicitly, MAKE_s corresponds to
    'make_state dom s'.
  Constructed s.t. (make_state dom s, s') -->* (skip, s)
    forall s'.
*)
Fixpoint make_state is (s : state) :=
  match is with
  | nil     => <{skip}>
  | i :: is => <{i := (s i); (make_state is s)}>
  end.

(* 
  Corresponds to the DO_a command defined by
    Brookes. Explicitly, DO_a corresponds to
    'do_tt dom a.
  Note that for ease of definition, an extra 
    <{skip}> is appended to the end of the command,
    when compared to Brookes's definition.
*)
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

(* 
  The aforementioned key property of make_state.
*)
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

(* 
  A useful observation (the corresponding uniqueness 
    claim to the previous claim).
*)
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

(* 
  A key lemma for proving full abstraction.
  This lemma allows us to convert statements 
    using transition traces (TT) to statements 
    using partial correctness (PC).
  Brookes essentially proves this lemma as part 
    of his proof of full abstraction (proposition 7.1).
*)
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

(* 
  Brookes proves this as part  of his proof 
    of full abstraction (proposition 7.1).
  A corollary of substitute nature of [| |],
    if one program is 'contained' in another,
    then iit will remain true in any context.
*)
Theorem Semantics_substitutive :
  forall c c' cxt,
    [|c|] =>> [|c'|]
      ->
    [|plug cxt c|] =>> [|plug cxt c'|].
Proof with ellipsis.
  intros.
  clean_induction cxt; 
    intros l H0; invert H0;
    apply CSemantics_stuttery_mumbly;
    (eapply sm_closure_implication; [ |eauto]);
    try (clear H4 l; 
      intros l [l1 [l2 [H0 []]]]; subst);
    try (clear H5 l; 
      intros l [l1 [l2 [H0 []]]]; subst).
  + apply SmSeq. apply sm_self...
  + apply SmSeq. apply sm_self...
  + apply SmIfTrue. apply sm_self...
  + apply SmIfFalse. apply sm_self...
  + apply SmIfTrue. apply sm_self...
  + apply SmIfFalse. apply sm_self...
  + apply SmWhile. apply sm_self.
    exists l1. repeat esplit... clear H1 l2.
    eapply star_implication; [ |eauto].
    clear H0 l1. intros l H0.
    eapply sm_closure_implication; [ |eauto].
    clear H0 l. intros l [l1 [l2 [H0 []]]]...
  + apply SmPar. apply sm_self...
  + apply SmPar. apply sm_self...
  + clear H6 l. intros l H0. invert H0.
    eapply SmAwait... apply sm_self...
Qed.

(* 
  Full abstraction proof (proposition 7.1).
*)
Theorem Semantics_equiv_PC : (* Full abstraction! *)
  forall c c', 
    [|c|] =>> [|c'|] <-> c <pc c'.
Proof with ellipsis.
  unfold "<pc", "[pc".
  intros; split; intros; intros t H0.
  - rewrite PC_from_TT in *.
    apply TT_equiv_Semantics.
    apply TT_equiv_Semantics in H0.
    eapply Semantics_substitutive...
  - destruct t as [ |t0 ts].
    {  apply nil_not_in_CSemantics in H0... }
    apply TT_equiv_Semantics.
    apply TT_equiv_Semantics in H0.
    destruct ts as [ |t' ts'].
    { 
      apply PC_from_TT.
      apply PC_from_TT in H0.
      specialize H with CXTHole...
    }
    assert (
      exists tw ts, t' :: ts' = ts ++ [tw]
    ).
    { 
      clear. induction ts'.
      - exists t', nil...
      - destruct IHts' as [tw [ts]].
        destruct ts.
        + destruct ts'... invert H.
          exists a, [tw]...
        + simpl in H. invert H.
          exists tw, (p :: a :: ts)...
      Unshelve.
      auto. auto.
    }
    destruct H1 as [tw [ts]]. 
    rewrite H1 in *. clear H1 t' ts'.
    destruct t0 as [s0 s0'].
    destruct tw as [sw sw'].
    apply TT_from_PC.
    apply TT_from_PC in H0.
    remember (
      do_tt dom ((s0, s0') :: ts ++ [(sw, sw')])
    ) as cr. clear Heqcr.
    specialize H with (CXTPar1 CXTHole cr)...
Qed.
    