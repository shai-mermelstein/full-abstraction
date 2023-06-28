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
From WS  Require Import StateTrace.
From WS  Require Import TransitionTrace.
From WS  Require Import TTequivSemantics.
From WS  Require Import Contexts.
From WS  Require Import FullAbstraction.

(* 
  This file contains as assortment of examples 
    form Brookes or similar to his.
*)

(* 
  An example showing that PC-preorder does not
   imply ST-preorder.
  Brookes uses <{X := 1; X := X + 1}> & <{X := 2}>
    for this end. 
  However, proving that using fine-grained semantics
    is not simple, and it is also unnecessary,
    as demonstrated.
*)
Example PC_doesn't_imply_ST :
  <{X := 1; X := 2}> [pc <{X := 2}>
    /\
  ~ <{X := 1; X := 2}> [st <{X := 2}>.
Proof with ellipsis.
  split; intros.
  - intros [s0 sw] H. unfold PC in *.
    invert H. invert H0. invert H5...
    invert H1. invert H...
    invert H0. invert H...
    invert H1...
    assert (
      (X |-> 2; X |-> 1; s0)
        =
      (X |-> 2; s0)
    )...
    + apply states_equal. intros.
      unfold update_s. 
      destruct (v =? X)...
    + rewrite H...
  - intros C.
    assert (ST <{X := 2}> [empty_s ; (X |-> 1); (X |-> 2)]).
    + apply C.
      apply ST_Step with <{X := 2}>...
      replace (X |-> 2) with (X |-> 2; X |-> 1)...
      apply states_equal. intros.
      unfold update_s.  destruct (v =? X)...
    + clear C.
      invert H. invert H3.
      * assert (empty_s X = (X |-> 1) X)...
        unfold empty_s, update_s in H.
        destruct (X =? X) eqn:E...
        eapply ieq_iff_neq...
      * invert H... invert H0...
        assert ((X |-> 2) X = (X |-> 1) X)...
        unfold update_s in H.
        destruct (X =? X) eqn:E...
        eapply ieq_iff_neq...
Qed.

(* 
  Proposition 8.1 of Brookes - laws of parallel programming
*)
Theorem law_of_parallel_programming_1: 
  forall c, 
    [|c|] <=> [|c ; skip|].
Proof with ellipsis.
  split; repeat intro.
   - apply SmSeq.
    destruct a.
    { apply nil_not_in_CSemantics in H... }
    assert (
      exists a' p', p :: a = a' ++ [p']
    ).
    { 
      clear H c.
      remember (p :: a) as l.
      generalize dependent a.
      generalize dependent p.
      clean_induction l...
      invert Heql.
      destruct a0.
      - exists [], p...
      - assert (p0 :: a0 = p0 :: a0)...
        clean_apply_in IHl H.
        destruct H as [a' [p']].
        exists (p :: a'), p'...
      Unshelve.
      auto. auto.
    }
    destruct H0 as [a' [[s s']]]. rewrite H0 in *. 
    clear H0 a p.
    replace (a' ++ [(s, s')])
      with (a' ++ [(s, s')] ++ [])...
    apply sm_mumbly with s'. simpl.
    replace (a' ++ [(s, s'); (s', s')])
      with ((a' ++ [(s, s')]) ++ [(s', s')]) 
      by (rewrite <- app_assoc; eauto).
    apply sm_self. 
    exists (a' ++ [(s, s')]), [(s', s')].
    repeat split...
    eapply SmSkip. apply sm_self...
  - invert H.
    apply CSemantics_stuttery_mumbly.
    eapply sm_closure_implication'...
    clear H3 a. intros ts [ts1 [ts2 [H []]]].
    subst.
    invert H0. induction H1.
    + invert H0.
      replace (ts1 ++ [(s, s)])
        with (ts1 ++ [(s, s)] ++ [])...
      apply sm_stuttery.
      rewrite <- app_nil_end...
    + rewrite app_assoc in *.
      apply sm_stuttery...
    + rewrite app_assoc in *.
      eapply sm_mumbly...
Qed.

Theorem law_of_parallel_programming_2: 
  forall c1 c2 c3, 
    [|(c1; c2); c3|] <=> [|c1; (c2; c3)|].
Proof with ellipsis.
  intros. split; repeat intro.
  - apply CSemantics_equiv'.
    apply CSemantics_equiv' in H.
    apply sm_closure_implication
      with [|(c1; c2); c3|]'...
    clear H a. intros ts H.
    invert H. destruct H3 as [ts1 [ts2 [H []]]].
    invert H. destruct H5 as [ts1' [ts1'' [H []]]].
    subst.
    rewrite <- app_assoc.
    apply SmSeq'.
    exists ts1', (ts1'' ++ ts2). repeat split...
    apply SmSeq'...
  - apply CSemantics_equiv'.
    apply CSemantics_equiv' in H.
    apply sm_closure_implication
      with [|c1; (c2; c3)|]'...
    clear H a. intros ts H.
    invert H. destruct H3 as [ts1 [ts2 [H []]]].
    invert H0. destruct H5 as [ts2' [ts2'' [H0 []]]].
    subst.
    rewrite app_assoc.
    apply SmSeq'.
    exists (ts1 ++ ts2'), ts2''. repeat split...
    apply SmSeq'...
Qed.

Lemma semantics_implication_via':
  forall c1 c2,
    [|c1|]' =>> [|c2|]'
      ->
    [|c1|] =>> [|c2|].
Proof with ellipsis.
  intros. intros ts H0.
  apply sm_closure_implication in H.
  apply CSemantics_equiv' in H0.
  apply H in H0.
  apply CSemantics_equiv'...
Qed.
    
(* 
  Brookes only states the first direction,
    as he is referring to rough-grain semantics,
    in which the second program allows
    context switches between the evaluation of
    b1 and b2, but the first program doesn't.
  However, in fine-grained semantics this
    distinction is lost, and we have full
    equivalence.
*)
Theorem law_of_parallel_programming_3: 
  forall b1 b2 c1 c2,
    [|if b1 && b2 then c1 else c2 end|]
      <=>
    [|if b1 then if b2 then c1 else c2 end else c2 end|].
Proof with ellipsis.
  intros. split; intros.
  - eapply semantics_implication_via'; 
      [ |eassumption].
    clear H a. intros ts H.
    invert H; 
      destruct H4 as [ts1 [ts2 [? []]]]; subst;
      invert H.
    + destruct H5 as [ts1' [ts1'' [? []]]]. subst.
      rewrite <- app_assoc.
      apply SmIfTrue'.
      exists ts1', (ts1'' ++ ts2). repeat split...
      apply SmIfTrue'...
    + apply SmIfFalse'...
    + destruct H5 as [ts1' [ts1'' [? []]]]. subst.
      rewrite <- app_assoc.
      apply SmIfTrue'.
      exists ts1', (ts1'' ++ ts2). repeat split...
      apply SmIfFalse'...
  - eapply semantics_implication_via'; 
      [ |eassumption].
    clear H a. intros ts H.
    invert H; 
      destruct H4 as [ts1 [ts2 [? []]]]; subst.
    + invert H0;
        destruct H5 as [ts1' [ts1'' [? []]]]; subst;
        rewrite app_assoc.
      * apply SmIfTrue'.
        repeat eexists...
        apply SmAndTrue'...
      * apply SmIfFalse'.
        repeat eexists...
        apply SmAndTrue'...
    + apply SmIfFalse'. 
      repeat eexists...
      apply SmAndFalse'...
Qed.

Theorem law_of_parallel_programming_4: 
  forall b c,
    [|while b do c end|]
      <=>
    [|if b then c; while b do c end else skip end|].
Proof with ellipsis.
  intros; split; intros;
    apply TT_equiv_Semantics;
    apply while_equiv_if_while;
    apply TT_equiv_Semantics...
Qed.

(* ignore below line! *)

(* 
Example ori_1 : NOT TRUE
  forall (i j : identifier),
    [|i:=j|] =>> [|i:=j; j:=i|].
Proof with ellipsis.
  intros. intros ts H.
  apply CSemantics_equiv'.
  apply CSemantics_equiv' in H.
  eapply sm_closure_implication'...
  clear H ts. intros ts H.
  invert H. invert H3.
  destruct H as [? [? []]]. subst.
  invert H. invert H0. invert H2.
  subst. simpl. *)

  (* if this isn't true, try with number for k *)
(* Example ori_1 :  NOT TRUE!
  forall (i j k: identifier),
    i <> k
      ->
    [|i:=k|] =>> [|i:=j; i:=k|].
Proof with ellipsis.
  intros. intros ts ?.
  apply CSemantics_equiv'.
  apply CSemantics_equiv' in H0.
  eapply sm_closure_implication'...
  clear H0 ts. intros ts ?.
  invert H0.
  destruct H4 as [ts1 [ts2 [? []]]]. subst.
  invert H0. invert H1. invert H3.
  rename s into s1. 
  replace ([(s0, s0)] ++ [(s1, i |-> s0 k; s1)])
    with ([(s0, s0)] ++ [(s1, i |-> s0 k; s1)] ++ [])...
  apply sm_mumbly with (i |-> s0 j; s1)...
  simpl.
  replace [(s0, s0); (s1, i |-> s0 j; s1); (i |-> s0 j; s1, i |-> s0 k; s1)]
    with ([(s0, s0)] ++ [(s1, i |-> s0 j; s1)] ++[(i |-> s0 j; s1, i |-> s0 k; s1)])...
  apply sm_mumbly with (i |-> s0 j; s1)...
  simpl.
  apply sm_self.
  apply SmSeq'.
  exists [(s0, s0); (s1, i |-> s0 j; s1)].
  repeat esplit...
  - apply SmAsgn' with (n:=s0 j) (s:=s1).
    exists [(s0, s0)]. repeat esplit...
    apply SmId'...
  - apply SmAsgn' 
      with (n:=s0 k) (s:=(i |-> s0 j; s1)).
    exists [(i |-> s0 j; s1, i |-> s0 j; s1)]. 
    repeat esplit...
    + replace (s0 k)
        with ((s0) k)
      apply SmId'...



    
  exists [(s0, s0); (s0, s0)], 
    [(s0, s0); (s1, i |-> s0 k; s1)].
  repeat split...
  - apply SmAsgn' with (n:=s0 j) (s:=s0).
    exists [(s0, s0)]. repeat esplit...
    + apply SmId'...
    + replace (i |-> s0 j; s0) with s0...
      symmetry.
      apply update_s_same.
  - apply SmAsgn' with (n:=s0 k) (s:=s1).
    exists [(s0, s0)]. repeat esplit...
    apply SmId'...
Admitted. *)

Example ori_3 : 
  forall (i: identifier) (n m : nat),
    [|i:=m|] =>> [|i:=n; i:=m|].
Proof with ellipsis.
  intros. intros ts ?.
  apply CSemantics_equiv'.
  apply CSemantics_equiv' in H.
  eapply sm_closure_implication'...
  clear H ts. intros ts ?.
  invert H.
  destruct H3 as [ts1 [ts2 [? []]]]. subst.
  invert H. invert H0. invert H2.
  rename s into s1. rename n0 into m. 
  replace ([(s0, s0)] ++ [(s1, i |-> m; s1)])
    with ([(s0, s0)] ++ [(s1, i |-> m; s1)] ++ [])...
  apply sm_mumbly with (i |-> n; s1)...
  simpl.
  replace [(s0, s0); (s1, i |-> n; s1); (i |-> n; s1, i |-> m; s1)]
    with ([(s0, s0)] ++ [(s1, i |-> n; s1)] ++[(i |-> n; s1, i |-> m; s1)])...
  apply sm_mumbly with (i |-> n; s1)...
  simpl.
  apply sm_self.
  apply SmSeq'.
  exists [(s0, s0); (s1, i |-> n; s1)].
  repeat esplit...
  - apply SmAsgn' with (n:=n) (s:=s1).
    exists [(s0, s0)]. repeat esplit...
    eapply SmNum'...
  - apply SmAsgn' 
      with (n:=m) (s:=(i |-> n; s1)).
    exists [(i |-> n; s1, i |-> n; s1)]. 
    repeat esplit...
    + eapply SmNum'...
    + replace (i |-> m; i |-> n; s1)
        with (i |-> m; s1)...
      apply update_s_shadow.
Qed.