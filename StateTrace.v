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
From WS  Require Import Basics.
From WS  Require Import AwaitDepth.
From WS  Require Import Contexts.
From WS  Require Import PartialCorrectness.

Inductive ST : com -> states -> Prop :=
  | ST_Term :  forall c s s',
    c / s -->* <{skip}> / s' 
      ->
    ST c [s; s']
  | ST_Step : forall c c' s s' ss,
    c / s -->* c' / s'
      ->
    ST c' (s' :: ss)
      ->
    ST c (s :: s' :: ss).
#[global] Hint Constructors ST : core.

Definition STpreorder c d := ST c |= ST d.
Notation "c '[st' d" := (STpreorder c d) 
  (at level 50).
Notation "c '~st' d" := (c [st d /\ d [st c)
  (at level 50).
#[global] Hint Transparent STpreorder : core.

Definition STorder c d :=
  forall cxt, plug cxt c [st plug cxt d.
Notation "c '<st' d" := (STorder c d) 
  (at level 50).
Notation "c '=st' d" := (c <st d /\ d <st c)
  (at level 50).
Notation "c '/st' d" := (~(c =st d))
  (at level 50).
#[global] Hint Transparent STorder : core.

(* auxiliary definitions *)

Fixpoint is_state (is : identifiers) (s : state) :=
  match is with
  | nil     => <{true}>
  | i :: is => <{i = (s i) && (is_state is s)}>
  end.

Fixpoint do_st (is : identifiers) (ss : states) :=
  match ss with
  | nil       => <{skip}>
  | s :: ss => <{
                  await (is_state is s) then 
                    skip 
                  end; 
                  do_st is ss
              }>
  end.

(* claims *)

Lemma ST_imlies_PC :
  forall c d, c [st d -> c [pc d.
Proof with ellipsis.
  unfold "[st", "[pc". 
  intros. intros [s0 sw]. intro.
  assert (ST d [s0; sw])...
  invert H1...
Qed. 

Lemma is_state_self :
  forall is s,
    is_state is s / s -->b* <{true}>.
Proof with ellipsis.
  intros. induction is as [ |i]...
  simpl.
  remember (is_state is s) as c. clear Heqc.
  eapply multi_step 
    with <{(s i) = (s i) && c}>...
  eapply multi_step 
    with <{true && c}>...
  remember (s i) as n. clear Heqn.
  replace <{true}> with (
    if (n =? n)%nat then 
      <{true}> 
    else 
      <{false}>
  )...
  rewrite Nat.eqb_refl...
Qed.

Lemma is_state_is :
  forall s s',
    is_state dom s / s' -->b* <{true}>
      ->
    s' = s.
Proof with ellipsis.
  intros.
  apply states_equal_by_dom. intros j Hj.
  induction dom as [ |i is]...
  invert H. invert H0. invert H4...
  invert H3. invert H1. invert H.
  invert H4...
  destruct (s' i =? s i)%nat eqn:E.
  - apply Nat.eqb_eq in E.
    invert H0. invert H...
  - solve_by_inverts 4.
Qed.

Lemma PC_from_ST :
  forall c s0 sw ss,
    ST c (s0 :: ss ++ [sw])
      <->
    PC <{c||(do_st dom (ss ++ [sw]))}> (s0, sw).
Proof with ellipsis.
  intros. split; intros.
  - generalize dependent s0.
    generalize dependent c.
    clean_induction ss.
    + simpl in *.
      invert H...
      apply multi_trans with (
        <{skip||(do_st dom [sw])}>, 
        sw
      )...
      * apply multi_step_par1...
      * apply multi_trans with (
          <{skip||skip; skip}>, 
          sw
        )...
        eapply multi_step...
        apply CS_Par2. simpl.
        apply CS_SeqStep.
        apply CS_AwaitTrue...
        apply is_state_self.
    + rename a into s1. unfold PC.
      simpl in H. invert H.
      { destruct ss... }
      apply multi_trans with (
        <{c'||(do_st dom (ss ++ [sw]))}>, 
        s1
      )...
      apply multi_trans with (
        <{c'||(do_st dom (s1 :: ss ++ [sw]))}>, 
        s1
      ).
      * apply multi_step_par1...
      * apply multi_trans with (
          <{c'||skip; (do_st dom (ss ++ [sw]))}>, 
          s1
        )...
        eapply multi_step...
        apply CS_Par2.
        simpl. apply CS_SeqStep.
        clear. apply CS_AwaitTrue...
        apply is_state_self.
  - simpl in H.
    generalize dependent s0.
    generalize dependent c.
    clean_induction ss; simpl in *.
    + apply bottleneck_await in H.
      destruct H as [c' [s1 [s2 [H []]]]].
      apply ST_Term.
      invert H0.
      apply is_state_is in H4. subst.
      invert H7...
      eapply multi_trans... 
      clear H c s0.
      rename c' into c. rename s2 into s.
      apply multi_step_par_skip...
      apply par_bottleneck...
    + rename a into s1.
      apply bottleneck_await in H.
      destruct H as [c' [s1' [s2 [H []]]]].
      invert H0.
      apply is_state_is in H4. subst.
      invert H7...
Qed.

Theorem PC_equiv_ST: 
  forall c d, c <pc d <-> c <st d.
Proof with ellipsis.
  unfold "<pc", "<st". split; intros.
  - unfold "[st", "[pc". 
    intros. intro ss. intros.

    assert (len ss >= 2).
    { invert H0... }
    apply list_head_tail in H1.
    destruct H1 as [s0 [sw [ss']]].
    subst. rename ss' into ss.

    specialize H 
      with (CXTPar1 cxt (do_st dom (ss ++ [sw]))).
    simpl in H.
    remember (plug cxt c) as c'.
    remember (plug cxt d) as d'.
    clear Heqc' c Heqd' d cxt.
    rename c' into c.
    rename d' into d.
        
    assert (
      PC <{c||(do_st dom (ss ++ [sw]))}> (s0, sw)
    ) by (apply PC_from_ST; ellipsis).
    clean_apply_in H H1.
    apply PC_from_ST with (dom:=dom)...
  - specialize H with cxt.
    apply ST_imlies_PC in H...
Qed.

