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

Fixpoint is_state (is : identifiers) s :=
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

Lemma bottleneck_await :
  forall cl b cr2 s0 sw,
    <{cl || (await b then skip end ; cr2)}> / s0 -->* <{skip}> / sw ->
    exists cl' s1,
      cl / s0 -->* cl' / s1
        /\
      <{cl' || (await b then skip end ; cr2)}> / s1 --> <{cl' || (skip ; cr2)}> / s1
        /\
      <{cl' || (skip ; cr2)}> / s1 -->* <{skip}> / sw.
Proof with eauto.
  intros.
  remember (<{await b then skip end}>) as cr1.
  remember (<{cl || cr1; cr2}>, s0) as cf0 eqn:E0.
  remember (<{skip}>, sw) as cfw eqn:Ew.
  generalize dependent s0. 
  generalize dependent cl. 
  generalize dependent cr2.
  induction H; intros; simpl in *; subst.
  - clean_inversion E0.
  - clean_inversion H.
    + assert ((<{ skip }>, sw) = (<{ skip }>, sw)) by auto.
      apply IHmulti with cr2 c1' s' in H...
      destruct H. destruct H. destruct H. destruct H1.
      exists x, x0...
    + clean_inversion H5.
      clean_inversion H1.
      exists cl, s0. split... split...
      clean_inversion H7.
      clean_inversion H.
Qed.

Lemma multi_step_par1 :
  forall c1 c2 c1' s s',
    c1 / s -->* c1' / s'
      ->
    <{c1 || c2}> / s -->* <{c1' || c2}> / s'.
Proof with eauto.
  intros.
  remember (c1, s) as cf eqn:E.
  remember (c1', s') as cf' eqn:E'.
  replace c1 with (fst cf) in * by (rewrite E; auto).
  replace s with (snd cf) in * by (rewrite E; auto).
  replace c1' with (fst cf') in * by (rewrite E'; auto).
  replace s' with (snd cf') in * by (rewrite E'; auto).
  clear E E' c1 c1' s s'.
  induction H...
  eapply multi_step...
  eapply CS_Par1.
  clean_inversion H.
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
  - admit.
Admitted.

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

