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
From WS  Require Import StepsTo.

Reserved Notation " t '/' s ',' n '-->' t' '/' s' ',' n' "
  (at level 40, s at level 39, t' at level 39).
Inductive fstep : relation (com * state * nat) :=
  | FS_AsgnStep : forall n s i a1 a1',
    a1 / s -->a a1' 
      ->
    <{ i := a1 }> / s, n --> <{ i := a1' }> / s, n
  | FS_Asgn : forall n s i (m : nat),
    <{ i := m }> / s, n --> <{ skip }> / (i |-> m ; s), n
  | FS_SeqStep : forall n n' s c1 c1' s' c2,
    c1 / s, n --> c1' / s', n'
      ->
    <{ c1 ; c2 }> / s, n --> <{ c1' ; c2 }> / s', n'
  | FS_SeqFinish : forall n s c2,
    <{ skip ; c2 }> / s, n --> c2 / s, n
  | FS_IfStep : forall n s b1 b1' c1 c2,
    b1 / s -->b b1' 
      ->
    <{ if b1 then c1 else c2 end }> / s, n
        --> <{ if b1' then c1 else c2 end }> / s, n
  | FS_IfTrue : forall n s c1 c2,
    <{ if true then c1 else c2 end }> / s, n 
        --> c1 / s, n
  | FS_IfFalse : forall n s c1 c2,
    <{ if false then c1 else c2 end }> / s, n
        --> c2 / s, n
  | FS_While : forall n s b1 c1,
    <{ while b1 do c1 end }> / s, S n
      --> <{ if b1 then c1; while b1 do c1 end else skip end }> / s, n
  | FS_Par1 : forall n n' s c1 c1' c2 s',
    c1 / s, n --> c1' / s', n'
      ->
    <{ c1 || c2 }> / s, n --> <{ c1' || c2 }> / s', n'
  | FS_Par2 : forall n n' s c1 c2 c2' s',
    c2 / s, n --> c2' / s', n' 
      ->
    <{ c1 || c2 }> / s, n --> <{ c1 || c2' }> / s', n'
  | FS_ParDone : forall n s,
    <{ skip || skip }> / s, n --> <{ skip }> / s, n
  | FS_AwaitTrue : forall n n' s s' b1 c1,
    b1 / s -->b* BTrue 
      ->
    multi fstep (c1, s, n) (<{skip}>, s', n') 
      ->
    <{ await b1 then c1 end }> / s, n --> <{ skip }> / s', n'
  | FS_AwaitFalse : forall n s b1 c1,
    b1 / s -->b* <{false}> 
      ->
    <{ await b1 then c1 end }> / s, n 
        --> <{ await b1 then c1 end }> / s, n
  where " t '/' s ',' n '-->' t' '/' s' ',' n' " 
    := (fstep (t, s, n) (t', s', n')).
#[global] Hint Constructors fstep : core.

Notation " t '/' s ',' n '-->*' t' '/' s' ',' n' " :=
  (multi fstep  (t, s, n) (t', s', n'))
    (at level 40, s at level 39, t' at level 39).
    
Inductive fTT (n : nat) : com -> transitions -> Prop :=
  | fTT_Term : 
      forall c0 s0 s1,
        c0 / s0, n -->* <{skip}> / s1, 0
          ->
        fTT n c0 [(s0, s1)]
  | fTT_Step :
      forall c0 c1 s0 s1 n1 ps, 
        c0 / s0, n -->* c1 / s1, n1
          ->
        fTT n1 c1 ps
          ->
        fTT n c0 ((s0, s1) :: ps).
#[global] Hint Constructors fTT : core.

(* lemmas *)

Lemma fstep_implies_cstep_aux1 :
  forall c0 cw s0 sw n0 nw,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    (
      forall c0' cw' s0' sw' n0' nw',
        c0' / s0', n0' -->* cw' / sw', nw'
          ->
        await_depth c0' < await_depth c0
          ->
        c0' / s0' -->* cw' / sw'
    )
      ->
    c0 / s0 -->* cw / sw.
Proof with ellipsis.
  intros.
  remember (c0, s0, n0) as cf0 eqn:E0.
  remember (cw, sw, nw) as cfw eqn:Ew.
  generalize dependent n0.
  generalize dependent s0.
  generalize dependent c0.
  induction H; intros; subst;
    try clean_inversion E0.
  destruct y as [[c' s'] n'].
  apply multi_step with (c', s').
  - clear IHmulti H0.
    remember (c0, s0, n0) as cf0 eqn:E0.
    remember (c', s', n') as cf' eqn:E'.
    generalize dependent n'.
    generalize dependent n0.
    generalize dependent s'.
    generalize dependent s0.
    generalize dependent c'.
    generalize dependent c0.
    induction H; intros; subst;
      clean_inversion E';
      clean_inversion E0...
    + apply CS_SeqStep. eapply IHfstep...
      intros. eapply H1...
    + apply CS_Par1. eapply IHfstep...
      intros. eapply H1...
    + apply CS_Par2. eapply IHfstep...
      intros. eapply H1...
  - eapply IHmulti...
    intros. 
    eapply H1...
    assert (await_depth c' <= await_depth c0)...
    clear IHmulti H1 H0 H2 H3.
    remember (c0, s0, n0) as cf0 eqn:E0.
    remember (c', s', n') as cf' eqn:E'.
    generalize dependent n'.
    generalize dependent n0.
    generalize dependent s'.
    generalize dependent s0.
    generalize dependent c'.
    generalize dependent c0.
    induction H; intros; subst;
      clean_inversion E';
      clean_inversion E0...
    + assert (await_depth c1' 
        <= await_depth c1)...
    + assert (await_depth c1' 
        <= await_depth c1)...
    + assert (await_depth c2' 
        <= await_depth c2)...
Qed.

Lemma fstep_implies_cstep :
  forall c0 cw s0 sw n0 nw,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    c0 / s0 -->* cw / sw.
Proof with ellipsis.
  intros.
  remember (await_depth c0) as M.
  assert (HM: await_depth c0 <= M)... clear HeqM.
  generalize dependent nw.
  generalize dependent n0.
  generalize dependent sw.
  generalize dependent s0.
  generalize dependent cw.
  generalize dependent c0.
  induction M; intros; subst.
  - eapply fstep_implies_cstep_aux1...
  - eapply fstep_implies_cstep_aux1...
    intros. eapply IHM...
Qed.

Lemma fstep_add_equaly_aux1 :
  forall c0 cw s0 sw n0 nw d,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    (
      forall c0' cw' s0' sw' n0' nw',
        c0' / s0', n0' -->* cw' / sw', nw'
          ->
        await_depth c0' < await_depth c0
          ->
        c0' / s0', (n0' + d) -->* cw' / sw', (nw' + d)
    )
      ->
    c0 / s0 , (n0 + d) -->* cw / sw , (nw + d).
Proof with ellipsis.
  intros.
  remember (c0, s0, n0) as cf0 eqn:E0.
  remember (cw, sw, nw) as cfw eqn:Ew.
  generalize dependent n0.
  generalize dependent s0.
  generalize dependent c0.
  induction H; intros; subst;
    try clean_inversion E0.
  destruct y as [[c' s'] n'].
  apply multi_step with (c', s', n' + d).
  - clear IHmulti H0 cw sw nw.
    remember (c0, s0, n0) as cf0 eqn:E0.
    remember (c', s', n') as cf' eqn:E'.
    generalize dependent n'.
    generalize dependent n0.
    generalize dependent s'.
    generalize dependent s0.
    generalize dependent c'.
    generalize dependent c0.
    induction H; intros; subst;
      clean_inversion E';
      clean_inversion E0...
    + apply FS_SeqStep. apply IHfstep...
      intros. apply H1...
    + apply FS_Par1. apply IHfstep...
      intros. apply H1...
    + apply FS_Par2. apply IHfstep...
      intros. apply H1...
  - apply IHmulti...
    intros. apply H1...
    assert (await_depth c' <= await_depth c0)...
    apply await_depth_monotone with s0 s'.
    eapply fstep_implies_cstep...
Qed.

Lemma fstep_add_equaly :
  forall c0 cw s0 sw n0 nw d,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    c0 / s0, (n0 + d) -->* cw / sw, (nw + d).
Proof with ellipsis.
  intros.
  remember (await_depth c0) as M.
  assert (HM: await_depth c0 <= M)... clear HeqM.
  generalize dependent nw.
  generalize dependent n0.
  generalize dependent sw.
  generalize dependent s0.
  generalize dependent cw.
  generalize dependent c0.
  induction M; intros; subst.
  - apply fstep_add_equaly_aux1...
  - apply fstep_add_equaly_aux1...
    intros. apply IHM...
Qed.

Corollary f_await_depth_monotone :
  forall c1 c2 s1 s2 n1 n2,
    c1 / s1, n1 -->* c2 / s2, n2
      ->
    await_depth c2 <= await_depth c1.
Proof with ellipsis.
  intros.
  eapply await_depth_monotone.
  eapply fstep_implies_cstep...
Qed.

Lemma cstep_implies_fstep_aux1 :
  forall c0 cw s0 sw,
    c0 / s0 -->* cw / sw
      ->
    (
      forall c0' cw' s0' sw',
        c0' / s0' -->* cw' / sw'
          ->
        await_depth c0' < await_depth c0
          ->
        exists n0' nw', 
          c0' / s0', n0' -->* cw' / sw', nw'
    )
      ->
    exists n0 nw, 
      c0 / s0, n0 -->* cw / sw, nw.
Proof with ellipsis.
  intros.
  remember (c0, s0) as cf0 eqn:E0.
  remember (cw, sw) as cfw eqn:Ew.
  generalize dependent s0.
  generalize dependent c0.
  induction H; intros; subst;
    try clean_inversion E0.
  destruct y as [c' s'].
  assert ((cw, sw) = (cw, sw))...
  apply IHmulti with c' s' in H2;
    [|shelve|auto]. clear IHmulti.
  destruct H2 as [n' [nw]].
  clear H0.
  assert (exists n0 n0', 
    c0 / s0, n0 --> c' / s', n0'
  ).
  - clear H2 cw sw n' nw.
    remember (c0, s0) as cf0 eqn:E0.
    remember (c', s') as cf' eqn:E'.
    generalize dependent s'.
    generalize dependent s0.
    generalize dependent c'.
    generalize dependent c0.
    induction H; intros; subst;
      clean_inversion E';
      clean_inversion E0;
      rename s'0 into s'.
    + assert (exists n0 n0', 
       c1 / s0, n0 --> c1' / s', n0'
      ).
      {
        eapply IHcstep with c1 c1' s0 s'...
        intros. apply H1...
      }
      destruct H0 as [n0 [n0']].
      exists n0, n0'...
    + assert (exists n0 n0', 
        c1 / s0, n0 --> c1' / s', n0'
      ).
      {
        eapply IHcstep with c1 c1' s0 s'...
        intros. apply H1...
      }
      destruct H0 as [n0 [n0']].
      exists n0, n0'...
    + assert (exists n0 n0', 
        c2 / s0, n0 --> c2' / s', n0'
      ).
      {
        eapply IHcstep with c2 c2' s0 s'...
        intros. apply H1...
      }
      destruct H0 as [n0 [n0']].
      exists n0, n0'...
    + assert (exists n0 n0', 
        c1 / s0, n0 -->* <{skip}> / s', n0'
      ). { apply H1 in H0... }
      destruct H2 as [n0 [n0']].
      exists n0, n0'.
      apply FS_AwaitTrue...
  - destruct H0 as [n0 [n0']].
    exists (n0 + n'), (n0' + nw).
    apply multi_trans with (c', s', n0' + n').
    + apply fstep_add_equaly...
    + replace (n0' + n') with (n' + n0')...
      replace (n0' + nw) with (nw + n0')...
      apply fstep_add_equaly...
Unshelve.
  remember 0 as Z. apply Z.
  intros. apply H1... 
    assert (await_depth c' <= await_depth c0)...
    eapply await_depth_monotone...
  apply O.
  apply O.
  apply O.
  apply O.
  apply O.
  apply O.
  apply O.
  apply O.
  apply O.
Qed.

Lemma cstep_implies_fstep :
  forall c0 cw s0 sw,
    c0 / s0 -->* cw / sw
      ->
    exists n0 nw, 
      c0 / s0, n0 -->* cw / sw, nw.
Proof with ellipsis.
  intros.
  remember (await_depth c0) as M.
  assert (HM: await_depth c0 <= M)... clear HeqM.
  generalize dependent sw.
  generalize dependent s0.
  generalize dependent cw.
  generalize dependent c0.
  induction M; intros; subst.
  - apply cstep_implies_fstep_aux1...
  - apply cstep_implies_fstep_aux1...
    intros. apply IHM...
Unshelve.
  remember 0 as Z. apply Z.
  remember 0 as Z. apply Z.
Qed.

Lemma fstep_n_monotone_aux :
  forall c0 cw s0 sw n0 nw,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    (
      forall c0' cw' s0' sw' n0' nw',
        c0' / s0', n0' -->* cw' / sw', nw'
          ->
        await_depth c0' < await_depth c0
          ->
        n0' >= nw'
    )
      ->
    n0 >= nw.
Proof with ellipsis.
  intros.
  remember (c0, s0, n0) as cf0 eqn:E0.
  remember (cw, sw, nw) as cfw eqn:Ew.
  generalize dependent n0.
  generalize dependent s0.
  generalize dependent c0.
  induction H; intros; subst;
    try clean_inversion E0.
  destruct y as [[c' s'] n'].
  assert (n0 >= n').
  - clear IHmulti H0 cw sw nw.
    remember (c0, s0, n0) as cf0 eqn:E0.
    remember (c', s', n') as cf' eqn:E'.
    generalize dependent n'.
    generalize dependent n0.
    generalize dependent s'.
    generalize dependent s0.
    generalize dependent c'.
    generalize dependent c0.
    induction H; intros; subst;
      clean_inversion E';
      clean_inversion E0.
    + apply IHfstep with c1 c1' s0 s'0; auto.
      intros. eapply H1...
    + apply IHfstep with c1 c1' s0 s'0; auto.
      intros. eapply H1...
    + apply IHfstep with c2 c2' s0 s'0; auto.
      intros. eapply H1...
  - assert (n' >= nw); [|lia].
    eapply IHmulti with c' s'; auto.
    intros. eapply H1...
    assert (await_depth c' <= await_depth c0)...
    eapply f_await_depth_monotone...
Qed.

Lemma fstep_n_monotone :
  forall c0 cw s0 sw n0 nw,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    n0 >= nw.
Proof with ellipsis.
  intros.
  remember (await_depth c0) as M.
  assert (HM: await_depth c0 <= M)... clear HeqM.
  generalize dependent nw.
  generalize dependent n0.
  generalize dependent sw.
  generalize dependent s0.
  generalize dependent cw.
  generalize dependent c0.
  induction M; intros; subst.
  - eapply fstep_n_monotone_aux...
  - eapply fstep_n_monotone_aux...
    intros. eapply IHM... lia.
Qed.

Lemma fstep_sub_equaly_aux1 :
  forall c0 cw s0 sw n0 nw d,
    c0 / s0, (n0 + d) -->* cw / sw, (nw + d)
      ->
    (
      forall c0' cw' s0' sw' n0' nw',
        c0' / s0', (n0' + d) -->* cw' / sw', (nw' + d)
          ->
        await_depth c0' < await_depth c0
          ->
        c0' / s0', n0' -->* cw' / sw', nw'
    )
      ->
    c0 / s0, n0 -->* cw / sw, nw.
Proof with ellipsis.
  intros.
  remember (c0, s0, n0 + d) as cf0 eqn:E0.
  remember (cw, sw, nw + d) as cfw eqn:Ew.
  generalize dependent n0.
  generalize dependent s0.
  generalize dependent c0.
  induction H; intros; subst.
  {
    clean_inversion E0.
    assert (nw = n0)...
  }
  destruct y as [[c' s'] n'].
  assert (exists n'', n' = n'' + d).
  {
    clear H1 IHmulti H.
    apply fstep_n_monotone in H0.
    induction n'...
    clean_inversion H0.
    apply IHn' in H1.
    destruct H1 as [n''].
    exists (S n'')...
  }
  destruct H2 as [n'']. subst.
  apply multi_step with (c', s', n'').
  - clear IHmulti H0 cw sw nw.
    remember (c0, s0, n0 + d) as cf0 eqn:E0.
    remember (c', s', n'' + d) as cf' eqn:E'.
    generalize dependent n''.
    generalize dependent n0.
    generalize dependent s'.
    generalize dependent s0.
    generalize dependent c'.
    generalize dependent c0.
    induction H; intros; subst;
      clean_inversion E';
      clean_inversion E0;
      try assert (n'' = n0) by lia...
    + apply FS_SeqStep. apply IHfstep...
      intros. apply H1...
    + assert (n0 = S n'')...
    + apply FS_Par1. apply IHfstep...
      intros. apply H1...
    + apply FS_Par2. apply IHfstep...
      intros. apply H1...
  - apply IHmulti...
    intros. apply H1...
    assert (await_depth c' <= await_depth c0)...
    eapply f_await_depth_monotone...
Qed.

Lemma fstep_sub_equaly :
  forall c0 cw s0 sw n0 nw d,
    c0 / s0, (n0 + d) -->* cw / sw, (nw + d)
      ->
    c0 / s0, n0 -->* cw / sw, nw.
Proof with ellipsis.
  intros.
  remember (await_depth c0) as M.
  assert (HM: await_depth c0 <= M)... clear HeqM.
  generalize dependent nw.
  generalize dependent n0.
  generalize dependent sw.
  generalize dependent s0.
  generalize dependent cw.
  generalize dependent c0.
  induction M; intros; subst.
  - eapply fstep_sub_equaly_aux1...
  - eapply fstep_sub_equaly_aux1...
    intros. apply IHM...
Qed.

Corollary cstep_implies_fstep_0 :
  forall c0 cw s0 sw,
    c0 / s0 -->* cw / sw
      ->
    exists n,
      c0 / s0, n -->* cw / sw, 0.
Proof with ellipsis.
  intros. apply cstep_implies_fstep in H.
  destruct H as [n0 [nw]].
  assert (n0 >= nw). 
  { eapply fstep_n_monotone... }
  assert (exists n, n0 = n + nw).
  { 
    clear H.
    induction n0...
    clean_inversion H0.
    - exists 0...
    - apply IHn0 in H1. destruct H1 as [n].
      exists (S n)...
  }
  destruct H1 as [n]. subst.
  exists n.
  apply fstep_sub_equaly with nw...
Qed.

Lemma f_while_equiv_if_while :
  forall b c n ts,
    fTT (S n) <{while b do c end}> ts
      <->
    fTT n <{if b then c; while b do c end else skip end}> ts.
Proof with ellipsis.
  intros; split; intros.
  - induction ts... solve_by_inverts 3.
  - induction ts...
Qed.

Lemma fTT_while_positive :
  forall n c b ts,
  fTT n <{while b do c end}> ts
    ->
  n > 0.
Proof with ellipsis.
  intros. destruct n... exfalso.
  induction ts... solve_by_inverts 3.
Qed.

Lemma f_if_steps_to :
  forall b c1 c2 c s0 s1 n0 n1,
    <{if b then c1 else c2 end}> / s0, n0 -->* c / s1, n1
      ->
    (
      exists b',
        b / s0 -->b* b'
          /\
        c = <{if b' then c1 else c2 end}>
          /\
        s1 = s0
          /\
        n1 = n0
    )
      \/
    (
      b / s0 -->b* <{true}>
        /\
      c1 / s0, n0 -->* c / s1, n1
    )
      \/
    (
      b / s0 -->b* <{false}>
        /\
      c2 / s0, n0 -->* c / s1, n1
    ).
Proof with ellipsis.
  intros.
  remember (<{ if b then c1 else c2 end }>, s0, n0) 
    as cf0 eqn:E0.
  remember (c, s1, n1) as cf1 eqn:E1.
  generalize dependent b.
  induction H; intros; subst.
  - clean_inversion E0.
    left. exists b...
  - clean_inversion H.
    assert ((c, s1, n1) = (c, s1, n1))...
    apply IHmulti with b1' in H...
    destruct H; destruct H; destruct H...
Qed.

Lemma f_seq_steps_to :
  forall c1 c2 c s0 s1 n0 n1,
    <{c1; c2}> / s0, n0 -->* c / s1, n1
      ->
    (
      (
        exists c1',
          c1 / s0, n0 -->* c1' / s1, n1
            /\
          c = <{c1'; c2}>
      )
        \/
      (
        exists s' n',
          c1 / s0, n0 -->* <{skip}> / s', n'
            /\
          c2 / s', n' -->* c / s1, n1
      )
    ).
Proof with ellipsis.
  intros.
  remember (<{c1; c2}>, s0, n0) as cf0 eqn:E0.
  remember (c, s1, n1) as cf1 eqn:E1.
  generalize dependent n1.
  generalize dependent n0.
  generalize dependent s1.
  generalize dependent s0.
  generalize dependent c.
  generalize dependent c2.
  generalize dependent c1.
  induction H; intros; subst; try clean_inversion E1.
  destruct y as [[c' s'] n'].
  clean_inversion H.
  specialize IHmulti with c1' c2 c s' s1 n' n1.
  assert ((<{ c1'; c2 }>, s', n') 
      = (<{ c1'; c2 }>, s', n'))...
  apply IHmulti in H... clear IHmulti.
  destruct H; destruct H; destruct H; subst...
  right. destruct H...
Qed.


