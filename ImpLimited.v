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
From WS  Require Import TransitionTrace.

Reserved Notation " t '/' s ',' n '-->' t' '/' s' ',' n' "
  (at level 40, s at level 39, t' at level 39).
Inductive lstep : relation (com * state * nat) :=
  | LS_AsgnStep : forall n s i a1 a1',
    a1 / s -->a a1' 
      ->
    <{ i := a1 }> / s, n --> <{ i := a1' }> / s, n
  | LS_Asgn : forall n s i (m : nat),
    <{ i := m }> / s, n --> <{ skip }> / (i |-> m ; s), n
  | LS_SeqStep : forall n n' s c1 c1' s' c2,
    c1 / s, n --> c1' / s', n'
      ->
    <{ c1 ; c2 }> / s, n --> <{ c1' ; c2 }> / s', n'
  | LS_SeqFinish : forall n s c2,
    <{ skip ; c2 }> / s, n --> c2 / s, n
  | LS_Ilstep : forall n s b1 b1' c1 c2,
    b1 / s -->b b1' 
      ->
    <{ if b1 then c1 else c2 end }> / s, n
        --> <{ if b1' then c1 else c2 end }> / s, n
  | LS_IfTrue : forall n s c1 c2,
    <{ if true then c1 else c2 end }> / s, n 
        --> c1 / s, n
  | LS_IfFalse : forall n s c1 c2,
    <{ if false then c1 else c2 end }> / s, n
        --> c2 / s, n
  | LS_While : forall n s b1 c1,
    <{ while b1 do c1 end }> / s, S n
      --> <{ if b1 then c1; while b1 do c1 end else skip end }> / s, n
  | LS_Par1 : forall n n' s c1 c1' c2 s',
    c1 / s, n --> c1' / s', n'
      ->
    <{ c1 || c2 }> / s, n --> <{ c1' || c2 }> / s', n'
  | LS_Par2 : forall n n' s c1 c2 c2' s',
    c2 / s, n --> c2' / s', n' 
      ->
    <{ c1 || c2 }> / s, n --> <{ c1 || c2' }> / s', n'
  | LS_ParDone : forall n s,
    <{ skip || skip }> / s, n --> <{ skip }> / s, n
  | LS_AwaitTrue : forall n n' s s' b1 c1,
    b1 / s -->b* BTrue 
      ->
    multi lstep (c1, s, n) (<{skip}>, s', n') 
      ->
    <{ await b1 then c1 end }> / s, n --> <{ skip }> / s', n'
  | LS_AwaitFalse : forall n s b1 c1,
    b1 / s -->b* <{false}> 
      ->
    <{ await b1 then c1 end }> / s, n 
        --> <{ await b1 then c1 end }> / s, n
  where " t '/' s ',' n '-->' t' '/' s' ',' n' " 
    := (lstep (t, s, n) (t', s', n')).
#[global] Hint Constructors lstep : core.

Notation " t '/' s ',' n '-->*' t' '/' s' ',' n' " :=
  (multi lstep  (t, s, n) (t', s', n'))
    (at level 40, s at level 39, t' at level 39).
    
Inductive lTT (n : nat) : com -> transitions -> Prop :=
  | lTT_Term : 
      forall c0 s0 s1,
        c0 / s0, n -->* <{skip}> / s1, 0
          ->
        lTT n c0 [(s0, s1)]
  | lTT_Step :
      forall c0 c1 s0 s1 n1 ps, 
        c0 / s0, n -->* c1 / s1, n1
          ->
        lTT n1 c1 ps
          ->
        lTT n c0 ((s0, s1) :: ps).
#[global] Hint Constructors lTT : core.

(* lemmas - lstep *)

Lemma l_await_depth_monotone :
  forall c0 cw s0 sw n0 nw,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    await_depth cw <= await_depth c0.
Proof with ellipsis.
  intros.
  remember (c0, s0, n0) as cf0 eqn:E0.
  remember (cw, sw, nw) as cfw eqn:Ew.
  generalize dependent nw.
  generalize dependent n0.
  generalize dependent sw.
  generalize dependent s0.
  generalize dependent cw.
  generalize dependent c0.
  induction H; intros; subst;
    try clean_inversion Ew...
  destruct y as [[c1 s1] n1].
  assert (await_depth cw <= await_depth c1)...
  assert (await_depth c1 <= await_depth c0)...
  clear IHmulti H0 H1 cw sw.
  remember (c0, s0, n0) as cf0 eqn:E0.
  remember (c1, s1, n1) as cf1 eqn:E1.
  generalize dependent n1.
  generalize dependent n0.
  generalize dependent s1.
  generalize dependent s0.
  generalize dependent c1.
  generalize dependent c0.
  induction H; intros; subst;
    clean_inversion E0;
    clean_inversion E1...
  - assert (await_depth c1' 
        <= await_depth c1)...
  - assert (await_depth c1' 
        <= await_depth c1)...
  - assert (await_depth c2' 
        <= await_depth c2)...
Qed.

Lemma lstep_n_monotone :
  forall c0 cw s0 sw n0 nw,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    n0 >= nw.
Proof with ellipsis.
  intros c0.
  remember ( 
    fun c0 =>
      forall cw s0 sw n0 nw,
        c0 / s0, n0 -->* cw / sw, nw
          ->
        n0 >= nw
  ) as P.
  assert (P c0)...
  apply await_depth_induction. 
  subst. clear. intro c0. intros.
  remember (c0, s0, n0) as cf0.
  remember (cw, sw, nw) as cfw.
  generalize dependent n0.
  generalize dependent s0.
  generalize dependent c0.
  clean_induction H0...
  destruct y as [[c1 s1] n1].
  assert (n0 >= n1).
  - clear IHmulti H0 cw sw nw.
    remember (c0, s0, n0) as cf0 eqn:E0.
    remember (c1, s1, n1) as cf1 eqn:E1.
    generalize dependent n1.
    generalize dependent n0.
    generalize dependent s1.
    generalize dependent s0.
    generalize dependent c1.
    generalize dependent c0.
    clean_induction H;
      invert E0; invert E1; ellipsis;
      eapply IHlstep; try reflexivity;
      intros; eapply H1; simpl; 
      ellipsis; lia.
  - assert (n1 >= nw)...
    eapply IHmulti; try reflexivity.
    intros. eapply H1...
    assert (await_depth c1 <= await_depth c0)...
    eapply l_await_depth_monotone...
Qed.

Lemma lstep_add_equaly :
  forall c0 cw s0 sw n0 nw d,
    c0 / s0, n0 -->* cw / sw, nw
      <->
    c0 / s0, (n0 + d) -->* cw / sw, (nw + d).
Proof with ellipsis.
  intro c0.
  remember ( 
    fun c0 =>
      forall cw s0 sw n0 nw d,
        c0 / s0, n0 -->* cw / sw, nw
          <->
        c0 / s0, (n0 + d) -->* cw / sw, (nw + d)
  ) as P.
  assert (P c0); [ |subst]...
  apply await_depth_induction. 
  subst. clear. intro c0. split; intros.
  - remember (c0, s0, n0) as cf0.
    remember (cw, sw, nw) as cfw.
    generalize dependent n0.
    generalize dependent s0.
    generalize dependent c0.
    clean_induction H0...
    destruct y as [[c1 s1] n1].
    apply multi_step with (c1, s1, n1 + d)...
    + clear IHmulti H0 cw sw nw.
      remember (c0, s0, n0) as cf0 eqn:E0.
      remember (c1, s1, n1) as cf1 eqn:E1.
      generalize dependent n1.
      generalize dependent n0.
      generalize dependent s1.
      generalize dependent s0.
      generalize dependent c1.
      generalize dependent c0.
      clean_induction H;
        invert E0; invert E1...
      * apply LS_SeqStep. apply IHlstep...
        intros. apply H1...
      * apply LS_Par1. apply IHlstep...
        intros. apply H1...
      * apply LS_Par2. apply IHlstep...
        intros. apply H1...
      * apply LS_AwaitTrue... apply H1...
    + apply IHmulti...
      intros. apply H1.
      assert (await_depth c1 <= await_depth c0)...
      eapply l_await_depth_monotone...
  - remember (c0, s0, n0 + d) as cf0 eqn:E0.
    remember (cw, sw, nw + d) as cfw eqn:E1.
    generalize dependent n0.
    generalize dependent s0.
    generalize dependent c0.
    clean_induction H0.
    { invert E0. assert (nw = n0)... }
    destruct y as [[c1 s1] n1'].
    assert (nw + d <= n1').
    { eapply lstep_n_monotone... }
    assert (n1' = (n1' - d) + d)...
    remember (n1' - d) as n1. 
    clear Heqn1 H2. subst.
    apply multi_step with (c1, s1, n1)...
    + clear IHmulti H0 cw sw nw.
      remember (c0, s0, n0 + d) as cf0 eqn:E0.
      remember (c1, s1, n1 + d) as cf1 eqn:E1.
      generalize dependent n1.
      generalize dependent n0.
      generalize dependent s1.
      generalize dependent s0.
      generalize dependent c1.
      generalize dependent c0.
      clean_induction H;
        invert E0; invert E1;
        try solve [assert (n0 = n1); ellipsis]...
      * apply LS_SeqStep. apply IHlstep...
        intros. apply H1...
      * assert (n0 = S n1)...
      * apply LS_Par1. apply IHlstep...
        intros. apply H1...
      * apply LS_Par2. apply IHlstep...
        intros. apply H1...
      * apply LS_AwaitTrue... eapply H1...
    + apply IHmulti...
      intros. apply H1.
      assert (await_depth c1 <= await_depth c0)...
      eapply l_await_depth_monotone...
Qed.

Lemma lstep_equiv_cstep :
  forall c0 cw s0 sw,
    c0 / s0 -->* cw / sw
      <->
    exists n,
      c0 / s0, n -->* cw / sw, 0.
Proof with ellipsis.
  intro c0.
  remember ( 
    fun c0 =>
      forall cw s0 sw,
        c0 / s0 -->* cw / sw
          <->
        exists n,
          c0 / s0, n -->* cw / sw, 0
  ) as P.
  assert (P c0); [ |subst]...
  apply await_depth_induction. 
  subst. clear. intro c0. split; intros.
  - remember (c0, s0) as cf0.
    remember (cw, sw) as cfw.
    generalize dependent s0.
    generalize dependent c0.
    clean_induction H0...
    destruct y as [c1 s1].
    assert ((cw, sw) = (cw, sw))...
    specialize IHmulti with c1 s1.
    clean_apply_in IHmulti H2.
    + destruct H2 as [n].
      assert (
        exists n',
         c0 / s0, n' --> c1 / s1, n
      ); [ |destruct H3 as [n']]...
      clear H2 H0 cw sw.
      remember (c0, s0) as cf0 eqn:E0.
      remember (c1, s1) as cf1 eqn:E1.
      generalize dependent s1.
      generalize dependent s0.
      generalize dependent c1.
      generalize dependent c0.
      clean_induction H;
        invert E0; invert E1.
      * assert (
          exists n',
            c1 / s0, n' --> c1' / s1, n
        ); [ |destruct H0 as [n']]...
        eapply IHcstep; try reflexivity. 
        intros. apply H1... 
      * assert (
          exists n',
            c1 / s0, n' --> c1' / s1, n
        ); [ |destruct H0 as [n']]...
        eapply IHcstep; try reflexivity. 
        intros. apply H1...
      * assert (
          exists n',
            c2 / s0, n' --> c2' / s1, n
        ); [ |destruct H0 as [n']]...
        eapply IHcstep; try reflexivity. 
        intros. apply H1...
      * assert (
          exists n',
            c1 / s0, n' -->* <{skip}> / s1, 0
        ).
        { apply H1... }
        destruct H2 as [n']. exists (n' + n).
        apply LS_AwaitTrue...
        eapply lstep_add_equaly 
          with (d:=n) in H2...
    + intros. apply H1.
      assert (await_depth c1 <= await_depth c0)...
      eapply await_depth_monotone...
  - destruct H0 as [n0].
    remember 0 as nw. rewrite Heqnw in H.
    clear Heqnw.
    remember (c0, s0, n0) as cf0.
    remember (cw, sw, nw) as cfw.
    generalize dependent n0.
    generalize dependent s0.
    generalize dependent c0.
    clean_induction H0...
    destruct y as [[c1 s1] n1].
    apply multi_step with (c1, s1).
    + clear IHmulti H0 cw sw nw.
      remember (c0, s0, n0) as cf0 eqn:E0.
      remember (c1, s1, n1) as cf1 eqn:E1.
      generalize dependent n1.
      generalize dependent n0.
      generalize dependent s1.
      generalize dependent s0.
      generalize dependent c1.
      generalize dependent c0.
      clean_induction H;
        invert E0; invert E1...
      * apply CS_SeqStep. eapply IHlstep...
        intros. apply H1...
      * apply CS_Par1. eapply IHlstep...
        intros. apply H1...
      * apply CS_Par2. eapply IHlstep...
        intros. apply H1...
      * apply CS_AwaitTrue... apply H1...
        exists (n0 - n1).
        apply lstep_add_equaly with (d:=n1).
        assert (n0 - n1 + n1 = n0); 
            [ |rewrite H2]...
        assert (n1 <= n0)...
        eapply lstep_n_monotone...
    + eapply IHmulti...
      intros. apply H1.
      assert (await_depth c1 <= await_depth c0)...
      eapply l_await_depth_monotone...
Qed.

Lemma lstep_equiv_lstep0 :
  forall c0 cw s0 sw n0 nw,
    c0 / s0, n0 -->* cw / sw, nw
      ->
    exists n,
      c0 / s0, n -->* cw / sw, 0.
Proof with ellipsis.
  intros. exists (n0 - nw).
  apply lstep_add_equaly with (d:=nw).
  replace (n0 - nw + nw) with n0...
  assert (nw <= n0)...
  eapply lstep_n_monotone...
Qed.

(* lemmas - lstep steps to *)

Lemma l_if_steps_to :
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

Lemma l_seq_steps_to :
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

(* lemmas - lTT *)

Lemma lTT_equiv_TT :
  forall c ps,
    TT c ps <-> exists n, lTT n c ps.
Proof with ellipsis.
  intros; split; intros.
  - induction H.
    + apply lstep_equiv_cstep in H.
      destruct H as [n]...
    + apply lstep_equiv_cstep in H.
      destruct H as [n0]. 
      destruct IHTT as [n1].
      exists (n0 + n1).
      apply lTT_Step with c1 n1...
      eapply lstep_add_equaly 
        with (d:=n1) in H...
  - destruct H as [n].
    induction H.
    + apply TT_Term. apply lstep_equiv_cstep...
    + eapply TT_Step... apply lstep_equiv_cstep...
      apply lstep_equiv_lstep0 in H...
Qed.

Lemma lTT_while_positive :
  forall n c b ts,
  lTT n <{while b do c end}> ts
    ->
  n > 0.
Proof with ellipsis.
  intros. destruct n... exfalso.
  induction ts... solve_by_inverts 3.
Qed.

Lemma l_while_equiv_if_while :
  forall b c n ts,
    lTT (S n) <{while b do c end}> ts
      <->
    lTT n <{
      if b then 
        c; while b do c end 
      else 
        skip 
      end
    }> ts.
Proof with ellipsis.
  intros; split; intros.
  - induction ts... solve_by_inverts 3.
  - induction ts...
Qed.

Theorem lTT_stuttery_mumbly: 
  forall c n, 
    stuttery_mumbly (lTT n c).
Proof with ellipsis.
  intros c n ts H. induction H...
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
      * eapply lTT_Term. eapply multi_trans...
      * eapply lTT_Step. eapply multi_trans...
        auto.
Qed.

Theorem lTT_if_substitutive :
  forall c1 c2 b ts n,
    lTT n <{if b then c1 else c2 end}> ts
      <->
    (
      LP{bTT true b; lTT n c1} ts
        \/
      LP{bTT false b; lTT n c2} ts
    ).
Proof with ellipsis.
  intros; split; intros.
  - remember <{ if b then c1 else c2 end }> as c.
    generalize dependent b.
    induction H; intros; subst.
    + apply l_if_steps_to in H.
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
    + apply l_if_steps_to in H.
      destruct H as [ |[]].
      * destruct H as [b' [H []]]. subst.
        assert (<{ if b' then c1 else c2 end }> 
          = <{ if b' then c1 else c2 end }>)...
        clean_apply_in IHlTT H1. destruct H1.
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
      * destruct H. clear IHlTT. left.
        rewrite cons_to_app.
        apply sm_mumbly with s0... simpl.
        apply sm_self. exists [(s0, s0)]...
      * destruct H. clear IHlTT. right.
        rewrite cons_to_app.
        apply sm_mumbly with s0... simpl.
        apply sm_self. exists [(s0, s0)]...
  - destruct H.
    + apply lTT_stuttery_mumbly.
      eapply sm_closure_implication...
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      induction H; simpl...
      * apply lTT_Step with c1 n...
        simpl in H.
        remember <{true}> as T.
        clean_induction H...
      * eapply lTT_Step; [ |apply IHbTT]...
        induction H...
    + apply lTT_stuttery_mumbly.
      eapply sm_closure_implication...
      clear H ts. 
      intros ts [ts1 [ts2 [H []]]]. subst.
      induction H; simpl...
      * apply lTT_Step with c2 n...
        simpl in H.
        remember <{false}> as T.
        clean_induction H...
      * eapply lTT_Step; [ |apply IHbTT]...
        induction H...
Qed.

Theorem lTT_seq_substitutive :
  forall c1 c2 n ts,
    lTT n <{c1; c2}> ts
      <->
    exists n1 n2,
      n1 + n2 = n
        /\
      LP{lTT n1 c1 ; lTT n2 c2} ts.
Proof with ellipsis.
  intros. split; intros.
  - remember <{ c1; c2 }> as c.
    generalize dependent c2.
    generalize dependent c1.
    induction H; intros; subst.
    + apply l_seq_steps_to in H.
      destruct H; destruct H; destruct H...
      destruct H.
      rename x0 into n2.
      rename x into s'.
      exists (n - n2), n2. repeat split...
      * assert ( n2 <= n)...
        eapply lstep_n_monotone...
      * rewrite cons_to_app.
        apply sm_mumbly with s'. simpl.
        apply sm_self...
        exists [(s0, s')]. repeat esplit...
        replace n2 with (0 + n2) in H...
        assert (n2 <= n).
        { eapply lstep_n_monotone... }
        replace n with ((n - n2) + n2) in H...
        apply lstep_add_equaly in H...
    + rename c1 into c.
      rename c2 into c1.
      rename c3 into c2.
      apply l_seq_steps_to in H.
      destruct H; destruct H; destruct H...
      * rename x into c1'.
        apply IHlTT in H1. 
        clear IHlTT H0 c.
        destruct H1 as [n1' [n2 [H1]]].
        assert (n1 <= n).
        { eapply lstep_n_monotone... }
        exists (n1' + (n - n1)), n2.
        repeat split...
        induction H0;
          try rewrite cons_to_app3_assoc_cons...
        destruct H0 as [l1 [l2 [H3 []]]]. subst.
        apply sm_self.
        exists ((s0, s1) :: l1). repeat esplit...
        apply lTT_Step with c1' n1'...
        replace (n1' + (n - (n1' + n2)))
          with (n - n2)...
        replace n with (n - n2 + n2) in H...
          apply lstep_add_equaly in H...
      * rename x into s'. clear IHlTT.
        rewrite cons_to_app.
        destruct H.
        assert (x0 <= n).
        { eapply lstep_n_monotone... }
        exists (n - x0), x0. repeat split...
        apply sm_mumbly with s'. simpl.
        apply sm_self.
        exists [(s0, s')]. repeat esplit...
        replace x0 with (0 + x0) in H...
        replace n with ((n - x0) + x0) in H...
        apply lstep_add_equaly in H...
  - destruct H as [n1 [n2 []]].
    apply lTT_stuttery_mumbly.
    eapply sm_closure_implication...
    clear H0 ts. 
    intros ts [ts1 [ts2 [H1 []]]]. subst.
    induction H1; simpl...
    + apply lTT_Step with c2 n2...
      remember (c0, s0, n) as cf0.
      remember (<{skip}>, s1, 0) as cf1.
      generalize dependent n.
      generalize dependent s0.
      generalize dependent c0.
      clean_induction H...
      destruct y as [[c' s'] n'].
      apply multi_trans 
        with (<{c'; c2}>, s', n' + n2)...
      rewrite <- lstep_add_equaly...
    + eapply lTT_Step...
      remember (c0, s0, n) as cf0.
      remember (c1, s1, n1) as cf1.
      generalize dependent n.
      generalize dependent s0.
      generalize dependent c0.
      clean_induction H...
      destruct y as [[c' s'] n'].
      apply multi_trans 
        with (<{c'; c2}>, s', n' + n2)...
      rewrite <- lstep_add_equaly...
Qed.
      
Lemma lTT_while_substitutive :
  forall n c b ts,
    lTT n <{while b do c end}> ts
      ->
    (bTT false b) ts
      \/
    exists nw,
      nw < n
        /\
      LP{
        (bTT true b ; TT c) 
        ; 
        lTT nw <{while b do c end}>
      } ts.
Proof with ellipsis.
  intros.
  destruct n. 
  { apply lTT_while_positive in H... }
  apply l_while_equiv_if_while in H.
  remember <{while b do c end}> as cwh. 
  clear Heqcwh.
  apply lTT_if_substitutive in H.
  destruct H.
  - right. 
    induction H;
      try destruct IHstutter_mumble_closure 
        as [nw []];
      try exists nw...
    destruct H as [l1 [l2 [H []]]]. subst.
    apply lTT_seq_substitutive in H0.
    destruct H0 as [n1 [n2 []]].
    exists n2. split...
    assert (
      forall p l2 l3,
        l1 ++ l2 ++ [p] ++ l3 
          =
        (l1 ++ l2) ++ [p] ++ l3 
    ).
    { intros. apply app_assoc. }
    induction H1;
      try rewrite H2;
      try rewrite app_assoc 
        in IHstutter_mumble_closure...
    clear H2.
    destruct H1 as [l2 [l3 [H1 []]]]. subst.
    apply sm_self. rewrite app_assoc.
    exists (l1 ++ l2). repeat esplit...
    apply sm_self. exists l1. repeat esplit...
    apply lTT_equiv_TT...
  - left.
    apply bTT_stuttery_mumbly.
    induction H...
    apply sm_self.
    destruct H as [l1 [l2 [H []]]]. subst.
    induction H; simpl in *...
    eapply bTT_Step...
    remember <{skip}> as c'.
    clean_induction H0;
      solve_by_inverts 2.
Qed.