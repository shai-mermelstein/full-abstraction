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

Reserved Notation "[| a -> n |]"
  (at level 0, a custom com at level 99).
Inductive ASemantics : aexp -> nat -> pairsP state :=
  | SmNum : forall s (n : nat),
    LP({[(s, s)]}^) |= [|n -> n|] 
  | SmId : forall s (i : identifier),
    LP({[(s, s)]}^) |= [|i -> s i|] 
  | SmPlus : forall a1 a2 n1 n2,
    LP([|a1 -> n1|] ; [|a2 -> n2|]) 
      |= [|a1 + a2 -> n1 + n2|]
  | SmMinus : forall a1 a2 n1 n2,
    LP([|a1 -> n1|] ; [|a2 -> n2|]) 
      |= [|a1 - a2 -> n1 - n2|]
  | SmMult : forall a1 a2 n1 n2,
    LP([|a1 -> n1|] ; [|a2 -> n2|]) 
      |= [|a1 * a2 -> n1 * n2|]
  where "[| a -> n |]" := (ASemantics a n).
#[global] Hint Constructors ASemantics : core.

Reserved Notation "[| b |]t"
  (at level 0, b custom com at level 99).
Reserved Notation "[| b |]f"
  (at level 0, b custom com at level 99).
Reserved Notation "[| b ->b v |]"
  (at level 0, b custom com at level 99).
Inductive BSemantics : bexp -> bool -> pairsP state :=
  | SmTrue : forall s,
    LP({[(s, s)]}^) |= [|true|]t
  | SmFalse : forall s,
    LP({[(s, s)]}^) |= [|false|]f
  | SmNot : forall b v,
    [|b ->b v|] |= [|~b ->b negb v|]
  | SmEq : forall a1 a2 n1 n2,
    LP([|a1 -> n1|] ; [|a2 -> n2|]) 
      |= [|a1 = a2 ->b (n1 =? n2)%nat|]
  | SmLe : forall a1 a2 n1 n2,
    LP([|a1 -> n1|] ; [|a2 -> n2|]) 
      |= [|a1 <= a2 ->b (n1 <=? n2)%nat|]
  | SmAndFalse : forall b1 b2,
    [|b1|]f |= [|b1 && b2|]f
  | SmAndTrue : forall b1 b2 v,
    LP([|b1|]t ; [|b2 ->b v|]) 
      |= [|b1 && b2 ->b v|]
  where "[| b |]t" := (BSemantics b true)
  and   "[| b |]f" := (BSemantics b false)
  and   "[| b ->b v |]" := (BSemantics b v).
#[global] Hint Constructors BSemantics : core.

Reserved Notation "[| c |]"
  (at level 0, c custom com at level 99).
Inductive CSemantics : com -> pairsP state :=
  | SmSkip : forall s,
    LP({[(s, s)]}^) |= [|skip|]
  | SmAsgn : forall i a n s,
    LP([|a -> n|] ; {[(s, (i |-> n; s))]}) 
      |= [|i := a|]
  | SmSeq : forall c1 c2,
    LP([|c1|]; [|c2|]) |= [|c1; c2|]
  | SmIfTrue : forall b c1 c2,
    LP([|b|]t ; [|c1|]) 
      |= [|if b then c1 else c2 end|]
  | SmIfFalse : forall b c1 c2,
    LP([|b|]f ; [|c2|])
      |= [|if b then c1 else c2 end|]
  | SmWhile : forall b c,
    LP(([|b|]t ; [|c|])* ; [|b|]f) (* star does not include ^, unlike Brookes*)
      |= [|while b do c end|]
  | SmPar : forall c1 c2,
    LP([|c1|] || [|c2|]) |= [|c1 || c2|]
  | SmAwait : forall b c s s',
    [|b|]t [(s, s)]
      ->
    [|c|] [(s, s')]
      ->
    LP({[(s, s')]}^) |= [|await b then c end|]
  where "[| c |]" := (CSemantics c).
#[global] Hint Constructors CSemantics : core.

(* delayed ^ *)

Reserved Notation "[| a -> n |]'"
  (at level 0, a custom com at level 99).
Inductive ASemantics' : aexp -> nat -> pairsP state :=
  | SmNum' : forall s (n : nat),
    LP({[(s, s)]}) |= [|n -> n|]'
  | SmId' : forall s (i : identifier),
    LP({[(s, s)]}) |= [| i -> s i|]' 
  | SmPlus' : forall a1 a2 n1 n2,
    LP([|a1 -> n1|]' + [|a2 -> n2|]') 
      |= [|a1 + a2 -> n1 + n2|]'
  | SmMinus' : forall a1 a2 n1 n2,
    LP([|a1 -> n1|]' + [|a2 -> n2|]') 
      |= [|a1 - a2 -> n1 - n2|]'
  | SmMult' : forall a1 a2 n1 n2,
    LP([|a1 -> n1|]' + [|a2 -> n2|]') 
      |= [|a1 * a2 -> n1 * n2|]'
  where "[| a -> n |]'" := (ASemantics' a n).
#[global] Hint Constructors ASemantics' : core.

Reserved Notation "[| b |]'t"
  (at level 0, b custom com at level 99).
Reserved Notation "[| b |]'f"
  (at level 0, b custom com at level 99).
Reserved Notation "[| b ->b v |]'"
  (at level 0, b custom com at level 99).
Inductive BSemantics' : bexp -> bool -> pairsP state :=
  | SmFalse' : forall s,
    LP({[(s, s)]}) |= [|true|]'t
  | SmTrue' : forall s,
    LP({[(s, s)]}) |= [|false|]'f
  | SmNot' : forall b v,
    [|b ->b v|]' |= [|~b ->b negb v|]'
  | SmEq' : forall a1 a2 n1 n2,
    LP([|a1 -> n1|]' + [|a2 -> n2|]')
      |= [|a1 = a2 ->b (n1 =? n2)%nat|]'
  | SmLe' : forall a1 a2 n1 n2,
    LP([|a1 -> n1|]' + [|a2 -> n2|]') 
      |= [|a1 <= a2 ->b (n1 <=? n2)%nat|]'
  | SmAndFalse' : forall b1 b2,
    [|b1|]'f |= [|b1 && b2|]'f
  | SmAndTrue' : forall b1 b2 v,
    LP([|b1|]'t + [|b2 ->b v|]') 
      |= [|b1 && b2 ->b v|]'
  where "[| b |]'t" := (BSemantics' b true)
  and   "[| b |]'f" := (BSemantics' b false)
  and   "[| b ->b v |]'" := (BSemantics' b v).
#[global] Hint Constructors BSemantics' : core.

Reserved Notation "[| c |]'"
  (at level 0, c custom com at level 99).
Inductive CSemantics' : com -> pairsP state :=
  | SmSkip' : forall s,
    LP({[(s, s)]}) |= [|skip|]'
  | SmAsgn' : forall i a n s,
    LP([| a -> n |]' + {[(s, (i |-> n; s))]}) 
      |= [|i := a|]'
  | SmSeq' : forall c1 c2,
    LP([|c1|]' + [|c2|]') |= [|c1; c2|]'
  | SmIfTrue' : forall b c1 c2,
    LP([|b|]'t + [|c1|]') 
      |= [|if b then c1 else c2 end|]'
  | SmIfFalse' : forall b c1 c2,
    LP([|b|]'f + [|c2|]')
      |= [|if b then c1 else c2 end|]'
  | SmWhile' : forall b c,
    LP(([|b|]'t + [|c|]')* + [|b|]'f) 
      |= [|while b do c end|]'
  | SmPar' : forall c1 c2,
    LP([|c1|]' # [|c2|]') |= [|c1 || c2|]'
  | SmAwait' : forall b c s s',
    [|b|]t [(s, s)]
      ->
    [|c|] [(s, s')]
      ->
    LP({[(s, s')]}) |= [|await b then c end|]'
  where "[| c |]'" := (CSemantics' c).
#[global] Hint Constructors CSemantics' : core.

(* equiv' *)

Theorem ASemantics_stuttery_mumbly :
  forall a n, stuttery_mumbly [|a -> n|].
Proof with ellipsis.
  intros a n ts H. destruct a.
  - assert (n0 = n); subst.
    { clean_induction H... }
    assert (exists s, LP({[(s, s)]}^) ts)...
    { 
      clean_induction H...
      - invert H.
      - destruct IHstutter_mumble_closure as [s].
        exists s...
      - destruct IHstutter_mumble_closure as [s].
        exists s...
    }
    destruct H0 as [s]. eapply SmNum...
  - assert (exists s, LP({[(s, s)]}^) ts /\ n = s i)...
    { 
      clean_induction H...
      - invert H.
      - destruct IHstutter_mumble_closure as [s []].
        exists s... 
      - destruct IHstutter_mumble_closure as [s []].
        exists s...
    }
    destruct H0 as [s []]. subst. eapply SmId...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      eapply SmPlus...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      eapply SmMinus...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      eapply SmMult...
Qed.

Theorem ASemantics_equiv' :
  forall a n,
    [|a -> n|] ~ LP([|a -> n|]'^).
Proof with ellipsis.
  intros a n ts; split.
  - generalize dependent ts.
    generalize dependent n.
    clean_induction a; invert H;
      eapply sm_closure_inner_implication; ellipsis;
      eapply sm_closure_inner_implication1; ellipsis;
      clear H4 ts; intro ts; intros;
      destruct H as [ts1 [ts2 [H []]]];
      clean_apply_in IHa1 H;
      clean_apply_in IHa2 H0;
      apply sm_closure_app...
  - intros.
    apply ASemantics_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    generalize dependent n.
    clean_induction a; intros ts H; invert H.
    + eapply SmNum...
    + eapply SmId...
    + eapply SmPlus...
      destruct H4 as [l1 [l2 [H []]]].
      subst. apply sm_self.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H0...
    + eapply SmMinus...
      destruct H4 as [l1 [l2 [H []]]].
      subst. apply sm_self.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H0...
    + eapply SmMult...
      destruct H4 as [l1 [l2 [H []]]].
      subst. apply sm_self.
      clean_apply_in IHa1 H.
      clean_apply_in IHa2 H0...
Qed.

Theorem BSemantics_stuttery_mumbly :
  forall b v, stuttery_mumbly [|b ->b v|].
Proof with ellipsis.
  intro b. clean_induction b; intros ts H.
  - assert (v = true); subst.
    { clean_induction H... }
    assert (exists s, LP({[(s, s)]}^) ts)...
    { 
      clean_induction H...
      - invert H.
      - destruct IHstutter_mumble_closure as [s].
        exists s...
      - destruct IHstutter_mumble_closure as [s].
        exists s...
    }
    destruct H0 as [s]. eapply SmTrue...
  - assert (v = false); subst.
    { clean_induction H... }
    assert (exists s, LP({[(s, s)]}^) ts)...
    { 
      clean_induction H...
      - invert H.
      - destruct IHstutter_mumble_closure as [s].
        exists s...
      - destruct IHstutter_mumble_closure as [s].
        exists s...
    }
    destruct H0 as [s]. eapply SmFalse...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      eapply SmEq...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      eapply SmLe...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      apply SmNot; ellipsis;
      apply IHb...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      try solve [eapply SmAndTrue; ellipsis];
      eapply SmAndFalse; ellipsis;
      apply IHb1...
Qed.

Theorem BSemantics_equiv' :
  forall b v,
    [|b ->b v|] ~ LP([|b ->b v|]'^).
Proof with ellipsis.
  intros b v ts; split.
  - generalize dependent ts.
    generalize dependent v.
    clean_induction b; invert H;
      try solve [
        eapply sm_closure_inner_implication; ellipsis;
        eapply sm_closure_inner_implication1; ellipsis;
        clear H4 ts; intro ts; intros;
        destruct H as [ts1 [ts2 [H []]]];
        apply ASemantics_equiv' in H;
        apply ASemantics_equiv' in H0;
        apply sm_closure_app; ellipsis
      ].
      + clean_apply_in IHb1 H4. clear IHb2.
        apply sm_closure_inner_implication
          with ([|b1 |]'f)...
      + eapply sm_closure_inner_implication; ellipsis;
        eapply sm_closure_inner_implication1; ellipsis;
        clear H4 ts; intro ts; intros;
        destruct H as [ts1 [ts2 [H []]]];
        clean_apply_in IHb1 H;
        clean_apply_in IHb2 H0;
        apply sm_closure_app...
  - intros.
    apply BSemantics_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    generalize dependent v.
    clean_induction b; intros ts H; invert H.
    + eapply SmTrue...
    + eapply SmFalse...
    + eapply SmEq...
      destruct H4 as [l1 [l2 [H []]]].
      subst. apply sm_self.
      apply sm_self in H.
      apply ASemantics_equiv' in H.
      apply sm_self in H0.
      apply ASemantics_equiv' in H0...
    + eapply SmLe...
      destruct H4 as [l1 [l2 [H []]]].
      subst. apply sm_self.
      apply sm_self in H.
      apply ASemantics_equiv' in H.
      apply sm_self in H0.
      apply ASemantics_equiv' in H0...
    + apply SmNot. apply IHb...
    + apply SmAndFalse. apply IHb1...
    + apply SmAndTrue.
      destruct H4 as [l1 [l2 [H []]]].
      subst. apply sm_self.
      clean_apply_in IHb1 H.
      clean_apply_in IHb2 H0...
Qed.

Theorem CSemantics_stuttery_mumbly :
  forall c, stuttery_mumbly [|c|].
Proof with ellipsis.
  intros c ts H. destruct c.
  - assert (exists s, LP({[(s, s)]}^) ts)...
    { 
      clean_induction H...
      - invert H.
      - destruct IHstutter_mumble_closure as [s].
        exists s...
      - destruct IHstutter_mumble_closure as [s].
        exists s...
    }
    destruct H0 as [s]. eapply SmSkip...
  - assert (exists s n, 
      LP([| a -> n |] ; {[(s, (i |-> n; s))]}) ts
    ). 
    { 
      clean_induction H...
      - invert H.
      - destruct IHstutter_mumble_closure 
          as [s [n]]...
      - destruct IHstutter_mumble_closure 
          as [s [n]]...
    }
    destruct H0 as [s [n]]. eapply SmAsgn...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      eapply SmSeq...
  - induction H; ellipsis;
      invert IHstutter_mumble_closure;
      try solve [eapply SmIfTrue; ellipsis];
      try solve [eapply SmIfFalse; ellipsis].
  - induction H; ellipsis;
    invert IHstutter_mumble_closure;
    eapply SmWhile...
  - induction H; ellipsis;
    invert IHstutter_mumble_closure;
    eapply SmPar...
  - induction H; ellipsis;
    invert IHstutter_mumble_closure;
    eapply SmAwait...
Qed.

Theorem CSemantics_equiv' :
  forall c,
    [|c|] ~ LP([|c|]'^).
Proof with ellipsis.
  intros c ts; split.
  - generalize dependent ts.
    clean_induction c; invert H.
    + eapply sm_closure_inner_implication...
    + eapply sm_closure_inner_implication
        with LP([|a -> n|]' + {[(s, i |-> n; s)]})...
      eapply sm_closure_inner_implication1...
      clear H3 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      apply ASemantics_equiv' in H.
      apply sm_closure_app...
    + eapply sm_closure_inner_implication...
      eapply sm_closure_inner_implication1...
      clear H3 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      clean_apply_in IHc1 H.
      clean_apply_in IHc2 H0.
      apply sm_closure_app...
    + eapply sm_closure_inner_implication
        with LP([|b|]'t + [|c1|]')...
      eapply sm_closure_inner_implication1...
      clear H4 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      apply BSemantics_equiv' in H.
      clean_apply_in IHc1 H0.
      apply sm_closure_app...
    + eapply sm_closure_inner_implication...
      eapply sm_closure_inner_implication1...
      clear H4 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      apply BSemantics_equiv' in H.
      clean_apply_in IHc2 H0.
      apply sm_closure_app...
    + eapply sm_closure_inner_implication...
      eapply sm_closure_inner_implication1...
      clear H3 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      assert (LP(([|b|]'t ; [|c|]')*) ts1).
      {
        clear H0 H1 ts ts2.
        eapply star_implecation...
        eapply sm_closure_inner_implication1...
        clear H ts1. intros ts H.
        destruct H as [ts1 [ts2 [H []]]].
        clean_apply_in IHc H0.
        apply sm_closure_app.
        apply BSemantics_equiv' in H.
        exists ts1, ts2. split...
      }
      eapply sm_closure_star in H2.
      apply sm_closure_app.
      exists ts1, ts2. repeat split...
      apply BSemantics_equiv'... 
    + eapply sm_closure_inner_implication...
      eapply sm_closure_inner_implication1...
      clear H3 ts; intro ts; intros.
      eapply int_implecation 
        with (P' := LP([|c1|]'^)) (Q' := LP([|c2|]'^))
        in H...
      

    + eapply sm_closure_inner_implication...
  - intros.
    apply CSemantics_stuttery_mumbly.
    eapply sm_closure_inner_implication...
    clear H ts. 
    clean_induction c; intros ts H; invert H.
    + eapply SmSkip...
    + apply SmAsgn with n s.
      destruct H3 as [ts1 [ts2 [H []]]].
      subst. apply sm_self.
      apply sm_self in H.
      apply ASemantics_equiv' in H...
    + destruct H3 as [ts1 [ts2 [H []]]].
      clean_apply_in IHc1 H.
      clean_apply_in IHc2 H0.
      apply SmSeq. apply sm_self...
    + destruct H4 as [ts1 [ts2 [H []]]].
      apply sm_self in H.
      apply BSemantics_equiv' in H...
      clean_apply_in IHc1 H0.
      apply SmIfTrue. apply sm_self...
    + destruct H4 as [ts1 [ts2 [H []]]].
      apply sm_self in H.
      apply BSemantics_equiv' in H...
      clean_apply_in IHc2 H0.
      apply SmIfFalse. apply sm_self...
    + destruct H3 as [ts1 [ts2 [H []]]].
      apply sm_self in H0.
      apply BSemantics_equiv' in H0...
      apply SmWhile. apply sm_self...
      exists ts1, ts2. split...
      clear H0 H1 ts ts2. rename ts1 into ts.
      apply sm_closed_star_implecation.
      apply star_implecation
        with LP([|b|]'t + [|c|]')...
      clear H ts. intros ts H.
      destruct H as [ts1 [ts2 [H []]]].
      apply sm_self in H.
      apply BSemantics_equiv' in H.
      clean_apply_in IHc H0... 
    + destruct H3 as [ts1 [ts2 [H []]]].
      apply SmPar. apply sm_self.
      eapply int_implecation...
    + eapply SmAwait...
Admitted.


(* 
Lemma int_replace1 :
  forall A (a : A) new x1 x2 y z,
    ((x1 ++ [a] ++ x2) ## y) z
      ->
    exists z1 z2,
      z = z1 ++ [a] ++ z2
        /\
      ((x1 ++ new ++ x2) ## y) (z1 ++ new ++ z2).
Proof with ellipsis.
  intros.
  remember (x1 ++ [a] ++ x2) as x.
  generalize dependent x1.
  clean_induction H.
  - destruct x1...
  - destruct x1; simpl in *.
    + invert Heqx.
      exists nil, l. split...
      simpl. clear IHinterwoven.
      induction new...
    + invert Heqx.
      assert (x1 ++ a :: x2 = x1 ++ a :: x2)...
      clean_apply_in IHinterwoven H0.
      destruct H0 as [z1 [z2 []]]. subst.
      exists (a1 :: z1), z2. split...
  - assert (x1 ++ a :: x2 = x1 ++ a :: x2)...
    clean_apply_in IHinterwoven H0.
    destruct H0 as [z1 [z2 []]]. subst.
    exists (a0 :: z1), z2. split...
Unshelve.
  apply nil.
  apply nil.
  apply nil.
  apply nil.
Qed.

Lemma int_replace2 :
  forall A (a : A) new x y1 y2 z,
    (x ## (y1 ++ [a] ++ y2)) z
      ->
    exists z1 z2,
      z = z1 ++ [a] ++ z2
        /\
      (x ## (y1 ++ new ++ y2)) (z1 ++ new ++ z2).
Proof with ellipsis.
  intros.
  remember (y1 ++ [a] ++ y2) as yx.
  generalize dependent y1.
  clean_induction H.
  - destruct y1...
  - assert (y1 ++ a :: y2 = y1 ++ a :: y2)...
    clean_apply_in IHinterwoven H0.
    destruct H0 as [z1 [z2 []]]. subst.
    exists (a0 :: z1), z2. split...
  - destruct y1; simpl in *.
    + invert Heqyx.
      exists nil, l. split...
      simpl. clear IHinterwoven.
      induction new...
    + invert Heqyx.
      assert (y1 ++ a :: y2 = y1 ++ a :: y2)...
      clean_apply_in IHinterwoven H0.
      destruct H0 as [z1 [z2 []]]. subst.
      exists (a1 :: z1), z2. split...
Unshelve.
  apply nil.
  apply nil.
  apply nil.
  apply nil.
Qed.

Theorem ASemantics_equiv' :
  forall a n,
    [|a -> n|] ~ LP([|a -> n|]'^).
Proof with ellipsis.
  intros; split; intros;
    rename a0 into ts;
    generalize dependent n;
    generalize dependent ts;
    clean_induction a...
  - invert H.
    remember LP({[(s, s)]}) as P.
    clean_induction H1.
    apply sm_self. eapply SmNum'...
  - invert H.
    remember LP({[(s, s)]}) as P.
    clean_induction H1.
    apply sm_self. apply SmId'...
  - invert H.
    remember LP([|a1 -> n1|] + [|a2 -> n2|]) as P.
    clean_induction H4.
    invert H. destruct H0 as [y [H []]].
    clean_apply_in IHa1 H.
    clean_apply_in IHa2 H0.
    remember [|a1 -> n1 |]' as P.
    generalize dependent l.
    clean_induction H.
    + remember [|a2 -> n2 |]' as P.
      generalize dependent l.
      clean_induction H0.
      * apply sm_self. apply SmPlus'...
      * clean_apply_in 
          IHstutter_mumble_closure H.
        replace (l ++ l1 ++ [(x, x)] ++ l2)
          with ((l ++ l1) ++ [(x, x)] ++ l2)
          by (rewrite <- app_assoc; ellipsis).
        eapply sm_stuttery...
        rewrite <- app_assoc...
      * clean_apply_in 
          IHstutter_mumble_closure H.
        replace (l ++ l1 ++ [(x, z)] ++ l2)
          with ((l ++ l1) ++ [(x, z)] ++ l2)
          by (rewrite <- app_assoc; ellipsis).
        eapply sm_mumbly with y...
        rewrite <- app_assoc...
    + assert ((l1 ++ l2) ++ y = (l1 ++ l2) ++ y)...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      apply sm_stuttery with (x:=x) in H1.
      rewrite <- app_assoc...
    + assert (
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y 
          = 
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y
      )...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      rewrite <- app_assoc in H1.
      apply sm_mumbly in H1.
      rewrite <- app_assoc...
  - invert H.
    remember LP([|a1 -> n1|] + [|a2 -> n2|]) as P.
    clean_induction H4.
    invert H. destruct H0 as [y [H []]].
    clean_apply_in IHa1 H.
    clean_apply_in IHa2 H0.
    remember [|a1 -> n1 |]' as P.
    generalize dependent l.
    clean_induction H.
    + remember [|a2 -> n2 |]' as P.
      generalize dependent l.
      clean_induction H0.
      * apply sm_self. apply SmMinus'...
      * clean_apply_in 
          IHstutter_mumble_closure H.
        replace (l ++ l1 ++ [(x, x)] ++ l2)
          with ((l ++ l1) ++ [(x, x)] ++ l2)
          by (rewrite <- app_assoc; ellipsis).
        eapply sm_stuttery...
        rewrite <- app_assoc...
      * clean_apply_in 
          IHstutter_mumble_closure H.
        replace (l ++ l1 ++ [(x, z)] ++ l2)
          with ((l ++ l1) ++ [(x, z)] ++ l2)
          by (rewrite <- app_assoc; ellipsis).
        eapply sm_mumbly with y...
        rewrite <- app_assoc...
    + assert ((l1 ++ l2) ++ y = (l1 ++ l2) ++ y)...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      apply sm_stuttery with (x:=x) in H1.
      rewrite <- app_assoc...
    + assert (
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y 
          = 
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y
      )...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      rewrite <- app_assoc in H1.
      apply sm_mumbly in H1.
      rewrite <- app_assoc...
  - invert H.
    remember LP([|a1 -> n1|] + [|a2 -> n2|]) as P.
    clean_induction H4.
    invert H. destruct H0 as [y [H []]].
    clean_apply_in IHa1 H.
    clean_apply_in IHa2 H0.
    remember [|a1 -> n1 |]' as P.
    generalize dependent l.
    clean_induction H.
    + remember [|a2 -> n2 |]' as P.
      generalize dependent l.
      clean_induction H0.
      * apply sm_self. apply SmMult'...
      * clean_apply_in 
          IHstutter_mumble_closure H.
        replace (l ++ l1 ++ [(x, x)] ++ l2)
          with ((l ++ l1) ++ [(x, x)] ++ l2)
          by (rewrite <- app_assoc; ellipsis).
        eapply sm_stuttery...
        rewrite <- app_assoc...
      * clean_apply_in 
          IHstutter_mumble_closure H.
        replace (l ++ l1 ++ [(x, z)] ++ l2)
          with ((l ++ l1) ++ [(x, z)] ++ l2)
          by (rewrite <- app_assoc; ellipsis).
        eapply sm_mumbly with y...
        rewrite <- app_assoc...
    + assert ((l1 ++ l2) ++ y = (l1 ++ l2) ++ y)...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      apply sm_stuttery with (x:=x) in H1.
      rewrite <- app_assoc...
    + assert (
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y 
          = 
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y
      )...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      rewrite <- app_assoc in H1.
      apply sm_mumbly in H1.
      rewrite <- app_assoc...
  - remember [|n -> n0|]' as P.
    clean_induction H...
    + invert H. eapply SmNum...
    + invert IHstutter_mumble_closure.
      eapply SmNum...
    + invert IHstutter_mumble_closure.
      eapply SmNum...
  - remember [|i -> n|]' as P.
    clean_induction H...
    + invert H. eapply SmId...
    + invert IHstutter_mumble_closure.
      eapply SmId...
    + invert IHstutter_mumble_closure.
      eapply SmId...
  - remember [|a1 + a2 -> n|]' as P.
    clean_induction H.
    + invert H. invert H4.
      destruct H as [y [H []]].
      apply sm_self in H.
      clean_apply_in IHa1 H.
      apply sm_self in H0.
      clean_apply_in IHa2 H0.
      apply SmPlus... apply sm_self...
    + invert IHstutter_mumble_closure.
      apply SmPlus...
    + invert IHstutter_mumble_closure.
      apply SmPlus...
  - remember [|a1 + a2 -> n|]' as P.
    clean_induction H.
    + invert H. invert H4.
      destruct H as [y [H []]].
      apply sm_self in H.
      clean_apply_in IHa1 H.
      apply sm_self in H0.
      clean_apply_in IHa2 H0.
      apply SmMinus... apply sm_self...
    + invert IHstutter_mumble_closure.
      apply SmMinus...
    + invert IHstutter_mumble_closure.
      apply SmMinus...
  - remember [|a1 + a2 -> n|]' as P.
    clean_induction H.
    + invert H. invert H4.
      destruct H as [y [H []]].
      apply sm_self in H.
      clean_apply_in IHa1 H.
      apply sm_self in H0.
      clean_apply_in IHa2 H0.
      apply SmMult... apply sm_self...
    + invert IHstutter_mumble_closure.
      apply SmMult...
    + invert IHstutter_mumble_closure.
      apply SmMult...
Qed.

Lemma BSemantics_stuttery_mumbly :
  forall b v,
    stuttery_mumbly [|b ->b v|].
Proof with ellipsis.
  intro. induction b; repeat intro.
  - remember [|true ->b v|] as P.
    clean_induction H;
      invert IHstutter_mumble_closure;
      eapply SmTrue...
  - remember [|false ->b v|] as P.
    clean_induction H;
      invert IHstutter_mumble_closure;
      eapply SmFalse...
  - remember [|a1 = a2 ->b v|] as P.
    clean_induction H;
      invert IHstutter_mumble_closure;
      eapply SmEq...
  - remember [|a1 <= a2 ->b v|] as P.
    clean_induction H;
      invert IHstutter_mumble_closure;
      eapply SmLe...
  - remember [|~ b ->b v|] as P.
    clean_induction H.
    + invert IHstutter_mumble_closure.
      apply sm_self in H1.
      apply sm_stuttery 
        with (x:=x) in H1.
      clean_apply_in IHb H1.
      eapply SmNot...
    + invert IHstutter_mumble_closure.
      apply sm_self in H1.
      apply sm_mumbly in H1.
      clean_apply_in IHb H1.
      eapply SmNot...
  - remember [|b1 && b2 ->b v|] as P.
    clean_induction H.
    + invert IHstutter_mumble_closure.
      * apply sm_self in H4.
        apply sm_stuttery 
          with (x:=x) in H4.
        clean_apply_in IHb1 H4.
        eapply SmAndFalse...
      * apply SmAndTrue.
        apply sm_stuttery...
    + invert IHstutter_mumble_closure.
      * apply sm_self in H4.
        apply sm_mumbly in H4.
        clean_apply_in IHb1 H4.
        eapply SmAndFalse...
      * apply SmAndTrue.
        apply sm_mumbly with y...
Qed.

Theorem BSemantics_equiv' :
  forall b v,
    [|b ->b v|] ~ LP([|b ->b v|]'^).
Proof with ellipsis.
  intros; split; intros;
    rename a into ts;
    generalize dependent ts;
    generalize dependent v;
    clean_induction b...
  - invert H.
    remember LP({[(s, s)]}) as P.
    clean_induction H0.
    apply sm_self. eapply SmFalse'...
  - invert H.
    remember LP({[(s, s)]}) as P.
    clean_induction H0.
    apply sm_self. eapply SmTrue'...
  - invert H.
    remember LP([|a1 -> n1|] + [|a2 -> n2|]) 
      as P.
    clean_induction H4.
    invert H.
    destruct H0 as [y [H []]].
    apply ASemantics_equiv' in H.
    apply ASemantics_equiv' in H0.
    remember LP([|a1 -> n1|]') as P.
    generalize dependent l.
    clean_induction H.
    remember LP([|a2 -> n2|]') as P.
    clean_induction H0.
    + apply sm_self. apply SmEq'...
    + rewrite app_assoc 
        in IHstutter_mumble_closure.
      apply sm_stuttery with (x:=x)
        in IHstutter_mumble_closure.
      rewrite app_assoc...
    + rewrite app_assoc 
        in IHstutter_mumble_closure.
      apply sm_mumbly
        in IHstutter_mumble_closure.
      rewrite app_assoc...
    + assert (
        (l1 ++ l2) ++ y = (l1 ++ l2) ++ y
      )...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      apply sm_stuttery with (x:=x) in H1.
      rewrite <- app_assoc...
    + assert (
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y
          = 
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y
      )...
      clean_apply_in
        IHstutter_mumble_closure H1.
      repeat rewrite <- app_assoc in H1.
      apply sm_mumbly in H1.
      rewrite <- app_assoc...
  - invert H.
    remember LP([|a1 -> n1|] + [|a2 -> n2|]) 
      as P.
    clean_induction H4.
    invert H.
    destruct H0 as [y [H []]].
    apply ASemantics_equiv' in H.
    apply ASemantics_equiv' in H0.
    remember LP([|a1 -> n1|]') as P.
    generalize dependent l.
    clean_induction H.
    remember LP([|a2 -> n2|]') as P.
    clean_induction H0.
    + apply sm_self. apply SmLe'...
    + rewrite app_assoc 
        in IHstutter_mumble_closure.
      apply sm_stuttery with (x:=x)
        in IHstutter_mumble_closure.
      rewrite app_assoc...
    + rewrite app_assoc 
        in IHstutter_mumble_closure.
      apply sm_mumbly
        in IHstutter_mumble_closure.
      rewrite app_assoc...
    + assert (
        (l1 ++ l2) ++ y = (l1 ++ l2) ++ y
      )...
      clean_apply_in
        IHstutter_mumble_closure H1.
      rewrite <- app_assoc in H1.
      apply sm_stuttery with (x:=x) in H1.
      rewrite <- app_assoc...
    + assert (
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y
          = 
        (l1 ++ [(x, y0); (y0, z)] ++ l2) ++ y
      )...
      clean_apply_in
        IHstutter_mumble_closure H1.
      repeat rewrite <- app_assoc in H1.
      apply sm_mumbly in H1.
      rewrite <- app_assoc...
  - invert H.
    clean_apply_in IHb H1.
    remember [|b ->b v0 |]' as P.
    clean_induction H1.
    apply sm_self. apply SmNot'...
  - invert H.
    + clean_apply_in IHb1 H4.
      clear IHb2.
      remember [|b1 |]'f as P.
      clean_induction H4.
      apply sm_self. apply SmAndFalse'...
    + remember LP([|b1 |]t + [|b2 ->b v|]) 
        as P.
      clean_induction H4.
      invert H.
      destruct H0 as [y [H []]].
      clean_apply_in IHb1 H.
      clean_apply_in IHb2 H0.
      remember [|b1|]'t as P.
      generalize dependent l.
      clean_induction H.
      remember [|b2|]'t as P.
      clean_induction H0.
      * apply sm_self. apply SmAndTrue'...
      * rewrite app_assoc.
        apply sm_stuttery.
        rewrite <- app_assoc...
      * rewrite app_assoc.
        apply sm_mumbly with y.
        rewrite <- app_assoc...
      * repeat rewrite <- app_assoc.
        apply sm_stuttery.
        rewrite app_assoc.
        apply IHstutter_mumble_closure...
      * repeat rewrite <- app_assoc.
        apply sm_mumbly with y0.
        apply IHstutter_mumble_closure...
        repeat rewrite app_assoc...
  - remember [|true ->b v |]' as P.
    clean_induction H.
    + invert H. eapply SmTrue...
    + invert IHstutter_mumble_closure.
      eapply SmTrue...
    + invert IHstutter_mumble_closure.
      eapply SmTrue...
  - remember [|false ->b v |]' as P.
    clean_induction H.
    + invert H. eapply SmFalse...
    + invert IHstutter_mumble_closure.
      eapply SmFalse...
    + invert IHstutter_mumble_closure.
      eapply SmFalse...
  - remember [|a1 = a2 ->b v |]' as P.
    clean_induction H.
    + invert H. invert H4.
      destruct H as [y [H []]].
      apply sm_self in H.
      apply ASemantics_equiv' in H.
      apply sm_self in H0.
      apply ASemantics_equiv' in H0.
      eapply SmEq. apply sm_self...
    + invert IHstutter_mumble_closure.
      apply SmEq...
    + invert IHstutter_mumble_closure.
      apply SmEq...
  - remember [|a1 = a2 ->b v |]' as P.
    clean_induction H.
    + invert H. invert H4.
      destruct H as [y [H []]].
      apply sm_self in H.
      apply ASemantics_equiv' in H.
      apply sm_self in H0.
      apply ASemantics_equiv' in H0.
      eapply SmLe. apply sm_self...
    + invert IHstutter_mumble_closure.
      apply SmLe...
    + invert IHstutter_mumble_closure.
      apply SmLe...
  - remember [|~ b ->b v |]' as P.
    clean_induction H.
    + invert H. 
      apply sm_self in H1.
      clean_apply_in IHb H1.
      apply SmNot...
    + invert IHstutter_mumble_closure.
      apply SmNot.
      apply BSemantics_stuttery_mumbly...
    + invert IHstutter_mumble_closure.
      apply SmNot. 
      apply BSemantics_stuttery_mumbly...
  - remember [|b1 && b2 ->b v |]' as P.
    clean_induction H.
    + invert H.
      * apply sm_self in H4.
        clean_apply_in IHb1 H4.
        apply SmAndFalse...
      * invert H4.
        destruct H as [y [H []]].
        apply sm_self in H.
        clean_apply_in IHb1 H.
        apply sm_self in H0.
        clean_apply_in IHb2 H0.
        apply SmAndTrue. apply sm_self...
    + invert IHstutter_mumble_closure.
      * apply SmAndFalse...
        apply BSemantics_stuttery_mumbly...
      * apply SmAndTrue...
    + invert IHstutter_mumble_closure.
      * apply SmAndFalse...
        apply BSemantics_stuttery_mumbly...
      * apply SmAndTrue...
Qed.
        
Theorem CSemantics_equiv' :
  forall c,
    [|c|] ~ LP([|c|]'^).
Proof with ellipsis.
  intros; split; intros;
    rename a into ts;
    generalize dependent ts;
    clean_induction c...
  - invert H.
    remember LP({[(s, s)]}) as P.
    clean_induction H0.
    apply sm_self. eapply SmSkip'...
  - invert H.
    remember LP([|a -> n|] + {[(s, i |-> n; s)]}) 
      as P.
    clean_induction H3.
    invert H. destruct H0 as [y [H []]].
    subst.
    apply ASemantics_equiv' in H.
    remember [|a -> n|]' as P.
    clean_induction H.
    + apply sm_self. eapply SmAsgn'.
      exists l, y. split...
    + repeat rewrite <- app_assoc.
      apply sm_stuttery.
      rewrite app_assoc...
    + repeat rewrite <- app_assoc.
      apply sm_mumbly with y0.
      repeat rewrite <- app_assoc 
        in IHstutter_mumble_closure...
  - invert H.
    remember LP([|c1|] + [|c2|]) as P.
    clean_induction H3.
    invert H. destruct H0 as [y [H []]].
    clean_apply_in IHc1 H.
    clean_apply_in IHc2 H0.
    remember [|c1 |]' as P.
    generalize dependent l.
    clean_induction H.
    remember [|c2 |]' as P.
    clean_induction H0.
    + apply sm_self. apply SmSeq'.
      exists l, l0...
    + rewrite app_assoc in *.
      apply sm_stuttery...
    + rewrite app_assoc in *.
      apply sm_mumbly with y...
    + repeat rewrite <- app_assoc in *.
      apply sm_stuttery...
    + repeat rewrite <- app_assoc in *.
      apply sm_mumbly with y0...
  - invert H.
    + remember LP([|b|]t + [|c2|]) as P.
      clean_induction H4.
      invert H. destruct H0 as [y [H []]].
      apply BSemantics_equiv' in H.
      clean_apply_in IHc1 H0.
      remember [|b|]'t as P.
      generalize dependent l.
      clean_induction H.
      remember [|c1|]' as P.
      clean_induction H0.
      * apply sm_self. apply SmIfTrue'.
        exists l, l0...
      * rewrite app_assoc in *.
        apply sm_stuttery...
      * rewrite app_assoc in *.
        apply sm_mumbly with y...
      * repeat rewrite <- app_assoc in *.
        apply sm_stuttery...
      * repeat rewrite <- app_assoc in *.
        apply sm_mumbly with y0...
    + remember LP([|b|]t + [|c2|]) as P.
      clean_induction H4.
      invert H. destruct H0 as [y [H []]].
      apply BSemantics_equiv' in H.
      clean_apply_in IHc2 H0.
      remember [|b|]'t as P.
      generalize dependent l.
      clean_induction H.
      remember [|c2|]' as P.
      clean_induction H0.
      * apply sm_self. apply SmIfFalse'.
        exists l, l0...
      * rewrite app_assoc in *.
        apply sm_stuttery...
      * rewrite app_assoc in *.
        apply sm_mumbly with y...
      * repeat rewrite <- app_assoc in *.
        apply sm_stuttery...
      * repeat rewrite <- app_assoc in *.
        apply sm_mumbly with y0...
  - invert H.
    admit.
    (* remember LP(([|b|]t; [|c|]) * + [|b|]f)
      as P.
    clean_induction H3.
    invert H. destruct H0 as [y [H []]].
    apply BSemantics_equiv' in H0.
    remember LP([|b|]t ; [|c|]) as P.
    generalize dependent l.
    clean_induction H.
    + remember LP([|b|]'f) as P.
      clean_induction H0; simpl in *.
      * apply sm_self. apply SmWhile'.
        exists nil, l. split...
      * replace (l1 ++ (x, x) :: l2)
          with (l1 ++ [(x, x)] ++ l2)...
      * replace (l1 ++ (x, z) :: l2)
          with (l1 ++ [(x, z)] ++ l2)...
        replace (l1 ++ (x, y) :: (y, z) :: l2)
          with (l1 ++ [(x, y); (y, z)] ++ l2)
          in IHstutter_mumble_closure...
    + assert (l2 ++ y = l2 ++ y)...
      clean_apply_in IHstarP H2.
      remember LP([|b|]t + [|c|]) as P.
      clean_induction H.
      * invert H. destruct H3 as [z [H []]].
        subst.
        remember [|while b do c end |]' as P.
        remember (l2 ++ y) as l.
        generalize dependent y.
        generalize dependent l2.
        clean_induction H2. *)
  - invert H.
    remember LP([|c1|] # [|c2|]) as P.
    clean_induction H3.
    invert H. destruct H0 as [y [H []]].
    clean_apply_in IHc1 H.
    clean_apply_in IHc2 H0.
    remember [|c1|]' as P.
    generalize dependent l.
    clean_induction H.
    remember [|c2|]' as P.
    generalize dependent l0.
    clean_induction H0.
    + apply sm_self. apply SmPar'...
    + apply int_replace2 
        with (new:=[]) in H1.
      destruct H1 as [z1 [z2 []]].
      subst.
      apply sm_stuttery...
    + apply int_replace2 
        with (new:=[(x, y); (y, z)]) in H1.
      destruct H1 as [z1 [z2 []]].
      subst.
      eapply sm_mumbly...
    + apply int_replace1
        with (new:=[]) in H1.
      destruct H1 as [z1 [z2 []]].
      subst.
      apply sm_stuttery...
    + apply int_replace1
        with (new:=[(x, y0); (y0, z)]) in H1.
      destruct H1 as [z1 [z2 []]].
      subst.
      eapply sm_mumbly...
  - invert H.
    remember LP({[(s, s')]}) as P.
    clean_induction H5.
    apply sm_self. eapply SmAwait'...
  - remember [|skip|]' as P.
    clean_induction H.
    + invert H. eapply SmSkip...
    + invert IHstutter_mumble_closure.
      eapply SmSkip...
    + invert IHstutter_mumble_closure.
      eapply SmSkip...
  - remember [|i := a|]' as P.
    clean_induction H.
    + invert H. invert H3.
      destruct H as [y [H []]].
      eapply SmAsgn. 
      apply sm_self.
      exists x, y. split...
      apply sm_self in H.
      apply ASemantics_equiv' in H...
    + invert IHstutter_mumble_closure.
      eapply SmAsgn...
    + invert IHstutter_mumble_closure.
      eapply SmAsgn...
Admitted.
        
        
     *)