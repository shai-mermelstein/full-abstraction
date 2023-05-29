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
    LP{[(s, s)]^} |= [|n -> n|] 
  | SmId : forall s (i : identifier),
    LP{[(s, s)]^} |= [|i -> s i|] 
  | SmPlus : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|] ; [|a2 -> n2|]}
      |= [|a1 + a2 -> n1 + n2|]
  | SmMinus : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|] ; [|a2 -> n2|]} 
      |= [|a1 - a2 -> n1 - n2|]
  | SmMult : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|] ; [|a2 -> n2|]} 
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
    LP{[(s, s)]^} |= [|true|]t
  | SmFalse : forall s,
    LP{[(s, s)]^} |= [|false|]f
  | SmNot : forall b v,
    [|b ->b v|] |= [|~b ->b negb v|]
  | SmEq : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|] ; [|a2 -> n2|]} 
      |= [|a1 = a2 ->b (n1 =? n2)%nat|]
  | SmLe : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|] ; [|a2 -> n2|]} 
      |= [|a1 <= a2 ->b (n1 <=? n2)%nat|]
  | SmAndFalse : forall b1 b2,
    [|b1|]f |= [|b1 && b2|]f
  | SmAndTrue : forall b1 b2 v,
    LP{[|b1|]t ; [|b2 ->b v|]} 
      |= [|b1 && b2 ->b v|]
  where "[| b |]t" := (BSemantics b true)
  and   "[| b |]f" := (BSemantics b false)
  and   "[| b ->b v |]" := (BSemantics b v).
#[global] Hint Constructors BSemantics : core.

Reserved Notation "[| c |]"
  (at level 0, c custom com at level 99).
Inductive CSemantics : com -> pairsP state :=
  | SmSkip : forall s,
    LP{[(s, s)]^} |= [|skip|]
  | SmAsgn : forall i a n s,
    LP{[|a -> n|] ; [(s, (i |-> n; s))]} 
      |= [|i := a|]
  | SmSeq : forall c1 c2,
    LP{[|c1|]; [|c2|]} |= [|c1; c2|]
  | SmIfTrue : forall b c1 c2,
    LP{[|b|]t ; [|c1|]} 
      |= [|if b then c1 else c2 end|]
  | SmIfFalse : forall b c1 c2,
    LP{[|b|]f ; [|c2|]}
      |= [|if b then c1 else c2 end|]
  | SmWhile : forall b c,
    LP{([|b|]t ; [|c|])* ; [|b|]f} (* star does not include ^, unlike Brookes*)
      |= [|while b do c end|]
  | SmPar : forall c1 c2,
    LP{[|c1|] || [|c2|]} |= [|c1 || c2|]
  | SmAwait : forall b c s s',
    [|b|]t [(s, s)]
      ->
    [|c|] [(s, s')]
      ->
    LP{[(s, s')]^} |= [|await b then c end|]
  where "[| c |]" := (CSemantics c).
#[global] Hint Constructors CSemantics : core.

(* delayed ^ *)

Reserved Notation "[| a -> n |]'"
  (at level 0, a custom com at level 99).
Inductive ASemantics' : aexp -> nat -> pairsP state :=
  | SmNum' : forall s (n : nat),
    LP{[(s, s)]} |= [|n -> n|]'
  | SmId' : forall s (i : identifier),
    LP{[(s, s)]} |= [| i -> s i|]' 
  | SmPlus' : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|]' + [|a2 -> n2|]'}
      |= [|a1 + a2 -> n1 + n2|]'
  | SmMinus' : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|]' + [|a2 -> n2|]'}
      |= [|a1 - a2 -> n1 - n2|]'
  | SmMult' : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|]' + [|a2 -> n2|]'} 
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
    LP{[(s, s)]} |= [|true|]'t
  | SmTrue' : forall s,
    LP{[(s, s)]} |= [|false|]'f
  | SmNot' : forall b v,
    [|b ->b v|]' |= [|~b ->b negb v|]'
  | SmEq' : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|]' + [|a2 -> n2|]'}
      |= [|a1 = a2 ->b (n1 =? n2)%nat|]'
  | SmLe' : forall a1 a2 n1 n2,
    LP{[|a1 -> n1|]' + [|a2 -> n2|]'}
      |= [|a1 <= a2 ->b (n1 <=? n2)%nat|]'
  | SmAndFalse' : forall b1 b2,
    [|b1|]'f |= [|b1 && b2|]'f
  | SmAndTrue' : forall b1 b2 v,
    LP{[|b1|]'t + [|b2 ->b v|]'}
      |= [|b1 && b2 ->b v|]'
  where "[| b |]'t" := (BSemantics' b true)
  and   "[| b |]'f" := (BSemantics' b false)
  and   "[| b ->b v |]'" := (BSemantics' b v).
#[global] Hint Constructors BSemantics' : core.

Reserved Notation "[| c |]'"
  (at level 0, c custom com at level 99).
Inductive CSemantics' : com -> pairsP state :=
  | SmSkip' : forall s,
    LP{[(s, s)]} |= [|skip|]'
  | SmAsgn' : forall i a n s,
    LP{[| a -> n |]' + [(s, (i |-> n; s))]} 
      |= [|i := a|]'
  | SmSeq' : forall c1 c2,
    LP{[|c1|]' + [|c2|]'} |= [|c1; c2|]'
  | SmIfTrue' : forall b c1 c2,
    LP{[|b|]'t + [|c1|]'} 
      |= [|if b then c1 else c2 end|]'
  | SmIfFalse' : forall b c1 c2,
    LP{[|b|]'f + [|c2|]'}
      |= [|if b then c1 else c2 end|]'
  | SmWhile' : forall b c,
    LP{([|b|]'t + [|c|]')* + [|b|]'f} 
      |= [|while b do c end|]'
  | SmPar' : forall c1 c2,
    LP{[|c1|]' # [|c2|]'} |= [|c1 || c2|]'
  | SmAwait' : forall b c s s',
    LP{[|b|]'t^} [(s, s)]
      ->
    LP{[|c|]'^} [(s, s')]
      ->
    LP{[(s, s')]} |= [|await b then c end|]'
  where "[| c |]'" := (CSemantics' c).
#[global] Hint Constructors CSemantics' : core.

(* stuttery mumbly *)

Theorem ASemantics_stuttery_mumbly :
  forall a n, stuttery_mumbly [|a -> n|].
Proof with ellipsis.
  intros a n ts H. destruct a.
  - assert (n0 = n); subst.
    { clean_induction H... }
    assert (exists s, LP{[(s, s)]^} ts)...
    { 
      clean_induction H...
      - invert H.
      - destruct IHstutter_mumble_closure as [s].
        exists s...
      - destruct IHstutter_mumble_closure as [s].
        exists s...
    }
    destruct H0 as [s]. eapply SmNum...
  - assert (exists s, LP{[(s, s)]^} ts /\ n = s i)...
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

Theorem BSemantics_stuttery_mumbly :
  forall b v, stuttery_mumbly [|b ->b v|].
Proof with ellipsis.
  intro b. clean_induction b; intros ts H.
  - assert (v = true); subst.
    { clean_induction H... }
    assert (exists s, LP{[(s, s)]^} ts)...
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
    assert (exists s, LP{[(s, s)]^} ts)...
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

Theorem CSemantics_stuttery_mumbly :
  forall c, stuttery_mumbly [|c|].
Proof with ellipsis.
  intros c ts H. destruct c.
  - assert (exists s, LP{[(s, s)]^} ts)...
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
      LP{[| a -> n |] ; [(s, (i |-> n; s))]} ts
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

(* equiv' *)

Theorem ASemantics_equiv' :
  forall a n,
    [|a -> n|] ~ LP{[|a -> n|]'^}.
Proof with ellipsis.
  intros a n ts; split.
  - generalize dependent ts.
    generalize dependent n.
    clean_induction a; invert H;
      eapply sm_closure_implication; ellipsis;
      eapply sm_closure_implication'; ellipsis;
      clear H4 ts; intro ts; intros;
      destruct H as [ts1 [ts2 [H []]]];
      clean_apply_in IHa1 H;
      clean_apply_in IHa2 H0;
      apply sm_closure_app...
  - intros.
    apply ASemantics_stuttery_mumbly.
    eapply sm_closure_implication...
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

Theorem BSemantics_equiv' :
  forall b v,
    [|b ->b v|] ~ LP{[|b ->b v|]'^}.
Proof with ellipsis.
  intros b v ts; split.
  - generalize dependent ts.
    generalize dependent v.
    clean_induction b; invert H;
      try solve [
        eapply sm_closure_implication; ellipsis;
        eapply sm_closure_implication'; ellipsis;
        clear H4 ts; intro ts; intros;
        destruct H as [ts1 [ts2 [H []]]];
        apply ASemantics_equiv' in H;
        apply ASemantics_equiv' in H0;
        apply sm_closure_app; ellipsis
      ].
      + clean_apply_in IHb1 H4. clear IHb2.
        apply sm_closure_implication
          with ([|b1 |]'f)...
      + eapply sm_closure_implication; ellipsis;
        eapply sm_closure_implication'; ellipsis;
        clear H4 ts; intro ts; intros;
        destruct H as [ts1 [ts2 [H []]]];
        clean_apply_in IHb1 H;
        clean_apply_in IHb2 H0;
        apply sm_closure_app...
  - intros.
    apply BSemantics_stuttery_mumbly.
    eapply sm_closure_implication...
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

Theorem CSemantics_equiv' :
  forall c,
    [|c|] ~ LP{[|c|]'^}.
Proof with ellipsis.
  intros c ts; split.
  - generalize dependent ts.
    clean_induction c; invert H.
    + eapply sm_closure_implication...
    + eapply sm_closure_implication
        with LP{[|a -> n|]' + [(s, i |-> n; s)]}...
      eapply sm_closure_implication'...
      clear H3 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      apply ASemantics_equiv' in H.
      apply sm_closure_app...
    + eapply sm_closure_implication...
      eapply sm_closure_implication'...
      clear H3 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      clean_apply_in IHc1 H.
      clean_apply_in IHc2 H0.
      apply sm_closure_app...
    + eapply sm_closure_implication
        with LP{[|b|]'t + [|c1|]'}...
      eapply sm_closure_implication'...
      clear H4 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      apply BSemantics_equiv' in H.
      clean_apply_in IHc1 H0.
      apply sm_closure_app...
    + eapply sm_closure_implication...
      eapply sm_closure_implication'...
      clear H4 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      apply BSemantics_equiv' in H.
      clean_apply_in IHc2 H0.
      apply sm_closure_app...
    + eapply sm_closure_implication...
      eapply sm_closure_implication'...
      clear H3 ts; intro ts; intros.
      destruct H as [ts1 [ts2 [H []]]].
      assert (LP{([|b|]'t ; [|c|]')*} ts1).
      {
        clear H0 H1 ts ts2.
        eapply star_implication...
        eapply sm_closure_implication'...
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
    + eapply sm_closure_implication...
      eapply sm_closure_implication'...
      clear H3 ts; intro ts; intros.
      eapply int_implication 
        with (P' := LP{[|c1|]'^}) (Q' := LP{[|c2|]'^})
        in H...
      apply sm_closure_int...
    + eapply sm_closure_implication...
      apply BSemantics_equiv' in H2.
      clean_apply_in IHc H3.
  - intros.
    apply CSemantics_stuttery_mumbly.
    eapply sm_closure_implication...
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
      apply star_implies_sm_closure_star.
      apply star_implication
        with LP{[|b|]'t + [|c|]'}...
      clear H ts. intros ts H.
      destruct H as [ts1 [ts2 [H []]]].
      apply sm_self in H.
      apply BSemantics_equiv' in H.
      clean_apply_in IHc H0... 
    + destruct H3 as [ts1 [ts2 [H []]]].
      apply SmPar. apply sm_self.
      eapply int_implication...
    + apply BSemantics_equiv' in H2...
      apply sm_closure_implication 
        in IHc.
      clean_apply_in IHc H3.
      apply CSemantics_stuttery_mumbly
        in H3.
      eapply SmAwait with s s'...
Qed.

(* nil not in Semantics *)

Lemma nil_not_in_ASemantics :
  forall a n, ~ [|a -> n|] nil.
Proof with ellipsis.
  intros. intro C.
  generalize dependent n.
  clean_induction a; invert C; remember [] as N...
  - replace ((s, s) :: N) with [(s, s)] in H0...
    clean_induction H0; try destruct l1...
  - replace ((s, s) :: N) with [(s, s)] in H0...
    clean_induction H0; try destruct l1...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
Qed.

Lemma nil_not_in_BSemantics :
  forall b v, ~ [|b ->b v|] nil.
Proof with ellipsis.
  intros. intro C.
  generalize dependent v.
  clean_induction b; invert C; remember [] as N...
  - replace ((s, s) :: N) with [(s, s)] in H...
    clean_induction H; try destruct l1...
  - replace ((s, s) :: N) with [(s, s)] in H...
    clean_induction H; try destruct l1...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1... 
    apply nil_not_in_ASemantics in H...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1... 
    apply nil_not_in_ASemantics in H...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
Qed.

Lemma nil_not_in_CSemantics :
  forall c, ~ [|c|] nil.
Proof with ellipsis.
  intros. intro C.
  induction c; invert C; remember [] as N...
  - replace ((s, s) :: N) with [(s, s)] in H...
    clean_induction H; try destruct l1...
  - replace ((s, i |-> n; s) :: N) 
      with [(s, i |-> n; s)] in H2...
    clean_induction H2; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
  - clean_induction H2; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
  - clean_induction H3; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
  - clean_induction H2; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...  destruct l2...
    clear IHc H H1 c.
    apply nil_not_in_BSemantics in H0...
  - clean_induction H2; try destruct l1...
    destruct H as [l1 [l2 [H []]]].
    destruct l1...
  - replace ((s, s') :: N) with [(s, s')] in H4...
    clean_induction H4; try destruct l1...
Qed.