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
      |= [|a1 = a2 ->b (n1 <=? n2)%nat|]
  | SmAndTrue : forall b1 b2,
    [|b1|]f |= [|b1 && b2|]f
  | SmAndFalse : forall b1 b2 v,
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
    LP([| a -> n |] ; {[(s, (i |-> n; s))]}) |= [|i := a|]
  | SmSeq : forall c1 c2,
    LP([|c1|]; [|c2|]) |= [|c1; c2|]
  | SmIfTrue : forall b c1 c2,
    LP([|b|]t ; [|c1|]) 
      |= [|if b then c1 else c2 end|]
  | SmIfFasle : forall b c1 c2,
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


(*  *)

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
  | SmTrue' : forall s,
    LP({[(s, s)]}) |= [|true|]'t
  | SmFalse' : forall s,
    LP({[(s, s)]}) |= [|false|]'f
  | SmNot' : forall b v,
    [|b ->b v|]' |= [|~b ->b negb v|]'
  | SmEq' : forall a1 a2 n1 n2,
    LP([|a1 -> n1|]' + [|a2 -> n2|]')
      |= [|a1 = a2 ->b (n1 =? n2)%nat|]'
  | SmLe' : forall a1 a2 n1 n2,
    LP([|a1 -> n1|]' + [|a2 -> n2|]') 
      |= [|a1 = a2 ->b (n1 <=? n2)%nat|]'
  | SmAndTrue' : forall b1 b2,
    [|b1|]'f |= [|b1 && b2|]'f
  | SmAndFalse' : forall b1 b2 v,
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
    LP([| a -> n |]' + {[(s, (i |-> n; s))]}) |= [|i := a|]'
  | SmSeq' : forall c1 c2,
    LP([|c1|]' + [|c2|]') |= [|c1; c2|]'
  | SmIfTrue' : forall b c1 c2,
    LP([|b|]'t + [|c1|]') 
      |= [|if b then c1 else c2 end|]'
  | SmIfFasle' : forall b c1 c2,
    LP([|b|]'f + [|c2|]')
      |= [|if b then c1 else c2 end|]'
  | SmWhile' : forall b c,
    LP(([|b|]'t + [|c|]')* + [|b|]'f) (* star does not include ^, unlike Brookes*)
      |= [|while b do c end|]'
  | SmPar' : forall c1 c2,
    LP([|c1|]' # [|c2|]') |= [|c1 || c2|]'
  | SmAwait' : forall b c s s',
    [|b|]'t [(s, s)]
      ->
    [|c|]' [(s, s')]
      ->
    LP({[(s, s')]}) |= [|await b then c end|]'
  where "[| c |]'" := (CSemantics' c).
#[global] Hint Constructors CSemantics' : core.

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
  
Theorem BSemantics_equiv' :
  forall a v,
    [|a ->b v|] ~ LP([|a ->b v|]'^).
Proof with ellipsis.