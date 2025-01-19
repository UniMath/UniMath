(* -*- coding: utf-8 *)

(** * Natural numbers *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Propositions.

Local Open Scope nat.

Notation ℕ := nat.

Module Uniqueness.

  Lemma helper_A (P:nat->Type) (p0:P 0) (IH:∏ n, P n->P(S n))
        (f:∏ n, P n) :
    weq (∏ n, f n = nat_rect P p0 IH n)
        (f 0=p0 × ∏ n, f(S n)=IH n (f n)).
  Proof.
    intros. simple refine (_,,isweq_iso _ _ _ _).
    { intros h. split.
      { exact (h 0). } { intros. exact (h (S n) @ maponpaths (IH n) (! h n)). } }
    { intros [h0 h'] ?. induction n as [|n' IHn'].
      { exact h0. } { exact (h' n' @ maponpaths (IH n') IHn'). } }
    { simpl. intros h. apply funextsec; intros n; simpl. induction n as [|n IHn].
      { simpl. reflexivity. }
      { simpl. rewrite <- path_assoc. simple refine (_ @ pathscomp0rid _).
        rewrite <- maponpathscomp0. rewrite IHn. rewrite pathsinv0l.
        simpl. reflexivity. } }
    { intros [h0 h']. apply maponpaths. apply funextsec; intro n; simpl.
      rewrite <- path_assoc. rewrite <- maponpathscomp0. rewrite pathsinv0r.
      apply pathscomp0rid. }
  Defined.

  Lemma helper_B (P:nat->Type) (p0:P 0) (IH:∏ n, P n->P(S n))
        (f:∏ n, P n) :
    weq (f = nat_rect P p0 IH)
        ((f 0=p0) × (∏ n, f(S n)=IH n (f n))).
  Proof.
    intros.
    exact (weqcomp (weqtoforallpaths _ _ _) (helper_A _ _ _ _)).
  Defined.

  Lemma helper_C (P:nat->Type) (p0:P 0) (IH:∏ n, P n->P(S n)) :
    (∑ f:∏ n, P n, f = nat_rect P p0 IH)
      ≃
    (∑ f:∏ n, P n, f 0=p0 × ∏ n, f(S n)=IH n (f n)).
  Proof.
    intros. apply weqfibtototal. intros f. apply helper_B.
  Defined.

  Lemma hNatRecursionUniq (P:nat->Type) (p0:P 0) (IH:∏ n, P n->P(S n)) :
    ∃! (f:∏ n, P n), f 0=p0 × ∏ n, f(S n) = IH n (f n).
  Proof.
    intros. exact (iscontrweqf (helper_C _ _ _) (iscontrcoconustot _ _)).
  Defined.

  Lemma helper_D (P:nat->Type) (p0:P 0) (IH:∏ n, P n->P(S n)) :
     (∑ f:∏ n, P n, (f 0=p0) × (∏ n, f(S n)=IH n (f n)))
       ≃
        (@hfiber
           (∑ (f:∏ n, P n), ∏ n, f(S n)=IH n (f n))
           (P 0)
           (λ fh, pr1 fh 0)
           p0).
  Proof.
    intros. simple refine (make_weq _ (isweq_iso _ _ _ _)).
    { intros [f [h0 h']]. exact ((f,,h'),,h0). }
    { intros [[f h'] h0]. exact (f,,(h0,,h')). }
    { intros [f [h0 h']]. reflexivity. }
    { intros [[f h'] h0]. reflexivity. }
  Defined.

  Lemma hNatRecursion_weq (P:nat->Type) (IH:∏ n, P n->P(S n)) :
    weq (total2 (fun f:∏ n, P n => ∏ n, f(S n)=IH n (f n))) (P 0).
  Proof.
    intros. exists (λ f, pr1 f 0). intro p0.
    apply (iscontrweqf (helper_D _ _ _)). apply hNatRecursionUniq.
  Defined.

End Uniqueness.

Fixpoint nat_dist (m n:nat) : nat :=
  match m , n with
    | S m, S n => nat_dist m n
    | 0, n => n
    | m, 0 => m end.

Module Discern.

  Fixpoint nat_discern (m n:nat) : UU :=
    match m , n with
      | S m, S n => nat_discern m n
      | 0, S n => empty
      | S m, 0 => empty
      | 0, 0 => unit end.

  Goal ∏ m n, nat_discern m n -> nat_discern (S m) (S n).
  Proof.
    intros ? ? e. exact e.
  Defined.

  Lemma nat_discern_inj m n : nat_discern (S m) (S n) -> nat_discern m n.
  Proof.
    intros e. induction m.
    { induction n. { exact tt. } { simpl in e. exact (fromempty e). } }
    { induction n. { simpl in e. exact (fromempty e). } { simpl in e. exact e. } }
  Defined.

  Lemma nat_discern_isaprop m n : isaprop (nat_discern m n).
  Proof.
    revert n; induction m as [|m IHm].
    { intros n. induction n as [|n IHn].
      { apply isapropifcontr. apply iscontrunit. }
      { simpl. apply isapropempty. } }
    { intros n. induction n as [|n IHn].
      { simpl. apply isapropempty. }
      { simpl. apply IHm. } }
  Defined.

  Lemma nat_discern_unit m : nat_discern m m = unit.
  Proof.
    induction m as [|m IHm]. { reflexivity. } { simpl. apply IHm. }
  Defined.

  Lemma nat_discern_iscontr m : iscontr (nat_discern m m).
  Proof.
    apply iscontraprop1.
    { apply nat_discern_isaprop. }
    { induction m as [|m IHm]. { exact tt. } { simpl. exact IHm. } }
  Defined.

  Fixpoint helper_A m n : nat_dist m n = 0 -> nat_discern m n.
  Proof.
    destruct m as [|m'].
    { destruct n as [|n'].
      { intros _. exact tt. } { simpl. exact (negpathssx0 n'). } }
    { destruct n as [|n'].
      { simpl. exact (negpathssx0 m'). } { simpl. exact (helper_A m' n'). } }
  Defined.

  Fixpoint helper_B m n : nat_discern m n -> m = n.
  Proof.
    destruct m as [|m'].
    { destruct n as [|n'].
      { intros _. reflexivity. } { simpl. exact fromempty. } }
    { destruct n as [|n'].
      { simpl. exact fromempty. }
      { simpl. intro i. assert(b := helper_B _ _ i); clear i.
        destruct b. reflexivity. } }
  Defined.

  Goal ∏ m n (e:nat_discern m n), maponpaths S (helper_B m n e) = helper_B (S m) (S n) e.
  Proof.
    reflexivity.
  Defined.

  Fixpoint helper_C m n : m = n -> nat_discern m n.
  Proof.
    intros e. destruct e.
         (* alternatively:
          destruct m. { exact tt. } { simpl. exact (the (nat_discern_iscontr _)). }
          *)
    exact (cast (! nat_discern_unit m) tt).
  Defined.

  Lemma apSC m n (e:m=n) : helper_C m n e = helper_C (S m) (S n) (maponpaths S e).
  Proof.
    intros. apply proofirrelevance. apply nat_discern_isaprop.
  Defined.

  Definition helper_D m n : isweq (helper_B m n).
  Proof.
    intros. simple refine (isweq_iso _ (helper_C _ _) _ _).
    { intro e. assert(p := ! helper_B _ _ e). destruct p.
      apply proofirrelevancecontr. apply nat_discern_iscontr. }
    { intro e. destruct e. induction m as [|m IHm].
      { reflexivity. }
      { exact (  maponpaths (helper_B (S m) (S m)) (! apSC _ _ (idpath m))
                            @ maponpaths (maponpaths S) IHm). } }
  Defined.

  Definition E m n : (nat_discern m n) ≃ (m = n).
  Proof.
    intros. exact (make_weq (helper_B _ _) (helper_D _ _)).
  Defined.

  Definition nat_dist_anti m n : nat_dist m n = 0 -> m = n.
  Proof.
    intros i. exact (helper_B _ _ (helper_A _ _ i)).
  Defined.

End Discern.

Fixpoint nat_dist_symm m n : nat_dist m n = nat_dist n m.
Proof.
  destruct m as [|m'].
  { destruct n as [|n']. { reflexivity. } { simpl. reflexivity. } }
  { destruct n as [|n'].
    { simpl. reflexivity. }
    { simpl. apply nat_dist_symm. } }
Defined.

Fixpoint nat_dist_ge m n : m ≥ n -> nat_dist m n = m-n.
Proof.
  induction m as [|m'].
  { induction n as [|n']. { reflexivity. } { intro f. now induction (!natleh0tois0 f). } }
  { induction n as [|n']. { reflexivity. } { exact (nat_dist_ge m' n'). } }
Defined.

Definition nat_dist_0m m : nat_dist 0 m = m.
Proof.
  reflexivity.
Defined.

Definition nat_dist_m0 m : nat_dist m 0 = m.
Proof.
  destruct m. { reflexivity. } { reflexivity. }
Defined.

Fixpoint nat_dist_plus m n : nat_dist (m + n) m = n.
Proof.
  revert m n; intros [|m'] ?.
  { simpl. apply nat_dist_m0. }
  { simpl. apply nat_dist_plus. }
Defined.

Fixpoint nat_dist_le m n : m ≤ n -> nat_dist m n = n-m.
Proof.
  destruct m as [|m'].
  { destruct n as [|n']. { reflexivity. } { simpl. intros _. reflexivity. } }
  { destruct n as [|n'].
    { intro f. now induction (!natleh0tois0 f). }
    { exact (nat_dist_le m' n'). } }
Defined.

Definition nat_dist_minus m n : m ≤ n -> nat_dist (n - m) n = m.
Proof.
  intros e. set (k := n-m). assert(b := ! minusplusnmm n m e).
  rewrite (idpath _ : n-m = k) in b. rewrite b.
  rewrite nat_dist_symm. apply nat_dist_plus.
Qed.

Fixpoint nat_dist_gt m n : m > n -> S (nat_dist m (S n)) = nat_dist m n.
Proof.
  destruct m as [|m'].
  { unfold natgth; simpl. intro x.
    apply fromempty. apply nopathsfalsetotrue. exact x. }
  { intro i. simpl.
    destruct n as [|n'].
    { apply (maponpaths S). apply nat_dist_m0. }
    { simpl. apply nat_dist_gt. exact i. } }
Defined.

Definition nat_dist_S m n : nat_dist (S m) (S n) = nat_dist m n.
Proof.
  reflexivity.
Defined.

Definition natminuseqlr m n x : m≤n -> n-m = x -> n = x+m.
Proof.
  intros i j.
  rewrite <- (minusplusnmm _ _ i). rewrite j. reflexivity.
Defined.

Definition nat_dist_between_le m n a b : m ≤ n -> nat_dist m n = a + b ->
  ∑ x, nat_dist x m = a × nat_dist x n = b.
Proof.
  intros i j. exists (m+a). split.
  { apply nat_dist_plus. }
  { rewrite (nat_dist_le m n i) in j.
    assert (k := natminuseqlr _ _ _ i j); clear j.
    assert (l := nat_dist_plus (m+a) b).
    rewrite nat_dist_symm. rewrite (natpluscomm (a+b) m) in k.
    rewrite (natplusassoc m a b) in l. rewrite <- k in l. exact l. }
Defined.

Definition nat_dist_between_ge m n a b :
  n ≤ m -> nat_dist m n = a + b -> ∑ x:nat, nat_dist x m = a × nat_dist x n = b.
Proof.
  intros i j.
  rewrite nat_dist_symm in j.
  rewrite natpluscomm in j.
  exists (pr1 (nat_dist_between_le n m b a i j)).
  apply (weqdirprodcomm _ _).
  exact (pr2 (nat_dist_between_le n m b a i j)).
Defined.

Definition nat_dist_between m n a b :
  nat_dist m n = a + b -> ∑ x:nat, nat_dist x m = a × nat_dist x n = b.
Proof.
  intros j.
  induction (natgthorleh m n) as [r|s].
  { apply nat_dist_between_ge. apply natlthtoleh. exact r. exact j. }
  { apply nat_dist_between_le. exact s. exact j. }
Defined.

Definition natleorle m n : (m≤n) ⨿ (n≤m).
Proof.
  intros.
  induction (natgthorleh m n) as [r|s].
  { apply ii2. apply natlthtoleh. exact r. }
  { apply ii1. exact s. }
Defined.

Definition nat_dist_trans x y z : nat_dist x z ≤ nat_dist x y + nat_dist y z.
Proof.
  intros. induction (natleorle x y) as [r|s].
  { rewrite (nat_dist_le _ _ r).
    induction (natleorle y z) as [t|u].
    { assert (u := istransnatgeh _ _ _ t r). rewrite (nat_dist_le _ _ t).
      rewrite (nat_dist_le _ _ u). apply (natlehandplusrinv _ _ x).
      rewrite (minusplusnmm _ _ u). rewrite (natpluscomm _ x).
      rewrite <- natplusassoc. rewrite (natpluscomm x).
      rewrite (minusplusnmm _ _ r). rewrite (natpluscomm y).
      rewrite (minusplusnmm _ _ t). apply isreflnatleh. }
    { rewrite (nat_dist_ge _ _ u).
      induction (natleorle x z) as [p|q].
      { rewrite (nat_dist_le _ _ p). apply (natlehandplusrinv _ _ x).
        rewrite (minusplusnmm _ _ p). rewrite natpluscomm.
        rewrite <- natplusassoc. rewrite (natpluscomm x).
        rewrite (minusplusnmm _ _ r). apply (natlehandplusrinv _ _ z).
        rewrite natplusassoc. rewrite (minusplusnmm _ _ u).
        apply (istransnatleh (m := y+z)).
        { apply natlehandplusr. exact u. }
        { apply natlehandplusl. exact u. } }
      { rewrite (nat_dist_ge _ _ q). apply (natlehandplusrinv _ _ z).
        rewrite (minusplusnmm _ _ q). rewrite natplusassoc.
        rewrite (minusplusnmm _ _ u). rewrite natpluscomm.
        apply (natlehandplusrinv _ _ x). rewrite natplusassoc.
        rewrite (minusplusnmm _ _ r). apply (istransnatleh (m := x+y)).
        { apply natlehandplusl. assumption. }
        { apply natlehandplusr. assumption. } } } }
  { rewrite (nat_dist_ge _ _ s).
    induction (natleorle z y) as [u|t].
    { assert (w := istransnatleh u s). rewrite (nat_dist_ge _ _ w).
      rewrite (nat_dist_ge _ _ u). apply (natlehandplusrinv _ _ z).
      rewrite (minusplusnmm _ _ w). rewrite natplusassoc.
      rewrite (minusplusnmm _ _ u). rewrite (minusplusnmm _ _ s).
      apply isreflnatleh. }
    { rewrite (nat_dist_le _ _ t).
      induction (natleorle x z) as [p|q].
      { rewrite (nat_dist_le _ _ p). apply (natlehandplusrinv _ _ x).
        rewrite (minusplusnmm _ _ p). apply (natlehandpluslinv _ _ y).
        rewrite (natplusassoc (x-y)). rewrite <- (natplusassoc y).
        rewrite (natpluscomm y (x-y)). rewrite (minusplusnmm _ _ s).
        apply (natlehandplusrinv _ _ y). rewrite (natplusassoc x).
        rewrite (natplusassoc _ x y). rewrite (natpluscomm x y).
        rewrite <- (natplusassoc _ y x). rewrite (minusplusnmm _ _ t).
        rewrite (natpluscomm z x). rewrite <- (natplusassoc x).
        rewrite (natplusassoc y). rewrite (natpluscomm z y).
        rewrite <- (natplusassoc y). apply (natlehandplusr _ _ z).
        apply (istransnatleh (m := x+y)).
        { apply natlehandplusr. assumption. }
        { apply natlehandplusl. assumption. } }
      { rewrite (nat_dist_ge _ _ q). apply (natlehandplusrinv _ _ z).
        rewrite (minusplusnmm _ _ q). apply (natlehandpluslinv _ _ y).
        rewrite (natplusassoc (x-y)). rewrite <- (natplusassoc y).
        rewrite (natpluscomm y (x-y)). rewrite (minusplusnmm _ _ s).
        apply (natlehandplusrinv _ _ y). rewrite (natplusassoc x).
        rewrite (natplusassoc _ z y). rewrite (natpluscomm z y).
        rewrite <- (natplusassoc _ y z). rewrite (minusplusnmm _ _ t).
        rewrite (natpluscomm y x). rewrite (natplusassoc x).
        apply natlehandplusl. apply (istransnatleh (m := z+y)).
        { apply natlehandplusr. assumption. }
        { apply natlehandplusl. assumption. } } } }
Defined.

Lemma plusmn0n0 m n : m + n = 0 -> n = 0.
Proof.
  intros i. assert (a := natlehmplusnm m n). rewrite i in a.
  apply natleh0tois0. assumption.
Defined.

Lemma plusmn0m0 m n : m + n = 0 -> m = 0.
Proof.
  intros i. assert (a := natlehnplusnm m n). rewrite i in a.
  apply natleh0tois0. assumption.
Defined.

Lemma natminus0le {m n} : m-n = 0 -> n ≥ m.
Proof.
  intros i. apply negnatgthtoleh. intro k.
  assert (r := minusgth0 _ _ k); clear k.
  induction (!i); clear i. exact (negnatgth0n 0 r).
Defined.

Lemma minusxx m : m - m = 0.
Proof.
  induction m as [|m IHm]. reflexivity. simpl. assumption.
Defined.

Lemma minusSxx m : S m - m = 1.
Proof.
  induction m as [|m IHm]. reflexivity. assumption.
Defined.

Lemma natminusminus n m : m ≤ n -> n - (n - m) = m.
Proof.
  intros i. assert (b := plusminusnmm m (n-m)).
  rewrite natpluscomm in b. rewrite (minusplusnmm _ _ i) in b.
  exact b.
Defined.

Lemma natplusminus m n k : k=m+n -> k-n=m.
Proof.
  intros i. rewrite i. apply plusminusnmm.
Defined.

Lemma natleplusminus k m n : k + m ≤ n -> k ≤ n - m.
Proof.
  intros i.
  apply (natlehandplusrinv _ _ m).
  rewrite minusplusnmm.
  { exact i. }
  { change (m ≤ n).
    simple refine (istransnatleh _ i); clear i.
    apply natlehmplusnm. }
Defined.

Lemma natltminus1 m n : m < n -> m ≤ n - 1.
Proof.
  intros i. assert (a := natlthp1toleh m (n - 1)).
  assert (b := natleh0n m). assert (c := natlehlthtrans _ _ _ b i).
  assert (d := natlthtolehsn _ _ c). assert (e := minusplusnmm _ _ d).
  rewrite e in a. exact (a i).
Defined.

Fixpoint natminusminusassoc m n k : (m-n)-k = m-(n+k).
Proof.
  intros. destruct m. { reflexivity. }
                      { destruct n. { rewrite natminuseqn. reflexivity. }
                                    { simpl. apply natminusminusassoc. } }
Defined.

Definition natminusplusltcomm m n k : k ≤ n -> m ≤ n - k -> k ≤ n - m.
Proof.
  intros i p.
  assert (a := natlehandplusr m (n-k) k p); clear p.
  assert (b := minusplusnmm n k i); clear i.
  rewrite b in a; clear b. apply natleplusminus.
  rewrite natpluscomm. exact a.
Qed.

Theorem nat_le_diff
        {n m : ℕ}
        (p : n ≤ m)
  : ∑ (k : ℕ), n + k = m.
Proof.
  exists (m - n).
  rewrite natpluscomm.
  exact (minusplusnmm _ _ p).
Qed.


(** * Bounded quantification *)

(** ** Some results on bounded quantification *)

Lemma weqforallnatlehn0 ( F : nat -> hProp ) :
  ( ∏ n : nat , natleh n 0 -> F n ) ≃ ( F 0 ).
Proof.
  intros.
  assert ( lg : ( ∏ n : nat , natleh n 0 -> F n ) <-> ( F 0 ) ).
  { split.
    - intro f.
      apply ( f 0 ( isreflnatleh 0 ) ).
    - intros f0 n l.
      set ( e := natleh0tois0 l ).
      rewrite e.
      apply f0.
  }
  assert ( is1 : isaprop ( ∏ n : nat , natleh n 0 -> F n ) ).
  { apply impred.
    intro n.
    apply impred.
    intro l.
    apply ( pr2 ( F n ) ).
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 ( pr2 ( F 0 ) ) ).
Defined.

Lemma weqforallnatlehnsn' ( n' : nat ) ( F : nat -> hProp ) :
  ( ∏ n : nat , natleh n ( S n' ) -> F n ) ≃
  ( ∏ n : nat , natleh n n' -> F n ) × ( F ( S n' ) ).
Proof.
  intros.
  assert ( lg : ( ∏ n : nat , natleh n ( S n' ) -> F n ) <->
                ( ∏ n : nat , natleh n n' -> F n ) × ( F ( S n' ) ) ).
  { split.
    - intro f.
      apply ( make_dirprod ( λ n, λ l, ( f n ( natlehtolehs _ _ l ) ) )
                          ( f ( S n' ) ( isreflnatleh _ ) ) ).
    - intro d2.
      intro n. intro l.
      destruct ( natlehchoice2 _ _ l ) as [ h | e ].
      + simpl in h.
        apply ( pr1 d2 n h ).
      + destruct d2 as [ f2 d2 ].
        rewrite e.
        apply d2.
  }
  assert ( is1 : isaprop ( ∏ n : nat , natleh n ( S n' ) -> F n ) ).
  { apply impred.
    intro n.
    apply impred.
    intro l.
    apply ( pr2 ( F n ) ).
  }
  assert ( is2 : isaprop ( ( ∏ n : nat , natleh n n' -> F n ) × ( F ( S n' ) ) ) ).
  { apply isapropdirprod.
    - apply impred.
      intro n.
      apply impred.
      intro l.
      apply ( pr2 ( F n ) ).
    - apply ( pr2 ( F ( S n' ) ) ).
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 is2 ).
Defined.

Lemma weqexistsnatlehn0 ( P : nat -> hProp  ) :
  ( hexists ( λ n : nat, ( natleh n 0 ) × ( P n ) ) ) ≃ P 0.
Proof.
  assert ( lg : hexists ( λ n : nat, ( natleh n 0 ) × ( P n ) ) <-> P 0  ).
  { split.
    - simpl.
      apply ( @hinhuniv _ ( P 0 ) ).
      intro t2.
      destruct t2 as [ n d2 ].
      destruct d2 as [ l p ].
      set ( e := natleh0tois0 l ).
      clearbody e.
      destruct e.
      apply p.
    - intro p.
      apply hinhpr.
      split with 0.
      split with ( isreflnatleh 0 ).
      apply p.
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ).
Defined.

Lemma weqexistsnatlehnsn' ( n' : nat ) ( P : nat -> hProp  ) :
  ( hexists ( λ n : nat, ( natleh n ( S n' ) ) × ( P n ) ) ) ≃
  hdisj ( hexists ( λ n : nat, ( natleh n n' ) × ( P n ) ) )  ( P ( S n' ) ).
Proof.
  intros.
  assert ( lg : hexists ( λ n : nat, ( natleh n ( S n' ) ) × ( P n ) ) <->
                hdisj ( hexists ( λ n : nat, ( natleh n n' ) × ( P n ) ) )  ( P ( S n' ) ) ).
  { split.
    - apply hinhfun.
      intro t2.
      destruct t2 as [ n d2 ].
      destruct d2 as [ l p ].
      destruct ( natlehchoice2 _ _ l ) as [ h | nh ].
      + simpl in h.
        apply ii1.
        apply hinhpr.
        split with n.
        apply ( make_dirprod h p ).
      + destruct nh.
        apply ( ii2 p ).
    - simpl.
      apply ( @hinhuniv _ ( ishinh _ ) ).
      intro c.
      destruct c as [ t | p ].
      + generalize t.
        simpl.
        apply hinhfun.
        clear t.
        intro t.
        destruct t as [ n d2 ].
        destruct d2 as [ l p ].
        split with n.
        split with ( natlehtolehs _ _ l ).
        apply p.
      + apply hinhpr.
        split with ( S n' ).
        split with ( isreflnatleh _ ).
        apply p.
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ).
Defined.


Lemma isdecbexists ( n : nat ) ( P : nat -> UU ) ( is : ∏ n' , isdecprop ( P n' ) ) :
  isdecprop ( hexists ( λ n', ( natleh n' n ) × ( P n' ) ) ).
Proof.
  intros.
  set ( P' := λ n' : nat, make_hProp _ ( is n' ) ).
  induction n as [ | n IHn ].
  - apply ( isdecpropweqb ( weqexistsnatlehn0 P' ) ).
    apply ( is 0 ).
  - apply ( isdecpropweqb ( weqexistsnatlehnsn' _ P' ) ).
    apply isdecprophdisj.
    + apply IHn.
    + apply ( is ( S n ) ).
Defined.

Lemma isdecbforall ( n : nat ) ( P : nat -> UU ) ( is : ∏ n' , isdecprop ( P n' ) ) :
  isdecprop ( ∏ n' , natleh n' n -> P n' ).
Proof.
  intros.
  set ( P' := λ n' : nat, make_hProp _ ( is n' ) ).
  induction n as [ | n IHn ].
  - apply ( isdecpropweqb ( weqforallnatlehn0 P' ) ).
    apply ( is 0 ).
  - apply ( isdecpropweqb ( weqforallnatlehnsn' _ P' ) ).
    apply isdecpropdirprod.
    + apply IHn.
    + apply ( is ( S n ) ).
Defined.



(** The following lemma finds the largest [ n' ] such that [ neg ( P n' ) ]. It is a stronger form of ( neg ∏ ) -> ( exists neg ) in the case of bounded quantification of decidable propositions. *)

Lemma negbforalldectototal2neg ( n : nat ) ( P : nat -> UU )
  ( is : ∏ n' : nat , isdecprop ( P n' ) ) :
  ¬ ( ∏ n' : nat , natleh n' n -> P n' ) ->
  total2 ( λ n', ( natleh n' n ) × ¬ ( P n' ) ).
Proof.
  set ( P' := λ n' : nat, make_hProp _ ( is n' ) ).
  induction n as [ | n IHn ].
  - intro nf.
    set ( nf0 := negf ( invweq ( weqforallnatlehn0 P' ) ) nf ).
    split with 0.
    apply ( make_dirprod ( isreflnatleh 0 ) nf0 ).
  - intro nf.
    set ( nf2 := negf ( invweq ( weqforallnatlehnsn' n P' ) ) nf ).
    set ( nf3 := fromneganddecy ( is ( S n ) ) nf2 ).
    destruct nf3 as [ f1 | f2 ].
    + set ( int := IHn f1 ).
      destruct int as [ n' d2 ].
      destruct d2 as [ l np ].
      split with n'.
      split with ( natlehtolehs _ _ l ).
      apply np.
    + split with ( S n ).
      split with ( isreflnatleh _ ).
      apply f2.
Defined.


(** ** Accessibility - the least element of an inhabited decidable subset of [nat] *)

Definition natdecleast ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) ) :=
  total2 ( λ  n : nat, ( F n ) × ( ∏ n' : nat , F n' -> natleh n n' ) ).

Lemma isapropnatdecleast ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) ) :
  isaprop ( natdecleast F is ).
Proof.
  intros.
  set ( P := λ n' : nat, make_hProp _ ( is n' ) ).
  assert ( int1 : ∏ n : nat, isaprop ( ( F n ) × ( ∏ n' : nat , F n' -> natleh n n' ) ) ).
  { intro n.
    apply isapropdirprod.
    - apply ( pr2 ( P n ) ).
    - apply impred.
      intro t.
      apply impred.
      intro.
      apply ( pr2 ( natleh n t ) ).
  }
  set ( int2 := ( λ n : nat, make_hProp _ ( int1 n ) ) : nat -> hProp ).
  change ( isaprop ( total2 int2 ) ).
  apply isapropsubtype.
  intros x1 x2. intros c1 c2.
  simpl in *.
  destruct c1 as [ e1 c1 ].
  destruct c2 as [ e2 c2 ].
  set ( l1 := c1 x2 e2 ).
  set ( l2 := c2 x1 e1 ).
  apply ( isantisymmnatleh _ _ l1 l2 ).
Defined.

Theorem accth ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) )
        ( is' : hexists F ) : natdecleast F is.
Proof.
  revert is'.
  simpl.
  apply (@hinhuniv _ ( make_hProp _ ( isapropnatdecleast F is ) ) ).
  intro t2.
  destruct t2 as [ n l ].
  simpl.
  set ( F' := λ n' : nat, hexists ( λ n'', ( natleh n'' n' ) × ( F n'' ) ) ).
  assert ( X : ∏ n' , F' n' -> natdecleast F is ).
  { intro n'.
    induction n' as [ | n' IHn' ].
    - apply ( @hinhuniv _  ( make_hProp _ ( isapropnatdecleast F is ) ) ).
      intro t2.
      destruct t2 as [ n'' is'' ].
      destruct is'' as [ l'' d'' ].
      split with 0.
      split.
      + set ( e := natleh0tois0 l'' ).
        clearbody e.
        destruct e.
        apply d''.
      + apply ( λ n', λ f : _, natleh0n n' ).
    - apply ( @hinhuniv _  ( make_hProp _ ( isapropnatdecleast F is ) ) ).
      intro t2.
      destruct t2 as [ n'' is'' ].
      set ( j := natlehchoice2 _ _ ( pr1 is'' ) ).
      destruct j as [ jl | je ].
      + simpl.
        apply ( IHn' ( hinhpr ( tpair _ n'' ( make_dirprod jl ( pr2 is'' ) ) ) ) ).
      + simpl.
        rewrite je in is''.
        destruct is'' as [ nn is'' ].
        clear nn. clear je. clear n''.
        assert ( is' : isdecprop ( F' n' ) ) by apply ( isdecbexists n' F is ).
        destruct ( pr1 is' ) as [ f | nf ].
        * apply ( IHn'  f ).
        * split with ( S n' ).
          split with is''.
          intros n0 fn0.
          destruct ( natlthorgeh n0 ( S n' ) )  as [ l' | g' ].
          -- set ( i' := natlthtolehsn _ _ l' ).
             destruct ( nf ( hinhpr ( tpair _ n0 ( make_dirprod i' fn0 ) ) ) ).
          -- apply g'.
  }
  apply ( X n ( hinhpr ( tpair _ n ( make_dirprod ( isreflnatleh n ) l ) ) ) ).
Defined.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/Nat.vo"
End:
*)
