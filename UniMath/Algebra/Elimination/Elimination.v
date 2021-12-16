 (** * Matrices

Gaussian Elimination over integers.

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.WellOrderedSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Maybe.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.NumberSystems.Integers.
Require Import UniMath.NumberSystems.RationalNumbers.
Require Import UniMath.Tactics.Nat_Tactics.

Require Import UniMath.PAdics.z_mod_p.
Require Import UniMath.PAdics.lemmas.

Require Import UniMath.RealNumbers.Prelim.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.
Require Import UniMath.Algebra.Elimination.Matrices.
Require Import UniMath.Algebra.Elimination.RowOps.


Section Gauss.

  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition maybe_choice {X : UU} (e : maybe X)
    : coprod (e != nothing) (e = nothing).
  Proof.
    destruct e.
    - apply ii1. apply negpathsii1ii2.
    - apply ii2. rewrite u. exists.
  Defined.

  Definition maybe_stn_choice
      {X : UU} { n : nat }
      (e : maybe (⟦ n ⟧)%stn)
    : coprod (∑ i : ⟦ n ⟧%stn, e = just i) (e = nothing).
  Proof.
    destruct e as [i | ?].
    - apply ii1. use tpair. {exact i. } simpl. reflexivity.
    - apply ii2. rewrite u. exists.
  Defined.

  Definition is_leading_entry {n : nat} (v : Vector hq n) (i_1 : ⟦ n ⟧%stn) :=
      (∏ i_2 : ⟦ n ⟧%stn, i_2 < i_1 -> (v i_2) = 0%hq).

  Definition is_leading_entry_dual {n : nat} (v : Vector hq n) (i_1 : ⟦ n ⟧%stn) :=
      (∏ i_2 : ⟦ n ⟧%stn, i_1 < i_2 -> (v i_2) = 0%hq).

  Definition flip_vector {X : UU} {n: nat} (v : Vector X n) := (λ i : ⟦ n ⟧%stn, v (dualelement i)).

  Lemma dualelement_2x {n : nat} (i : ⟦ n ⟧%stn) : dualelement (dualelement i) = i.
  Proof.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | gt].
    { simpl. apply fromstn0. rewrite <- contr_eq in i. assumption. }
    simpl.
    set (m := n - 1).
    try rewrite lemmas.natdoubleminus.
    unfold make_stn.
    apply subtypePath_prop.
    simpl.
    rewrite (lemmas.doubleminuslehpaths m i); try reflexivity.
    unfold m.
    apply lemmas.minusnleh1.
    apply (pr2 i).
  Defined.

  Lemma dualelement_eq {n : nat} (i j : ⟦ n ⟧%stn)
    : dualelement i = j -> i = dualelement j.
  Proof.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    {apply fromstn0. apply fromstn0. rewrite <- contr_eq in i. assumption. }
    intros H; apply subtypePath_prop; revert H; simpl.
    intros eq; rewrite <- eq; simpl.
    set (m := n - 1).
    rewrite minusminusmmn; try reflexivity.
    apply (natlthsntoleh); unfold m.
    rewrite lemmas.minussn1non0; try assumption; exact (pr2 i).  (*TODO lemmas ? *)
  Defined.

  Lemma dualelement_lt_comp {n : nat} (i j : ⟦ n ⟧%stn)
    : i < j -> (dualelement i) > (dualelement j).
  Proof.
    intros lt.
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    { simpl. apply fromstn0. rewrite contr_eq. assumption.  }
    simpl.
    set (m := (n - 1)).
    apply minusgth0inv.
    rewrite natminusminusassoc.
    rewrite natpluscomm.
    rewrite <- natminusminusassoc.
    rewrite minusminusmmn.
    2: {unfold m. apply (natgthtogehm1 _ _ (pr2 j)). }
    apply (minusgth0 _ _ lt).
  Defined.

  Lemma dualelement_le_comp {n : nat} (i j : ⟦ n ⟧%stn)
    : i ≤ j -> (dualelement i) ≥ (dualelement j).
  Proof.
    intros le.
    destruct (natlehchoice i j) as [lt | eq]; try assumption.
    { apply natlthtoleh. apply (dualelement_lt_comp _ _ lt). }
    unfold dualelement.
    destruct (natchoice0 n) as [contr_eq | ?].
    { simpl; apply fromstn0. rewrite contr_eq. assumption.  }
    rewrite eq.
    apply isreflnatgeh.
  Defined.


  Lemma dualvalue_eq {X : UU} {n : nat} (v : ⟦ n ⟧%stn -> X) (i : ⟦ n ⟧%stn)
    : (v i) = (λ i' : ⟦ n ⟧%stn, v (dualelement i')) (dualelement i).
  Proof.
    simpl; rewrite dualelement_2x; reflexivity.
  Defined.


  Definition leading_entry_compute_dual_internal
    { n : nat } (v : Vector hq n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧%stn).
  Proof.
    destruct iter as [iter lt].
    induction iter.
    { exact nothing. }
    simpl in lt.
    assert (lt' : iter < S n). {apply (istransnatlth _ _ _ lt (natgthsnn n)). }
    destruct (isdeceqhq 0%hq (v (iter,, lt))).
    - exact (IHiter lt').
    - exact (just ((iter,, lt))).
  Defined.

  Definition leading_entry_compute_internal
    { n : nat } (v : Vector hq n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧)%stn.
  Proof.
    destruct (leading_entry_compute_dual_internal (λ i : ⟦ n ⟧%stn, v (dualelement i)) iter) as [s | ?].
    - exact (just (dualelement s)).
    - exact nothing.
  Defined.


  Definition leading_entry_compute {n : nat} (v : Vector hq n)
     := leading_entry_compute_internal v (n,, natgthsnn n).

  Definition leading_entry_dual_compute {n : nat} (v : Vector hq n)
     := leading_entry_compute_dual_internal v (n,, natgthsnn n).
  Proof.

  Lemma leading_entry_compute_eq  {n : nat} (v : Vector hq n)
  (i_1 i_2 : ⟦ n ⟧%stn)
  (e_1 : leading_entry_compute v = just i_1)
  (e_2 : leading_entry_dual_compute (λ i : ⟦ n ⟧%stn, v (dualelement i)) = just i_2)
  : i_1 = dualelement i_2.
  Proof.
    unfold leading_entry_compute, leading_entry_dual_compute in *.
    unfold leading_entry_compute_internal in *.
    destruct (leading_entry_compute_dual_internal (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))
      as [s | contr].
    2: { unfold just, nothing in e_1. contradiction (negpathsii1ii2 i_1 tt). apply pathsinv0. apply e_1. }
    assert (e_3 : (dualelement s) = i_1).
    { apply just_injectivity. exact (e_1). }
    assert (e_4 : s = i_2). { unfold just in e_2. apply ii1_injectivity in e_2. assumption. }
    rewrite <- e_3; rewrite e_4; apply idpath.
  Defined.

  Lemma leading_entry_compute_internal_eq  {n : nat} (v : Vector hq n)
    (i_1 i_2 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute_internal v (n,, natgthsnn n) = just i_1)
    (e_2 : leading_entry_compute_dual_internal (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn n) = just i_2)
    : i_1 = dualelement i_2.
  Proof.
    apply (leading_entry_compute_eq v); try assumption.
  Defined.

  Lemma leading_entry_compute_impl {n : nat} (v : Vector hq n)
    (i_1 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute_internal v (n,, natgthsnn n) = just i_1)
  : ∑ (i_2 : ⟦ n ⟧%stn),
    leading_entry_compute_dual_internal  (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn n) = just i_2.
  Proof.
    unfold leading_entry_compute, leading_entry_dual_compute in *.
    unfold leading_entry_compute_internal in *.
    destruct (leading_entry_compute_dual_internal (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))
      as [s | contr].
    2: {unfold just, nothing in e_1. contradiction (negpathsii1ii2 (i_1) tt). apply pathsinv0. apply e_1. }
    assert (e_2 : dualelement s = i_1). {apply just_injectivity. apply e_1. }
    apply dualelement_eq in e_2.
    rewrite e_2.
    use tpair. {apply s. }
    simpl. rewrite e_2. reflexivity.
  Defined.

  Definition select_pivot_row_easy_internal {n : nat} (mat : Matrix hq n n)
     (row_sep : ⟦ n ⟧%stn) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : maybe (∑ i : ⟦ n ⟧%stn, row_sep ≤ i).
  Proof.
    destruct (leading_entry_compute_dual_internal ((col mat k)) iter) as [i | ?].
    2: { exact nothing. }
    destruct (natlthorgeh (pr1 i) row_sep) as [? | gt]. {exact nothing. }
    exact (just (i,, gt )).
  Defined.

  Definition select_pivot_row_easy {n : nat} (mat : Matrix hq n n)
             (row_sep k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : maybe (⟦ n ⟧%stn).
  Proof.
    destruct (select_pivot_row_easy_internal mat row_sep k iter) as [t | ?].
    - apply (just (pr1 t)).
    - exact nothing.
  Defined.

  Lemma leading_entry_compute_dual_internal_correct1
      {n : nat} (vec : Vector hq n) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < iter -> (hqneq 0%hq (vec i)) ->
      ((leading_entry_compute_dual_internal vec iter)) != nothing.
  Proof.
    intros i H2 H4. (* TODO variable names*)
    unfold leading_entry_compute_dual_internal.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      apply negnatlthn0 in H2.
      contradiction.
    - rewrite nat_rect_step.
      destruct (isdeceqhq _ _). 2: {simpl. unfold just. apply negpathsii1ii2. }
      simpl.
      destruct (nat_eq_or_neq i (pr1_)).
      2: { simpl. apply IHpr1_.
           assert (k_lt_pr1_ : i ≤ pr1_).  {apply natlthsntoleh; assumption.  }
           apply (natleh_neq k_lt_pr1_ h).
      }
      simpl in H4.
      simpl in p.
      apply fromempty.
      rewrite p in H4.
      assert (absurd : vec i = vec (pr1_,, pr2_)).
      { apply maponpaths.
        apply subtypePath_prop.
        apply p0.
      }
      rewrite absurd in H4.
      contradiction.
  Defined.

  Lemma leading_entry_compute_dual_internal_correct2
    { n : nat } (v : Vector hq n) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : ((leading_entry_compute_dual_internal v iter)) != nothing )
    : (∑ i : ⟦ n ⟧%stn,
             just i = (leading_entry_compute_dual_internal v iter)
          ×  i < iter × (hqneq 0%hq (v i))).
  Proof.
    revert ne_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      intros.
      contradiction.
    - rewrite nat_rect_step.
      destruct (isdeceqhq _ _).
      2 : { intros ?. use tpair.
            { exact (pr1_ ,, pr2_). }
            use tpair. {simpl. reflexivity. }
            use tpair.
            - apply (natgthsnn pr1_).
            - simpl.
              assumption.
      }
      intros H.
      rewrite  p in *.
      apply IHpr1_ in H.
      destruct H as [pr1_' pr2_'].
      destruct pr2_' as [pr2_' H'].
      destruct H' as [H' H''].
      use tpair.
      {exact pr1_'. }
      use tpair. {assumption. }
      use tpair.
      { apply (istransnatlth _ _ _  H' (natgthsnn pr1_) ). }
      simpl.
      apply H''.
  Defined.

  Definition  leading_entry_compute_dual_internal_correct3
    {n : nat} (v : Vector hq n) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : (( leading_entry_compute_dual_internal v iter)) = nothing )
    : ∏ i : ⟦ n ⟧%stn, i < iter -> v i = 0%hq.
  Proof.
    intros i i_lt_iter.
    revert ne_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter pr2_].
    induction iter.
    - apply fromempty. apply negnatlthn0 in i_lt_iter; assumption.
    - rewrite nat_rect_step.
      assert (obv : iter < S n). {apply (istransnatlth _ _ _ (natgthsnn iter) pr2_). }
      destruct (isdeceqhq 0%hq (v (iter,, pr2_))).
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice i iter). {  apply natlthsntoleh; assumption. }
      + intros H.
        rewrite p in *.
        apply IHiter in H; try assumption.
      + intros ?.
        rewrite p.
        apply maponpaths.
        apply subtypePath_prop.
        apply p0. (* TODO no temp variable names *)
  Defined.

  Definition leading_entry_compute_dual_internal_correct4
    {n : nat} (v : Vector hq n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : ( ∏ i : ⟦ n ⟧%stn, i < iter -> v i = 0%hq)
   -> (leading_entry_compute_dual_internal v iter) = nothing.
  Proof.
    intros H.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter.
    - apply idpath.
    - rewrite nat_rect_step.
      assert (obv : iter < S n). {apply (istransnatgth _ _ _ (natgthsnn n) p ) . }
      destruct (isdeceqhq 0%hq (v (iter,, p))).
      + apply IHiter.
        intros.
        apply H.  {apply (istransnatgth _ _ _ (natgthsnn iter) X ) . }
      + rewrite H in n0; try assumption.
        { contradiction. }
        apply (natgthsnn iter).
  Defined.


  (* Additionally we do return the first (in order of iteration) such  non-zero element.
     TODO horrible state of this proof should be put in order. *)
  Definition leading_entry_compute_dual_internal_correct5 {n : nat} (v : Vector hq n)
    (iter : ⟦ S n ⟧%stn)
    (i : ⟦ n ⟧%stn)
    (eq : ((leading_entry_compute_dual_internal v iter)) = (just i))
    : (0%hq != v i) × (∏ i' : ⟦ n ⟧%stn, i < i' -> i' < iter -> 0%hq = (v i')).
  Proof.
    unfold leading_entry_compute_dual_internal.
    assert (ne_nothing : leading_entry_compute_dual_internal v iter != nothing).
    { destruct (maybe_choice (leading_entry_compute_dual_internal v iter)).
      - assumption.
      - rewrite eq.
        apply negpathsii1ii2. }
    revert ne_nothing.
    destruct iter as [iter p].
    induction iter.
    { simpl. intros. contradiction. }
    set (p' :=  (istransnatlth iter n (S n) p (natgthsnn n))).
    pose (@leading_entry_compute_dual_internal n v (S iter,, p) ) as H.
    destruct (@maybe_stn_choice hq n H) as [s | ?].
    2: {contradiction. }
    intros H'.
    revert H'.
    unfold leading_entry_compute_dual_internal.
    rewrite nat_rect_step.
    destruct (isdeceqhq 0%hq (v (iter,, p) )) as [z | nz].
    - destruct (maybe_choice (leading_entry_compute_dual_internal v (iter,, p'))) as [H' | contr].
      2: { revert s. revert H.
           unfold leading_entry_compute_dual_internal.
           rewrite nat_rect_step.
           destruct (isdeceqhq _ _). 2: { intros. contradiction. }
           intros.
           contradiction.
      }
      pose (first_nonzero := leading_entry_compute_dual_internal_correct2 v (iter,, p') H').
      intros ne_nothing_unf.
      assert (ne_nothing : leading_entry_compute_dual_internal v (S iter,, p) != nothing).
      { unfold leading_entry_compute_dual_internal.
        rewrite nat_rect_step.
        destruct (isdeceqhq _ _).
        2: { rewrite z in *. contradiction. }
        apply ne_nothing_unf. }
      use tpair. { pose (C2 := @leading_entry_compute_dual_internal_correct2 n v (S iter,, p) ne_nothing).
                   destruct C2 as [i' C2].
                   destruct C2 as [eq' C2].
                   unfold H in s.
                   destruct s as [s s_eq].
                   rewrite eq in eq'.
                   destruct C2 as [? neq].
                   apply (just_injectivity) in eq'.
                   rewrite <- eq'.
                   apply neq.
      }
      simpl.
      intros i' ? ?.
      destruct (natlehchoice i' iter) as [? | eq']. {assumption. }
      { apply (IHiter p'); try assumption.
        unfold H in eq.
        unfold leading_entry_compute_dual_internal in eq.
        rewrite nat_rect_step in eq.
        destruct (isdeceqhq _ _) in eq.
        2: {contradiction. }
        unfold leading_entry_compute_dual_internal.
        unfold p'.
        rewrite eq.
        reflexivity.
      }
      rewrite <- eq' in *.
      rewrite z.
      apply maponpaths.
      apply subtypePath_prop. symmetry. assumption.
    - intros ?.
      simpl.
      use tpair. {
        try assumption.
          destruct (maybe_choice (leading_entry_compute_dual_internal v (S iter,, p))) as [ne_nothing|contr_eq].
          2: { rewrite contr_eq in *.
               unfold just in eq.
               symmetry in eq. apply negpathsii1ii2 in eq.
               contradiction.
          }
          pose (C2 := @leading_entry_compute_dual_internal_correct2 n v (S iter,, p) ne_nothing).
          destruct C2 as [i' C2].
          destruct C2 as [eq' C2].
          unfold H in s.
          destruct s as [s s_eq].
          rewrite eq in eq'.
          destruct C2 as [? neq].
          apply (just_injectivity) in eq'.
          rewrite <- eq'.
          apply neq.
      }
      intros ? i'_gt_iter i_le_iter.
      apply natlthtonegnatgeh in i'_gt_iter.
      unfold leading_entry_compute_dual_internal in eq.
      rewrite nat_rect_step in eq.
      destruct (isdeceqhq  _ _) as [? | eq'] in eq.
      { contradiction. }
      apply just_injectivity in eq.
      rewrite <- eq in *.
      contradiction.
  Defined.

  Definition leading_entry_compute_internal_correct1 {n : nat} (v : Vector hq n)
    (iter : ⟦ S n ⟧%stn)
    (i : ⟦ n ⟧%stn)
    (eq : ((leading_entry_compute_internal v (n,, natgthsnn n))) = (just i))
    : (0%hq != v i) × (∏ i' : ⟦ n ⟧%stn, i' < i -> i' < iter -> 0%hq = (v i')).
  Proof.
    pose (H1 := leading_entry_compute_impl v i eq).
    destruct H1 as [i' H1].
    pose (H2 := leading_entry_compute_eq v i i' eq H1).
    unfold leading_entry_compute_internal in eq.
    pose (H := @leading_entry_compute_dual_internal_correct5 n
              (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n) (dualelement i)).
    destruct (@maybe_stn_choice hq n
              (leading_entry_compute_dual_internal
              (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))) as [? | contr_eq].
    2: { contradiction (@negpathsii1ii2 ((⟦ n ⟧)%stn) unit (i') tt).
         unfold just in H1; rewrite <- H1.
         rewrite contr_eq. reflexivity.  }
    destruct t as [t H3].
    rewrite H2 in *.
    destruct H as [H4 H5].
    { rewrite <- H2. rewrite H2. rewrite dualelement_2x. apply H1. }
    use tpair. { rewrite dualelement_2x in H4. assumption. }
    intros j gt lt.
    rewrite (H5 (dualelement j)).
    - rewrite dualelement_2x; apply idpath.
    - apply dualelement_lt_comp; (exact gt).
    - exact (pr2 (dualelement j)).
  Defined.

  Definition  leading_entry_compute_internal_correct2
    {n : nat} (v : Vector hq n) (iter : ⟦ S n ⟧%stn)
    (eq_nothing : ((leading_entry_compute_internal v iter)) = nothing )
    : ∏ i : ⟦ n ⟧%stn, (dualelement i) < iter -> v i = 0%hq.
  Proof.
    intros i i_lt_iter.
    revert eq_nothing.
    unfold leading_entry_compute_internal, leading_entry_compute_dual_internal.
    destruct iter as [iter pr2_].
    induction iter.
    - apply fromempty. apply negnatlthn0 in i_lt_iter; assumption.
    - rewrite nat_rect_step.
      assert (obv : iter < S n). {apply (istransnatlth _ _ _ (natgthsnn iter) pr2_). }
      destruct (isdeceqhq 0%hq _).
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice (dualelement i) (iter)). {  apply natlthsntoleh; assumption. }
      { intros H; rewrite p in *; apply IHiter in H; try assumption. }
      intros ?.
      rewrite p.
      apply maponpaths.
      rewrite <- (dualelement_eq i); try reflexivity.
      apply subtypePath_prop; assumption.
  Defined.

  Lemma select_pivot_eq_leading_dual
    {n : nat} (mat : Matrix hq n n) (row_sep k i : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : (select_pivot_row_easy mat row_sep k iter) = (just i))
    :
    (select_pivot_row_easy  mat row_sep k iter) =
    (leading_entry_compute_dual_internal (col mat k) iter).
  Proof.
    unfold select_pivot_row_easy, select_pivot_row_easy_internal in *.
    destruct (leading_entry_compute_dual_internal (col mat k) iter) as [s | ?].
    - destruct (natlthorgeh _ _).
      + simpl in *.
        symmetry in ne_nothing. apply negpathsii1ii2 in ne_nothing.
        contradiction.
      + simpl. reflexivity.
    - simpl.
      simpl in ne_nothing.
      symmetry in ne_nothing.
      apply negpathsii1ii2 in ne_nothing.
      contradiction.
  Defined.

  Lemma select_pivot_impl_leading_dual
      {n : nat} (mat : Matrix hq n n) (row_sep k i : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
      (k_le_i : k ≤ i)
    : (select_pivot_row_easy mat row_sep k iter) != nothing ->
      (leading_entry_compute_dual_internal (col mat k) iter) != nothing.
  Proof.
    unfold select_pivot_row_easy, select_pivot_row_easy_internal in *.
    destruct (leading_entry_compute_dual_internal (col mat k) iter) as [s | ?].
    - destruct (natlthorgeh _ _).
      + simpl in *.
        intros.
        contradiction.
      + simpl. intros. apply negpathsii1ii2.
    - simpl.
      intros. contradiction.
  Defined.


  (* Previously : easy'' *)
  Definition select_pivot_row_coprod {n : nat} (mat : Matrix hq n n)
    (row_sep : ⟦ n ⟧%stn) (k : ⟦ n ⟧%stn) :
    coprod ((∑ i: ⟦ n ⟧%stn, row_sep ≤ i × (hqneq (mat i k) 0%hq)))
           (∏ i : ⟦ n ⟧%stn, row_sep ≤ i -> mat i k = 0%hq ).
  Proof.
    pose (H := (leading_entry_compute_dual_internal_correct2 (col mat k) (n,, natgthsnn n))).
    destruct
      (maybe_choice (leading_entry_compute_dual_internal (col mat k) (n,, natgthsnn n))) as [nnone | none].
    - destruct H as [H1 H2]; try assumption.
      destruct (natlthorgeh H1 row_sep) as [? | gt].
      + apply ii2.
        set (H2' := (pr1 H2)).
        symmetry in H2'.
        pose (H3 := @leading_entry_compute_dual_internal_correct5 n (col mat k) (n,, natgthsnn n) H1 (H2')).
        destruct H3 as [H3 H4].
        intros i (*i_lt_iter*) ke_le_i.
        unfold col, transpose, flip in *.
        rewrite <- H4; try reflexivity; try assumption.
        apply (natlthlehtrans H1 row_sep i); assumption.
        apply (pr2 i).
      + apply ii1.
        use tpair. { apply H1. }
        simpl.
        use tpair. {apply gt. }
        simpl.
        unfold col, transpose, flip in *.
        destruct H2 as [? H2].
        destruct H2 as [? H2].
        destruct (isdeceqhq  (mat H1 k) 0%hq) as [contr_eq | ?].
        { rewrite contr_eq in *. contradiction. }
        assumption.
    - apply ii2.
      pose (H' := @leading_entry_compute_dual_internal_correct3).
      intros.
      rewrite <- (H' n (col mat k) (*iter*) (n,, natgthsnn n) none i); try reflexivity.
      apply (pr2 i).
  Defined.

  (* Selecting the first (checking leftmost columns first) column that has a non-zero entry ≥ the row_sep. *)
  Definition select_uncleared_column_internal {n : nat} (mat : Matrix hq n n)
    (row_sep : ⟦ n ⟧%stn) (col_iter : ⟦ S n ⟧%stn) (p : n > 0):
    ∑ j: ⟦ n ⟧%stn, coprod (j < col_iter × (∑ i: ⟦ n ⟧%stn, row_sep ≤ i × (hqneq (mat i j) 0%hq)
            × ∏ i' j' : (⟦ n ⟧)%stn, row_sep ≤ i' -> j' < j -> mat i' j' = 0%hq))
         (∏ i : ⟦ n ⟧%stn, row_sep ≤ i -> (∏ j : ⟦ n ⟧%stn, j < col_iter -> mat i j = 0%hq )).
  Proof.
    destruct col_iter as [col_iter lt].
    induction col_iter as [? | col_iter IH].
    - use tpair. { exact (0,, p). }
      right.
      intros ? ? ? contr.
      contradiction (negnatgth0n n contr).
    - assert (lt' : col_iter < S n). { simpl in lt. apply (istransnatlth _ _ _ lt (natgthsnn n)). }
      destruct (IH lt') as [m IH'].
      destruct (IH') as [IH_left | IH_right].
      + destruct IH_left as [H1 IH_left].
        destruct IH_left as [H2 H3].
        use tpair. { apply m. }
        left.
        use tpair. { apply (istransnatlth _ _ _ H1 (natgthsnn col_iter)). }
        use tpair. { simpl in lt. apply H2. } apply H3.
      + use tpair. {exact (col_iter,, lt). }
        destruct (select_pivot_row_coprod mat row_sep (col_iter,, lt)) as [nz | z].
        * left.
          (*use tpair. {apply (col_iter,, lt). }*)
          use tpair. { apply (natgthsnn col_iter). }
          use tpair. {apply nz. }
          use tpair. {apply nz. }
          use tpair. {apply nz. }
          simpl. intros i' j' ? ?.
          apply IH_right; try assumption.
        * right.
          intros i rowsep_le_i j j_lt_scoliter.
          destruct (natlehchoice j col_iter) as [? | eq].
          { apply (natlehlthtrans _ _ _ j_lt_scoliter). apply (natgthsnn col_iter). }
          { intros. apply IH_right; try assumption. }
          intros.
          rewrite <- (z i); try assumption.
          apply maponpaths.
          apply subtypePath_prop.
          simpl.
          assumption.
  Defined.

  Definition select_uncleared_column {n : nat} (mat : Matrix hq n n)
    (row_sep : ⟦ n ⟧%stn) := select_uncleared_column_internal mat row_sep (n,, natgthsnn n).

  (* Refactored to include induction on natgthorleh j k*)
  Definition gauss_clear_column_step (n : nat) (ki kj : (⟦ n ⟧%stn))
             (i : (⟦ n ⟧%stn)) (mat : Matrix hq n n) : Matrix hq n n.
  Proof.
    destruct (stn_eq_or_neq i ki) as [? | ?].
    - exact mat.
    - exact ((make_add_row_matrix ki i (- ( (mat i kj) * hqmultinv (mat ki kj)))%hq
      ** mat)).
  Defined.

  Definition gauss_clear_column_step' (n : nat) (ki kj : (⟦ n ⟧%stn))
             (i : (⟦ n ⟧%stn)) (mat : Matrix hq n n) : Matrix hq n n.
  Proof.
    destruct (stn_eq_or_neq i ki) as [? | ?].
    - exact mat.
    - exact ((gauss_add_row mat ki i (- ( (mat i kj) * hqmultinv (mat ki kj)))%hq)).
  Defined.


  Lemma gauss_clear_column_step_eq (n : nat) (ki kj : (⟦ n ⟧%stn))
             (i : (⟦ n ⟧%stn)) (mat : Matrix hq n n):
    gauss_clear_column_step n ki kj i mat = gauss_clear_column_step' n ki kj i mat.
  Proof.
    unfold gauss_clear_column_step.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq i ki) as [? | ?].
    {apply idpath. }
    rewrite add_row_mat_elementary.
    - apply idpath.
    - apply issymm_natneq.
      assumption.
  Defined.


  (* Equivalent and the right definition with iter as S n instead of n -> TODO is
     replacing uses of the other one with this one *)
  (* [gauss_clear_column' mat k p _]:
    clear column [k] in rows [0 ≤ i < p],
    from row 0 up to row p (though order doesn’t matter. *)
  (* TODO: rename to [gauss_clear_column_segment]
     TODO: refactor to use a chosen/given pivot, not always diagonal *)
  (* Temporarily renamed to old ! To try to make all lemmas work on this one. *)
  Definition gauss_clear_column_old { n : nat } (mat : Matrix hq n n)
      (k_i k_j : (⟦ n ⟧%stn)) (p : ⟦ S n ⟧%stn)
    : Matrix hq n n.
  Proof.
    destruct p as [p lt_p].
    induction p as [ | p gauss_clear_column_IH ].
    { exact mat. }  (* not applying the step since surely 0 ≤ k *)
    destruct (natgthorleh p k_i).
    - refine (gauss_clear_column_step n k_i k_j (p,, lt_p) (gauss_clear_column_IH _)).
      apply (istransnatlth _ _ _ (natlthnsn p) lt_p).
    - exact mat.
  Defined.

  (* A third version that more closely follows the matrix construction -
     we break at iter ≤ k. This however is already done in gauss_clear_column_step. *)
  Definition gauss_clear_column'' { n : nat }
    (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn))  (iter : ⟦ S n ⟧%stn) : Matrix hq n n.
  Proof.
    (*revert mat.*)
    destruct iter as [pr1_ pr2_].
    induction pr1_ as [ | m gauss_clear_column_IH ].
    {exact mat. }  (* not applying the step since surely 0 ≤ k *)
    set (piv := mat k_i k_j).
    destruct (natgthorleh m k_i).
    2 : {exact mat. }
    assert (m_lt_n : m < S n). {  apply (istransnatlth _ _ _ (natlthnsn m) pr2_) . }
    exact (gauss_clear_column_step n k_i k_j (m,, pr2_) (gauss_clear_column_IH m_lt_n)).
  Defined.

  Lemma gauss_clear_column_as_left_matrix  { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn)) : Matrix hq n n.
  Proof.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - exact (@identity_matrix hq n) (*mat*).
    - assert (pr2_' : pr1_ < n). { apply pr2_. }
      assert (pr2_'' : pr1_ < S n). { apply (istransnatlth _ _ _ (natlthnsn pr1_ ) pr2_ ). }
       destruct (natgthorleh pr1_ k_i).
      + exact (make_add_row_matrix k_i  (pr1_,, pr2_) (- ((mat (pr1_,,pr2_) k_j) * hqmultinv (mat k_i k_j)))%hq
              ** (IHpr1_ pr2_'')).
      + exact (@identity_matrix hq n ** (IHpr1_ pr2_'' )). (* TODO break completely? *)
  Defined.

  (* TODO generalize to rigs *)
  Lemma gauss_add_row_inv0 {n : nat} (mat : Matrix hq n n) (i j: ⟦ n ⟧%stn) (s : hq)
    : ∏ (k : ⟦ n ⟧%stn), j ≠ k -> gauss_add_row  mat i j s k = mat k.
  Proof.
    intros k j_ne_k.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j].
    - rewrite k_eq_j in j_ne_k.
      apply isirrefl_natneq in j_ne_k.
      apply fromempty; assumption.
    - simpl.
      reflexivity.
  Defined.

  Lemma gauss_add_row_inv1 {n : nat} (mat : Matrix hq n n) (i j: ⟦ n ⟧%stn) (s : hq)
    : ∏ (k : ⟦ n ⟧%stn), (mat i = const_vec 0%hq) -> gauss_add_row mat i j s = mat.
  Proof.
    intros k eq0.
    apply funextfun; intros i'; apply funextfun; intros j'.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j'].
    - simpl.
      rewrite <- i'_eq_j'.
      rewrite eq0.
      unfold const_vec ; simpl.
      rewrite (@ringmultx0 hq).
      rewrite (@rigrunax1 hq).
      reflexivity.
    - simpl.
      reflexivity.
  Defined.

  Lemma gauss_add_row_inv2 {n : nat} (mat : Matrix hq n n) (i_1 i_2: ⟦ n ⟧%stn) (s : hq)
    : ∏ (j_1: ⟦ n ⟧%stn), (mat i_1 j_1 = 0%hq) -> (gauss_add_row mat i_1 i_2 s) i_2 j_1 = mat i_2 j_1.
  Proof.
    intros j_1 eq0.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j'].
    - simpl.
      try rewrite <- i'_eq_j'.
      rewrite eq0.
      rewrite (@ringmultx0 hq).
      rewrite (@rigrunax1 hq).
      reflexivity.
    - simpl.
      reflexivity.
  Defined.

  (* Restating a similar lemma for the regular version of this operation, in order to prove their
     equivalence *)
  Lemma gauss_clear_column_as_left_matrix_inv0  { n : nat } (pr1_: nat) (pr2_ : pr1_ < S n)
        (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn)) (i : ⟦ n ⟧%stn): pr1_  ≤ i ->
        ((gauss_clear_column_as_left_matrix (pr1_,, pr2_) mat k_i k_j) ** mat) i = mat i.
  Proof.
    induction pr1_.
    - simpl. intros. unfold gauss_clear_column_as_left_matrix. simpl.
      rewrite matlunax2. reflexivity.
    - intros.
      unfold gauss_clear_column_as_left_matrix.
      rewrite nat_rect_step.
      destruct (natgthorleh pr1_ k_i).
      + unfold gauss_clear_column_as_left_matrix in IHpr1_.
        assert (pr2_': pr1_ < S n). {apply (istransnatlth _ _ _ (natgthsnn pr1_) pr2_). }
        ( rewrite <- (IHpr1_ pr2_')).
        rewrite matrix_mult_assoc.
        2 : { apply natlehtolehs in X; assumption. }
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq.  apply natgthtoneq in h. assumption. }
        rewrite IHpr1_. 2 : {apply natlehsntolth  in X. apply natlthtoleh in X. assumption. }
        set (x := nat_rect _ _ _ _).
        rewrite gauss_add_row_inv0.
        2: {apply snlehtotonlt in X.
            - apply issymm_natneq. apply natgthtoneq; assumption.
            - apply natneq0togth0.
              destruct (natchoice0 pr1_).
              + rewrite <- p in h.
                apply negnatgth0n in h.
                contradiction.
              + apply natgthtoneq.
                assumption.
        }
        unfold x.
        rewrite IHpr1_.
        { apply idpath. }
        apply natlehsntolth in X. apply natlthtoleh in X. assumption.
      + rewrite matlunax2.
        assert (pr2_': pr1_ < S n). {apply (istransnatlth _ _ _ (natgthsnn pr1_) pr2_). }
        unfold gauss_clear_column_as_left_matrix in IHpr1_.
        rewrite <- (IHpr1_ pr2_').
        2 : {apply (istransnatleh (natgehsnn pr1_) X). }
        set (x := nat_rect _ _ _).
        unfold matrix_mult.
        apply funextfun; intros q.
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths_2.
        apply maponpaths.
        apply proofirrelevance.
        apply propproperty.
  Defined.

  (*TODO why are pr1_ pr2_ separate ?  *)
  Lemma gauss_clear_column_as_left_matrix_inv1  { n : nat } (pr1_: nat) (pr2_ : pr1_ < S n)
        (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn)) (i : ⟦ n ⟧%stn) (i_leh_k : i ≤ k_i):
        (gauss_clear_column_as_left_matrix (pr1_,, pr2_) mat k_i k_j ** mat) i = mat i.
  Proof.
    induction pr1_.
    - simpl. simpl. unfold gauss_clear_column_as_left_matrix.
      simpl. rewrite matlunax2. reflexivity.
    - intros.
      unfold gauss_clear_column_as_left_matrix.
      rewrite nat_rect_step.
      destruct (natgthorleh pr1_ k_i).
      + assert (pr2_': pr1_ < S n). {apply (istransnatlth _ _ _ (natgthsnn pr1_) pr2_). }
        ( rewrite <- (IHpr1_ pr2_')).
        unfold gauss_clear_column_as_left_matrix in *.
        rewrite IHpr1_.
        rewrite matrix_mult_assoc.
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq. apply natgthtoneq. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply natgthtoneq. apply (natlehlthtrans _ _ _  i_leh_k h).  }
        unfold gauss_clear_column_as_left_matrix in IHpr1_.
        rewrite IHpr1_.
        reflexivity.
      + rewrite matlunax2.
        unfold gauss_clear_column_as_left_matrix in IHpr1_.
        rewrite   IHpr1_.
        reflexivity.
  Defined.

  Lemma clear_column_matrix_invertible  { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn))
        : (* (@matrix_inverse hq n mat) *)
          @matrix_inverse hq _ (gauss_clear_column_as_left_matrix iter mat k_i k_j).
  Proof.
    set (pre := gauss_clear_column_as_left_matrix iter mat k_i k_j).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - unfold pre.  simpl. apply identity_matrix_is_inv.
    - unfold pre.
      rewrite nat_rect_step.
      destruct (natgthorleh pr1_ k_i) as [gt | ?].
      2: { apply inv_matrix_prod_is_inv.
           - apply identity_matrix_is_inv.
           - apply IHpr1_. }
      apply inv_matrix_prod_is_inv.
      { apply add_row_matrix_is_inv.
       - apply natlthtoneq; assumption.
       - apply (stn_implies_ngt0 k_i).
      }
      apply IHpr1_.
  Defined.


  (* Move all invs up here ? *)
  Lemma gauss_clear_column_step_inv4
     (n : nat) (k_i k_j : (⟦ n ⟧%stn))
         (j : (⟦ n ⟧%stn)) (mat : Matrix hq n n)
         (p : j = k_i) : (gauss_clear_column_step n k_i k_j j mat) = mat.
  Proof.
    unfold gauss_clear_column_step.
    destruct (stn_eq_or_neq j k_i) as [j_gt_k | j_leq_k].
    {apply idpath. }
    unfold gauss_add_row.
    apply funextfun; intros i.
    apply funextfun; intros ?.
    destruct (stn_eq_or_neq i j) as [eq | neq].
    - simpl.
      rewrite p in *.
      apply isirrefl_natneq in j_leq_k.
      contradiction.
    - rewrite p in j_leq_k.
      apply isirrefl_natneq in j_leq_k.
      contradiction.
  Defined.


  Definition gauss_clear_row
             { n : nat }
             (mat : Matrix hq n n)
             (row : (⟦ n ⟧%stn))
    : Matrix hq n n.
  Proof.
    destruct (natchoice0 n) as [contr_eq | p]. {apply fromstn0. rewrite contr_eq; assumption. }
    destruct (pr2 (select_uncleared_column mat row p)) as [some | none].
    2 : {exact mat. }
    refine (gauss_clear_column_old _  row (pr1 (select_uncleared_column mat row p)) (n ,, natlthnsn n )).
    refine (gauss_switch_row mat row (pr1 (pr2 some))).
  Defined.

  Definition gauss_clear_row_as_left_matrix
             { n : nat }
             (mat : Matrix hq n n)
             (row : (⟦ n ⟧%stn))
    : Matrix hq n n.
  Proof.
    destruct (natchoice0 n) as [contr_eq | p]. {apply fromstn0. rewrite contr_eq; assumption. }
    destruct (pr2 (select_uncleared_column mat row p)) as [some | none].
    2 : {exact (@identity_matrix hq n). }
    set (mat_by_normal_op := (gauss_switch_row mat row (pr1 (pr2 some)))).
    refine ((gauss_clear_column_as_left_matrix (n,, natgthsnn n) mat_by_normal_op row
                                              (pr1 (select_uncleared_column mat row p))) ** _).
    refine (make_gauss_switch_row_matrix n row (pr1 (pr2 some))).
  Defined.

  Lemma clear_row_matrix_invertible
  { n : nat } (mat : Matrix hq n n) (r: (⟦ n ⟧%stn))
  :
  @matrix_inverse hq _ (gauss_clear_row_as_left_matrix mat r).
  Proof.
    unfold gauss_clear_row_as_left_matrix.
    destruct (natchoice0 n) as [contr_eq | p]. {apply fromstn0. rewrite contr_eq; assumption. }
    destruct (pr2 (select_uncleared_column mat r p)).
    2: {apply identity_matrix_is_inv. }
    apply inv_matrix_prod_is_inv.
    - apply clear_column_matrix_invertible.
    - apply switch_row_matrix_is_inv.
  Defined.

  Definition gauss_clear_rows_up_to_internal { n : nat }
             (mat : Matrix hq n n)
             (p : n > 0) (* Remove p when gcc is refactored *)
             (row_sep : (⟦ S n ⟧%stn))
    : (Matrix hq n n).
  Proof.
    destruct row_sep as [row_sep row_sep_lt_n].
    induction row_sep as [ | row_sep gauss_clear_earlier_rows].
    { exact mat. }
    assert (lt : row_sep < S n). {apply (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ). }
    refine (gauss_clear_row _ (row_sep,, row_sep_lt_n)).
    exact (gauss_clear_earlier_rows lt).
  Defined.

  Definition gauss_clear_rows_up_to { n : nat }
             (mat : Matrix hq n n)
             (p : n > 0) (* Remove p when gcc is refactored *)
             (row_sep : (⟦ S n ⟧%stn))
    := gauss_clear_rows_up_to_internal mat p row_sep.

  (* invertible matrix, such that left-multiplication by this
     corresponds to [gauss_clear_columns_up_to]  *)
  Lemma clear_rows_up_to_as_left_matrix_internal
      { n : nat }
      (mat : Matrix hq n n)
      (p : n > 0) (* Remove p when gcc is refactored *)
      (row_sep : (⟦ S n ⟧%stn))
    : (Matrix hq n n).
  Proof.
    destruct row_sep as [row_sep row_sep_lt_n].
    induction row_sep as [ | row_sep gauss_clear_earlier_rows].
    { exact (@identity_matrix hq n). }
    assert (lt : row_sep < S n). {apply (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ). }
    set (mat_by_normal_op :=  (gauss_clear_rows_up_to_internal mat p (row_sep,, lt))).
    refine (gauss_clear_row_as_left_matrix mat_by_normal_op (row_sep,, row_sep_lt_n) ** _).
    exact (gauss_clear_earlier_rows lt).
  Defined.

  Lemma clear_rows_up_to_as_left_matrix  { n : nat } (mat : Matrix hq n n) (p : n > 0) (* Remove p when gcc is refactored *)
        (k : (⟦ S n ⟧%stn)) : Matrix hq n n.
  Proof.
    exact (clear_rows_up_to_as_left_matrix_internal mat p k).
  Defined.

  (* the deining property of [clear_columns_up_to_as_left_matrix]
     - proven later, after the equivalence of clear columns procedure - TODO remove / move  *)
  (*Lemma clear_columns_up_to_as_left_matrix_eq {n : nat} (p : ⟦ S n ⟧%stn) (* Remove p when gcc is refactored *)
        (H : n > 0) (*TODO remove *) (k : (⟦ n ⟧%stn)) (mat : Matrix hq n n)
    : ((clear_columns_up_to_as_left_matrix mat H p) ** mat) = (pr1 (gauss_clear_columns_up_to mat H p )).
  Proof.
    intros.
    unfold clear_columns_up_to_as_left_matrix,
      gauss_clear_columns_up_to.
    destruct p as [p p_lt_sn].
    induction p.
    - apply matlunax2.
    -
  Abort. (* We need gcc as matrix = gcc here, but it's stated below. *)*)

  Lemma clear_rows_up_to_matrix_invertible {n : nat} (p : ⟦ S n ⟧%stn)
    (H : n > 0) (k : (⟦ n ⟧%stn)) (mat : Matrix hq n n)
    : @matrix_inverse hq _  (clear_rows_up_to_as_left_matrix mat H p).
  Proof.
    unfold clear_rows_up_to_as_left_matrix.
    set (pre := gauss_clear_column_as_left_matrix p mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct p as [pr1_ pr2_].
    induction pr1_ as [| pr1_ IH].
    - simpl. apply identity_matrix_is_inv.
    - unfold clear_rows_up_to_as_left_matrix,
             clear_rows_up_to_as_left_matrix_internal.
      rewrite nat_rect_step.
      apply inv_matrix_prod_is_inv.
      + apply clear_row_matrix_invertible; try assumption.
      + apply IH.
  Defined.

  (* A variant of gccut that does not switch rows
     This will be used to find a witness to non-invertibility for lower triangular input matrices.  *)
  Definition gauss_clear_columns_up_to_no_switch { n : nat } (p : n > 0) (* Remove p when gcc is refactored *)
             (k : (⟦ S n ⟧%stn))
             (mat : Matrix hq n n) : Matrix hq n n.
  Proof.
    destruct k as [k lt_k_n].
    induction k as [ | k' gauss_clear_earlier_columns].
    - exact mat.
    - assert (lt : k' < S n). {apply (istransnatlth _ _ _ (natgthsnn k') lt_k_n ). }
      set (piv := k').
      destruct (isdeceqhq (mat (k',, lt_k_n) (k',, lt_k_n)) 0%hq).
      + refine ( (gauss_clear_earlier_columns _ )).
        exact lt.
      + refine (gauss_clear_column_old _   (k' ,, lt_k_n)  (k' ,, lt_k_n) (n ,, natlthnsn n ) ).
        refine ( (gauss_clear_earlier_columns _ )).
        exact lt.
  Defined.


  Lemma clear_columns_up_to_no_switch_as_left_matrix_internal { n : nat } (p : n > 0) (* Remove p when gcc is refactored *)
    (k : (⟦ S n ⟧%stn)) (mat : Matrix hq n n) :  Matrix hq n n.
  Proof.
    destruct k as [k lt_k_n].
    induction k as [ | k' gauss_clear_earlier_columns].
    { exact (@identity_matrix hq n). }
    assert (lt : k' < S n). {apply (istransnatlth _ _ _ (natgthsnn k') lt_k_n ). }
    set (mat_by_normal_op :=  (gauss_clear_columns_up_to_no_switch p (k' ,, lt) mat )).
    set (piv :=  make_stn n k' lt_k_n).
    destruct (isdeceqhq (mat (k',, lt_k_n) (k',, lt_k_n)) 0%hq).
    - refine ( ( (gauss_clear_earlier_columns _ ))).
      exact lt.
    - refine ((gauss_clear_column_as_left_matrix  (n,, natlthnsn n) _ (k' ,, lt_k_n) (k' ,, lt_k_n)) ** _ ).
      + exact ( mat_by_normal_op ).
      + refine ( (gauss_clear_earlier_columns _)).
        assumption.
  Defined.

  Lemma clear_columns_up_to_no_switch_as_left_matrix  { n : nat } (p : n > 0)
    (k : (⟦ S n ⟧%stn)) (mat : Matrix hq n n) : Matrix hq n n.
  Proof.
    exact ((clear_columns_up_to_no_switch_as_left_matrix_internal p k mat)).
  Defined.

  Lemma clear_columns_up_to_matrix_no_switch_invertible {n : nat} (p : ⟦ S n ⟧%stn) (* Remove p when gcc is refactored *)
    (H : n > 0) (k : (⟦ n ⟧%stn)) (mat : Matrix hq n n)
    : (* (@matrix_inverse hq _ mat) -> *)
       @matrix_inverse hq _  (clear_columns_up_to_no_switch_as_left_matrix H p mat).
  Proof.
    unfold clear_columns_up_to_no_switch_as_left_matrix.
    set (pre := gauss_clear_column_as_left_matrix p mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct p as [pr1_ pr2_].
    induction pr1_.
    - simpl. apply identity_matrix_is_inv.
    - unfold clear_columns_up_to_no_switch_as_left_matrix_internal.
      rewrite nat_rect_step.
      destruct (isdeceqhq _ _).
      {apply IHpr1_. }
      refine (inv_matrix_prod_is_inv _ _ _ _ ).
      { apply clear_column_matrix_invertible . }
      apply IHpr1_.
  Defined.


  (* Inputting a matrix and transforming it into an upper-triangular matrix by
     elementary matrix operations or equivalent *)
  Definition gauss_clear_all_row_segments { n : nat } (mat : Matrix hq n n) : Matrix hq n n.
  Proof.
    destruct (natchoice0 n). {exact mat. }
    refine ((gauss_clear_rows_up_to  mat _ (n,,_))).
    - assumption.
    - exact (natgthsnn n).
  Defined.

  Definition gauss_clear_all_column_segments_by_left_mult { n : nat } (mat : Matrix hq n n) : Matrix hq n n.
  Proof.
    destruct (natchoice0 n). {exact mat. }
    refine (clear_rows_up_to_as_left_matrix mat  _ (n,,_) ).
    - assumption.
    - exact (natgthsnn n).
  Defined.

  (* The clear column step operation does clear the target entry (mat (k j)) *)
  Lemma gauss_clear_column_step_inv1 (n : nat) (k_i k_j : (⟦ n ⟧%stn))
        (j : (⟦ n ⟧%stn)) (mat : Matrix hq n n)  (p_1 : mat k_i k_j != 0%hq)
        (p_2 : j ≠ k_i) :
    (gauss_clear_column_step n k_i k_j j mat) j k_j = 0%hq.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (stn_eq_or_neq j k_i) as [p | ?].
    {rewrite p in p_2. apply isirrefl_natneq in p_2. contradiction. }
    unfold make_add_row_matrix.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    assert (p_3 : n > 0). { apply (stn_implies_ngt0 k_i). }
    set (f := λ i, _).
    rewrite (@two_pulse_function_sums_to_points_rig' hq n _ p_3 k_i j). (*TODO fix ugly signature *)
    - destruct (stn_eq_or_neq k_i j) as [k_eq_j | k_neq_j].
      + rewrite k_eq_j.
        replace (f j) with 0%hq.
        { rewrite (@riglunax1 hq); reflexivity. }
        unfold f, pointwise, identity_matrix, const_vec.
        rewrite stn_neq_or_neq_refl; rewrite coprod_rect_compute_1.
        rewrite stn_neq_or_neq_refl; rewrite coprod_rect_compute_1.
        rewrite k_eq_j.
        rewrite stn_neq_or_neq_refl; rewrite coprod_rect_compute_1.
        rewrite (@rigrunax2 hq).
        rewrite <- k_eq_j.
        rewrite (hqisrinvmultinv (mat k_i k_j)). 2 : {exact p_1. }
        rewrite (@ringrinvax1 hq).
        rewrite (@rigmult0x hq).
        reflexivity.
      + destruct (stn_eq_or_neq j j) as [? | absurd].
        2: { apply fromempty; clear f. apply isirrefl_natneq in absurd. contradiction. }
        unfold f.
        destruct (stn_eq_or_neq j j) as [? | absurd].
        2: { apply fromempty; clear f. apply isirrefl_natneq in absurd. contradiction. }
        simpl.
        unfold pointwise.
        apply issymm_natneq in k_neq_j.
        pose (eq := @id_mat_ii hq n k_i).
        etrans. {apply maponpaths. do 2 apply maponpaths_2. rewrite id_mat_ii. apply idpath. }
        etrans. {do 2 apply maponpaths_2; do 2 apply maponpaths; rewrite id_mat_ii. apply idpath. }
        etrans. {apply maponpaths. apply maponpaths_2. apply maponpaths. rewrite id_mat_ij.
                   2: { apply issymm_natneq. exact (k_neq_j). } apply idpath. }
        etrans. {do 3 apply maponpaths_2. rewrite id_mat_ij; try assumption; apply idpath. }
        etrans. {do 2 apply maponpaths_2.
                 rewrite (@rigrunax2 hq), (@riglunax1 hq).
                 reflexivity. }
        apply issymm_natneq in k_neq_j.
        unfold const_vec.
        etrans. { apply maponpaths.  reflexivity. }
        rewrite (@rigmultx0 hq).
        etrans.
          {apply maponpaths. rewrite (@rigrunax1 hq).
          rewrite (@riglunax2 hq). reflexivity. }
        etrans.
          { apply maponpaths_2.
            rewrite <- (@ringrmultminus hq).
            rewrite hqmultassoc.
            rewrite (@ringlmultminus hq).
            rewrite (hqmultcomm _ (mat k_i k_j) ).
            rewrite (hqisrinvmultinv (mat k_i k_j)).
            2 : {exact p_1. }
            rewrite hqmultcomm.
            rewrite (@ringlmultminus hq).
            rewrite (@riglunax2 hq).
           reflexivity. }
      apply hqlminus.
    - apply issymm_natneq. assumption.  (* TODO move earlier in signature of pf sums to p *)
    - intros i i_neq_k i_neq_j; unfold f.
      rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
      unfold identity_matrix, pointwise.
      apply issymm_natneq in i_neq_k.
      apply issymm_natneq in i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_k), coprod_rect_compute_2.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      etrans. {apply maponpaths_2. rewrite hqplusl0. reflexivity. }
      rewrite (rigmultx0 hq (_)%hq).
      apply rigmult0x.
  Admitted.
  (*Defined.*) (* TOOD really slow proof! Replace admitted by defined when sped up. *)

    (* The clear column step operation only changes the target row*)
  Lemma gauss_clear_column_step_inv2 (n : nat) (k_i k_j : (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix hq n n) (j : ⟦ n ⟧%stn)
        (p : r ≠ j)  : (gauss_clear_column_step n k_i k_j j mat) r = mat r.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (stn_eq_or_neq j k_i) as [? | ?].
    {apply idpath. }
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_add_row_matrix, pointwise.
    assert (p'' : n > 0). { apply stn_implies_ngt0. assumption. }
    apply funextfun. intros q.
    destruct (stn_eq_or_neq r j ) as [r_eq_j | r_neq_j].
    { simpl. rewrite r_eq_j in p. apply isirrefl_natneq in p; contradiction. }
    simpl.
    rewrite (@pulse_function_sums_to_point_rig'' hq n _ (stn_implies_ngt0 j ) r ).
    - rewrite (id_mat_ii).
      apply (@riglunax2 hq).
    - unfold is_pulse_function. (* TODO use just one of these pulse defs *)
      intros x r_neq_x.
      set (lft := identity_matrix r x).
      change (lft * mat x q)%ring with (@identity_matrix hq n r x * mat x q)%hq. (*Why need this and why slow? *)
      rewrite (id_mat_ij r x r_neq_x).
      apply rigmult0x.
  Defined.

  Lemma gauss_clear_column_step_inv2' (n : nat) (k_i k_j : (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix hq n n) (j j' : ⟦ n ⟧%stn)
        (p : r ≠ j) : (gauss_clear_column_step n k_i k_j j mat) r j' = mat r j'.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (stn_eq_or_neq j k_i) as [h | ?].
    {apply idpath. }
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_add_row_matrix.
    assert (p' : n > 0). { apply stn_implies_ngt0. assumption. }
    set (f := λ i : (⟦ n ⟧%stn), _).
    (*TODO proof would be tightened up without this inline assert *)
    assert (b : (*Σ f*)   iterop_fun 0%rig op1  f = f r ). {
      apply (@pulse_function_sums_to_point_rig'' hq n _ (stn_implies_ngt0 j) r).
      unfold is_pulse_function.
      intros q r_neq_k.
      unfold f.
      destruct (stn_eq_or_neq r j) as [r_eq_q | r_neq_q].
      - rewrite r_eq_q in p. (*TODO*)
        apply (isirrefl_natneq) in p.
        contradiction.
      - unfold identity_matrix.
        rewrite coprod_rect_compute_2.
        rewrite (stn_eq_or_neq_right r_neq_k), coprod_rect_compute_2.
        apply rigmult0x.
    }
    unfold pointwise.
    rewrite b.
    unfold f.
    rewrite (stn_eq_or_neq_right p), coprod_rect_compute_2.
    unfold identity_matrix.
    rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
    apply (@riglunax2 hq).
  Defined.

  Lemma gauss_clear_column_step_inv3
     (n : nat) (k_i k_j : (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix hq n n) (j j' : ⟦ n ⟧%stn)
         (p : r < j) : (gauss_clear_column_step n k_i k_j j mat) r j' = mat r j'.
  Proof.
    assert (p': r ≠ j). {apply issymm_natneq.  apply natgthtoneq. assumption. }
    rewrite (gauss_clear_column_step_inv2 n k_i k_j r mat j  p').
    apply idpath.
  Defined.



  (* Proving mat r  is unchanged after column clearance   if r > n'. *)
  Lemma gauss_clear_column_inv0'
        { n : nat } (k_i k_j : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (mat : Matrix hq n n) (r : ⟦ n ⟧%stn)
    (r_gt_n' : r ≥ iter) : (gauss_clear_column_old  mat k_i k_j iter) r = mat r.
  Proof.
    destruct iter as [n' p].
    induction n'.
    - simpl.
      reflexivity.
    - unfold gauss_clear_column_old.
      rewrite nat_rect_step.
      destruct (natgthorleh n' k_i). 2: { apply idpath. }
      set (sn' := make_stn n n' p).
      assert (q : n' < n). {apply p. }
      assert (q': r > n'). {apply r_gt_n'. }
      rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _).
      { unfold gauss_clear_column_old, gauss_clear_column_step.
        - unfold gauss_clear_column_old in IHn'.
          apply IHn'.
          apply natgthtogeh; assumption.
      }
      unfold gauss_clear_column_step.
      unfold gauss_clear_column_old in *.
      rewrite gauss_add_row_inv0. 2:{ apply natlthtoneq. assumption. }
      rewrite IHn'.
      { apply idpath. }
      apply natgthtogeh.
      apply r_gt_n'.
  Defined.


  (* if the target row r ≤  the pivot row k,
     mat r is not changed bybac the clearing procedure. *)
  Lemma gauss_clear_column_inv3
        { n : nat } (k_i k_j r : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (p' : r ≤ k_i)
        (mat : Matrix hq n n) (*(kk_ne_0 : mat k k != 0%hq)*) :
    ((gauss_clear_column_old mat k_i k_j iter) r = mat r).
  Proof.
    destruct iter as [n' p].
    induction n'.
    { unfold gauss_clear_column_old. simpl. reflexivity. }
    simpl.
    unfold gauss_clear_column_old.
    apply funextfun. intros q.
    rewrite nat_rect_step.
    destruct (natgthorleh _ _); try reflexivity.
    rewrite gauss_clear_column_step_inv3.
    2 : {refine (natgthgehtrans _ _ _ h _); assumption. }
    unfold gauss_clear_column_old in IHn'.
    rewrite IHn'.
    reflexivity.
  Defined.


  (* Proving the column clearing procedure works on one row at a time *)
  Lemma gauss_clear_column_inv0
        { n : nat } (k_i k_j : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn) (mat : Matrix hq n n) : ∏ r : (⟦ n ⟧%stn),
        r < iter ->
        k_i < r ->
        ((gauss_clear_column_old  mat k_i k_j iter) r
         = (gauss_clear_column_step' n k_i k_j r mat) r).
  Proof.
    destruct iter as [n' p].
    revert mat k_i k_j p.
    induction n'.
    - intros mat k_i k_j p r r_le_0.
      contradiction (negnatgth0n r r_le_0).
    - intros mat k_i k_j p r r_le_sn k_le_r.
      set (sn' := make_stn n (n') p).
      assert (p' : n' < S n). {apply (istransnatlth _ _ _ (natgthsnn n') p). }
      set (IHnp := IHn'  mat k_i k_j p').
      destruct (natlehchoice r (n')) as [? | eq]. {assumption. }
      + assert (follows : r ≤ n'). { apply natlthtoleh in h. assumption. }
        unfold gauss_clear_column_old.
        rewrite nat_rect_step.
        unfold gauss_clear_column_old in IHnp.
        destruct (natgthorleh _ _).
        2: { assert (absurd : n' ≤ r).
             { apply natgthtogeh in k_le_r.
               apply (istransnatleh h0 k_le_r). }
               apply fromempty.
               apply natgehtonegnatlth in absurd.
               contradiction.
        }
        rewrite (gauss_clear_column_step_inv2).
        2 : { apply natgthtoneq in h. apply issymm_natneq. apply h. }
        etrans.
        { assert (eq : p' =  (istransnatlth n' (S n') (S n) (natlthnsn n') p)).
          apply proofirrelevance.
          apply propproperty.
          rewrite <- eq.
          apply idpath.
        }
        rewrite <- IHnp; try reflexivity; try assumption.
      + rewrite <- gauss_clear_column_step_eq.
        rewrite gauss_clear_column_step_eq.
        simpl.
        unfold gauss_clear_column_old.
        rewrite nat_rect_step.
        try do 2 rewrite gauss_clear_column_step_eq.
        unfold gauss_clear_column_step'.
        set (sn'' := (make_stn n ( n') p)).
        set (p'' := istransnatlth _ _ _ _ _).
        destruct (natgthorleh _ _).
        2: { unfold gauss_clear_column_step.
             destruct (stn_eq_or_neq _ _); try reflexivity.
              assert (absurd : n' ≤ r).
             { apply natgthtogeh in k_le_r.
               rewrite eq; apply isreflnatgeh. }
             rewrite <- eq in *.
             apply natlehneggth in h.
             contradiction.
        }
        replace   (gauss_clear_column_step n k_i k_j sn'' _ r)
          with (gauss_clear_column_step n k_i k_j sn'' mat r).
        { replace sn'' with r.
          { rewrite gauss_clear_column_step_eq. apply idpath. }
          rewrite (@subtypePath_prop _ _ r (n',, p)). {reflexivity. }
          apply eq.
        }
        assert (step1 : (gauss_clear_column_old mat k_i k_j (n',, p'')) r = mat r).
        { rewrite gauss_clear_column_inv0'.
          - apply idpath.
          - rewrite eq.
            apply natlthnsn. }
        assert (commute :
                  gauss_clear_column_step n k_i k_j sn'' (gauss_clear_column_old mat k_i k_j  (n',, p'')) r
               =  gauss_clear_column_old (gauss_clear_column_step n k_i k_j sn'' mat) k_i k_j (n',, p'')  r).
        { unfold gauss_clear_column_step.
          destruct (stn_eq_or_neq _ _).
          {reflexivity. }
          unfold make_add_row_matrix.
          apply funextfun. intros x.
          rewrite matrix_mult_eq; unfold matrix_mult_unf, pointwise.
          rewrite gauss_clear_column_inv0'.
          2 : { unfold sn''. apply (natlthnsn). }
          assert (eq' : r = sn'').
          { rewrite (@subtypePath_prop _ _ r (n',, p)). {reflexivity. } apply eq. }
          rewrite <- eq'.
          rewrite (stn_neq_or_neq_refl).
          simpl.
          apply pathsinv0.
          etrans.
          { rewrite (gauss_clear_column_inv0').
            - apply idpath.
            - rewrite eq.
              apply natlthnsn.
          }
          unfold pointwise.
          unfold const_vec, pointwise.
          rewrite matrix_mult_eq; unfold matrix_mult_unf.
          rewrite stn_neq_or_neq_refl; simpl.
          unfold const_vec, pointwise.
          apply maponpaths.
          apply funextfun. intros y.
          destruct (stn_eq_or_neq k_i y) as [eq'' | ?].
          - rewrite <- eq''.
            rewrite id_mat_ii.
            do 2 rewrite (@rigrunax2 hq).
            rewrite gauss_clear_column_inv3.
            + apply idpath.
            + apply isreflnatleh.
          - unfold pointwise, const_vec.
            unfold identity_matrix.
            rewrite (stn_eq_or_neq_right h1); simpl.
            do 2 rewrite (@rigmultx0 hq); rewrite (@rigrunax1 hq).
            destruct (stn_eq_or_neq r y) as [eq'' | ?].
            * rewrite eq''. simpl.
              rewrite gauss_clear_column_inv0'.
              { apply idpath. }
              rewrite <- eq''.
              rewrite eq.
              apply natgthsnn.
            * simpl.
              do 2 rewrite (@rigmult0x hq).
              apply idpath.
        }
        unfold gauss_clear_column_old in commute.
        set (f := @gauss_clear_column_inv0').
        unfold gauss_clear_column_old in f.
        rewrite commute.
        rewrite gauss_clear_column_step_eq.
        rewrite <- gauss_clear_column_step_eq.
        rewrite <- (f n k_i k_j ( n' ,, p'')). {reflexivity. }
        rewrite eq.
        apply isreflnatleh.
  Admitted.


  (* Proving mat r  is unchanged after column clearance   if r > n'. *)
  Lemma gauss_clear_column_inv0''
        { n : nat } (k_i k_j : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (mat : Matrix hq n n) (r : ⟦ n ⟧%stn)
    (r_gt_n' : r ≥ iter) : (gauss_clear_column_old mat k_i k_j iter) r = mat r.
  Proof.
    destruct iter as [n' p].
    induction n'.
    - simpl.
      reflexivity.
    - set (sn' := make_stn n n' p).
      assert (q : n' < n). { exact p. }
      assert (q': r > n'). {apply (natgehtogthsn _ _ r_gt_n'). }
      unfold gauss_clear_column_old in *.
      rewrite nat_rect_step.
      destruct (natgthorleh _ _); try reflexivity.
      rewrite gauss_clear_column_step_inv2.
      2: { apply natgthtoneq. assumption. }
      rewrite IHn'.
      + reflexivity.
      + apply (natgthtogeh). assumption.
  Defined.


  (* Invariant stating that the clearing procedure does clear all the target entries (r, k) for r > k. *)
  Lemma gauss_clear_column_inv1
        { n : nat } (k_i k_j : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (mat : Matrix hq n n) (p' : mat k_i k_j != 0%hq) :  ∏ r : (⟦ n ⟧%stn),
    r < iter -> r > k_i -> ((gauss_clear_column_old mat k_i k_j iter) r k_j = 0%hq).
  Proof.
    destruct iter as [n' p].
    intros r r_le_n' r_gt_k.
    rewrite (gauss_clear_column_inv0  k_i k_j (n' ,, p) mat (*p'*) r r_le_n').
    rewrite <- gauss_clear_column_step_eq.
    rewrite (gauss_clear_column_step_inv1 n k_i k_j r mat); try reflexivity; try assumption.
    - apply natgthtoneq. assumption.
    - apply r_gt_k.
  Defined.


  (* if the iterator n' ≤   the pivot index k,
     applying the clearing procedure leaves mat invariant. *)
  Lemma gauss_clear_column_inv2
        { n : nat } (k_i k_j : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn) (p' : S iter ≤ k_i)
        (mat : Matrix hq n n) (kk_ne_0 : mat k_i k_j != 0%hq) :
    ((gauss_clear_column_old mat k_i k_j iter) = mat ).
  Proof.
    intros.
    destruct iter as [n' p].
    apply funextfun. intros i.
    intros.
    induction n' as [| m IHn].
    - simpl.
      reflexivity.
    - assert (p'': m < S n). { apply (istransnatgth _ _ _ p (natgthsnn m) ). }
      assert (p''' : S m ≤ k_i). { apply (istransnatgeh _ _ _ p' (natgehsnn (S m) )  ). }
      set (IHn' := IHn p'' p''').
      rewrite <- IHn'.
      unfold gauss_clear_column_old.
      rewrite nat_rect_step.
      destruct (natgthorleh _ _).
      { clear IHn'. apply fromempty. apply natgehsntogth in p''.
        apply natgehsntogth in p'''.
        apply isasymmnatgth in p'''; try assumption; contradiction.
      }
      unfold gauss_clear_column_old in IHn.
      rewrite  IHn; try assumption; reflexivity.
  Defined.


  (* Expresses the property that a matrix is partially upper triangular -
     in the process of being constructed as upper triangular.
     mat =
     [ 1 0 0 1
       0 1 1 1
       0 0 1 1
       0 0 1 1]  - fulfills  gauss_columns_cleared mat (1,, 1 < 4).

    Additionally expresses the property that any entry i j with i > k_i is 0.

  TODO maybe not uiseful anymore. *)
  Definition gauss_columns_cleared { n : nat } (mat : Matrix hq n n)
             (k_i k_j : ⟦ n ⟧%stn) := ∏ i j : ⟦ n ⟧%stn,
              j < k_j ->
              k_i < i ->
              mat i j = 0%hq.

  Definition diagonal_filled { n : nat } (mat : Matrix hq n n) :=
    ∏ i : ⟦ n ⟧%stn, mat i i != 0%hq.



  (*  *)
  Lemma gauss_clear_column_step_inv6
    {n : nat} (mat : Matrix hq n n) (i j : (⟦ n ⟧)%stn) (k_i k_j : (⟦ n ⟧)%stn)
    :
    mat k_i j = 0%hq -> gauss_clear_column_step n k_i k_j j mat  i j = mat i j.
  Proof.
    intros kj_0.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _). {apply idpath. }
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _) as [eq | neq].
    - simpl. rewrite kj_0. rewrite (@rigmultx0 hq _).
      rewrite eq. apply (@rigrunax1 hq).
    - simpl.
      apply idpath.
  Defined.

  (* Proving that if the input matrix is _lower triangular_, it will remain so after gcc. *)
  Lemma gauss_clear_column_inv5
    { n : nat }  (mat : Matrix hq n n) (k_i k_j  : (⟦ n ⟧%stn)) (iter : ⟦ S n ⟧%stn)
    (lt : @is_lower_triangular hq n n mat)
    :
    @is_lower_triangular hq n n  (gauss_clear_column_old mat k_i k_j iter).
  Proof.
    intros.
    unfold is_lower_triangular.
    unfold gauss_clear_column_old.
    destruct iter as [iter ?].
    induction iter.
    { intros i j i_lt_j. simpl.
      apply (lt _ _ i_lt_j). }
    intros i j i_lt_j.
    rewrite nat_rect_step.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (natgthorleh _ _) as [gt | le].
    2: { apply lt.  assumption. }
    destruct (stn_eq_or_neq (*(iter,, pr2) i*) _ _) as [eq | ?].
    { rewrite <- eq in gt. apply isirreflnatgth in gt. contradiction. }
    set (m := nat_rect _ _ _ _).
    set (p := istransnatlth _ _ _ _).
    unfold gauss_add_row.
    apply issymm_natneq in h.
    destruct (stn_eq_or_neq i (iter,, pr2)).
    - simpl.
      rewrite IHiter.
      2: { rewrite p0 in i_lt_j.
           simpl in i_lt_j. simpl. rewrite <- i_lt_j.
           reflexivity. }
      replace (m _ k_i j) with 0%hq.
      2: {unfold m.
          rewrite IHiter; try reflexivity.
          rewrite p0 in i_lt_j.
          refine (istransnatgth _ _ _ _ _).
          - apply i_lt_j.
          - apply gt.
      }
      rewrite (@rigmultx0 hq).
      rewrite (@riglunax1 hq).
      apply idpath.
    - simpl.
      rewrite  IHiter; try reflexivity; try assumption.
  Defined.

  (* 0 in pivot row -> corresponding col is unchanged after gcc *)
  Lemma gauss_clear_column_inv6
    { n : nat }  (mat : Matrix hq n n) ( k_i k_j  : (⟦ n ⟧%stn)) (iter : ⟦ S n ⟧%stn)
    (j : ⟦ n ⟧%stn) (p : mat k_i j = 0%hq)
    :
    ∏ i : ⟦ n ⟧%stn, gauss_clear_column_old mat k_i k_j iter i j = mat i j.
  Proof.
    unfold gauss_clear_column_old.
    destruct iter as [iter ?].
    induction iter.
    { intros i. simpl. reflexivity. }
    intros i.
    rewrite nat_rect_step.
    rewrite  gauss_clear_column_step_eq.
    destruct (stn_eq_or_neq (iter,, pr2) (*j*) k_i) as [eq | ?].
    - rewrite <- eq.
      destruct (natgthorleh _ _) as [contr | ?].
      { apply isirreflnatgth in contr. contradiction. }
      reflexivity.
    - assert (obv : iter < S n). {exact (istransnatlth iter (S iter) (S n) (natlthnsn iter) pr2). }
      rewrite <- (IHiter (istransnatlth iter (S iter) (S n) (natlthnsn iter) pr2)).
      rewrite <- gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct ( natgthorleh _ _).
      2: { rewrite IHiter. reflexivity. }
      set (f := nat_rect _ _ _ _).
      set (m := f _).
      rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _); try reflexivity.
      unfold gauss_add_row.
      destruct (stn_eq_or_neq _ _); try apply coprod_rect_compute_1; try apply coprod_rect_compute_2.
      + rewrite coprod_rect_compute_1.
        unfold m. do 3 rewrite IHiter.
        rewrite p.
        rewrite <- p0.
        rewrite (@rigmultx0 hq).
        rewrite (@rigrunax1 hq).
        reflexivity.
      + rewrite coprod_rect_compute_2.
        reflexivity.
  Defined.

  Definition first_nonzero_element_internal
    { n : nat } (v : Vector hq n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧)%stn.
  Proof.
    destruct iter as [iter lt].
    induction iter.
    { exact nothing. }
    simpl in lt.
    assert (lt' : iter < S n). {apply (istransnatlth _ _ _ lt (natgthsnn n)). }
    destruct (isdeceqhq 0%hq (v (dualelement  (iter,, lt)))).
    - exact (IHiter lt').
    - exact (just (dualelement (iter,, lt))).
  Defined.

  Definition first_nonzero_element
    { n : nat } (v : Vector hq n)
    := first_nonzero_element_internal v (n,, natgthsnn n).

  Definition last_zero_element_internal
    { n : nat } (v : Vector hq n) (p : n > 0) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧)%stn.
  Proof.
    destruct iter as [iter lt].
    induction iter.
    { exact nothing. }
    simpl in lt.
    assert (lt' : iter < S n). {apply (istransnatlth _ _ _ lt (natgthsnn n)). }
    destruct (isdeceqhq 0%hq (v ((iter,, lt)))).
    - exact (IHiter lt').
    - exact (just (iter,, lt)).
  Defined.


  Definition from_just {X : UU} (m : maybe X) (p : m != nothing) : X.
  Proof.
    unfold nothing in p.
     destruct m as [x | u].
     - exact x.
     - contradiction p.
       rewrite u; reflexivity.
  Defined.

  (* 1 : any leading entry is strictly to the right of a previous leading entry
     2 : any zero row is below any non-zero row *)
  Definition is_row_echelon {n : nat} (mat : Matrix hq n n) :=
    ∏ i_1 i_2 : ⟦ n ⟧%stn,
    ∏ j_1 j_2 : ⟦ n ⟧%stn,
       leading_entry_compute (mat i_1) = (just j_2)
    -> i_1 < i_2
    -> j_1 ≤ j_2
    -> mat i_2 j_1 = 0%hq
   × ((mat i_1 = const_vec 0%hq) -> (i_1 < i_2) -> (mat i_2 = const_vec 0%hq)).

  Definition is_row_echelon_partial_1
    {n : nat} (mat : Matrix hq n n) (p : n > 0) (row_sep : ⟦ S n ⟧%stn) :=
    ∏ i_1 i_2 : ⟦ n ⟧%stn,
    ∏ j_1 j_2 : ⟦ n ⟧%stn,
     i_1 < row_sep
    -> leading_entry_compute (mat i_1) = (just j_2)
    -> i_1 < i_2
    -> j_1 ≤ j_2
    -> mat i_2 j_1 = 0%hq.

  Definition is_row_echelon_partial_2
    {n : nat} (mat : Matrix hq n n) (iter : ⟦ S n ⟧%stn) :=
    ∏ (i_1 i_2 : ⟦ n ⟧%stn),
    i_1 < iter
    -> (mat i_1 = const_vec 0%hq)
    -> i_1 < i_2
    -> mat i_2 = const_vec 0%hq.

  Definition is_row_echelon_partial {n : nat} (mat : Matrix hq n n) (p : n > 0) (iter : ⟦ S n ⟧%stn)
    := is_row_echelon_partial_1 mat p iter × is_row_echelon_partial_2 mat iter.

  Lemma is_row_echelon_from_partial
    {m n : nat} (mat : Matrix hq n n) (p : n > 0)
    : (is_row_echelon_partial mat p (n,, natgthsnn n)) -> is_row_echelon mat.
  Proof.
    unfold is_row_echelon, is_row_echelon_partial.
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    intros H ? ? ? H' ?; intros.
    use tpair.
    { refine ((pr1 H) i_1 i_2 _ _ _ _ _ _);
      try apply X; try assumption. exact (pr2 i_1).
    }
    simpl; intros.
    refine ((pr2 H) i_1 i_2 _ _ _ ); try assumption.
    exact (pr2 i_1).
  Abort.

  Lemma gauss_clear_row_inv0
    {n : nat} (m : Matrix hq n n) (row : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : ∏ i : ⟦ n ⟧%stn, i < row -> (gauss_clear_row m ) row i = m i.
  Proof.
    unfold gauss_clear_row.
    destruct (natchoice0 n) as [contr_eq | ?]. { apply fromstn0. rewrite contr_eq; assumption. }
    intros i lt.
    destruct (select_uncleared_column _ _) as [j H].
    destruct H as [some | none].
    - simpl.
      rewrite gauss_clear_column_inv3; try reflexivity; try assumption.
      2: { apply natgthtogeh. assumption. }
      apply funextfun; intros ?.
      rewrite (@gauss_switch_row_inv0 n n _); try reflexivity.
      { apply natlthtoneq. assumption. }
      apply natlthtoneq.
      refine (natlthlehtrans _ _ _ _ _).
      {apply lt. }
      apply (pr1 (pr2 (pr2 some))).
   - reflexivity.
  Defined.

  Lemma const_vec_eq  {X : UU} {n : nat} (v : Vector X n) (e : X) (i : ⟦ n ⟧%stn)
    : v = const_vec e -> v i = e.
    Proof. intros eq. rewrite eq. reflexivity.
  Defined.

  Lemma gauss_clear_row_internal_inv2
    {n : nat} (mat : Matrix hq n n) (p : n > 0) (row : ⟦ n ⟧%stn)
    : ∏ i_1 : ⟦ n ⟧%stn,
       (gauss_clear_row mat i_1) i_1 = const_vec 0%hq
    -> ∏ i_2 : ⟦ n ⟧%stn, i_1 < i_2
    -> mat i_2 = const_vec 0%hq.
  Proof.
    intros i_1 eqconst0 i_2 i1_lt_j2.
    unfold gauss_clear_row in *.
    destruct (natchoice0 n) as [contr_eq | ?]. { apply fromstn0. rewrite contr_eq; assumption. }
    destruct (select_uncleared_column _ _) as [k H].
    destruct H as [H1 | none].
    2: { simpl; simpl in eqconst0.
         apply funextfun; intros j'; rewrite none; try assumption; try reflexivity.
         {apply natlthtoleh. assumption. }
         apply (pr2 j').
    }
    simpl.
    revert eqconst0; simpl.
    rewrite gauss_clear_column_inv3.
    2: {apply isreflnatleh. }
    unfold gauss_clear_column_step'.
    unfold gauss_switch_row.
    rewrite (stn_eq_or_neq_left (idpath i_1)).
    simpl.
    intros.
    assert( eqz  : (λ j : (⟦ n ⟧)%stn, mat (pr1 (pr2 H1)) k) (pr1 (pr2 H1)) = 0%hq).
    { rewrite (const_vec_eq _ 0%hq); try assumption; try reflexivity. }
    contradiction (pr1 (pr2 (pr2 (pr2 ((H1)))))).
  Defined.

  Lemma gauss_clear_row_internal_inv4
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0) (* Remove p when gcc is refactored *)
    (row_sep : (⟦ S n ⟧%stn))
    (p' : row_sep < n)
    :  is_row_echelon_partial_1 mat p
        (pr1 row_sep,, istransnatlth (pr1 row_sep) n (S n) (p') (natgthsnn n))
    -> is_row_echelon_partial_1 (gauss_clear_row mat (pr1 row_sep,, p')) p
        (S (pr1 row_sep),, p').
  Proof.
    intros H1.
    unfold is_row_echelon_partial_1 in *.
    unfold gauss_clear_rows_up_to.
    intros i_1 i_2 j_1 j_2 i1_lt H2.
    intros i1_lt_i2 j1_lt_j2.
    revert H2.
    unfold gauss_clear_row.
    clear p.
    destruct (natchoice0 n) as [contr_eq | p]. { apply fromstn0. rewrite contr_eq; assumption. }
    destruct (select_uncleared_column _ _ _) as [j H3]; simpl.
    destruct H3 as [some | none].
    2: { destruct (natlehchoice i_1 row_sep) as [i1_lt_rowsep | eq]. {apply natlthsntoleh. assumption. }
         { intros. rewrite (H1 i_1 i_2 j_1 j_2); try assumption; try reflexivity. }
         rewrite none; try assumption; try reflexivity.
         - apply natlthtoleh. change (pr1 (pr1 row_sep,, p')) with (pr1 row_sep).
            assert (eq' : pr1 i_1 = pr1 row_sep). {apply eq. }
            unfold hProptoType. simpl.
            rewrite <- eq'.
            assumption.
         - apply (pr2 j_1).
    }
    destruct (natlehchoice i_1 row_sep) as [i1_lt_rowsep | eq]. { apply (natlthsntoleh _ _ i1_lt). }
    - destruct (natgthorleh i_2 row_sep) as [i2_gt_rowsep | i2_le_rowsep].
    + rewrite gauss_clear_column_inv3; try assumption.
      rewrite gauss_clear_column_inv0; try assumption.
      2: { apply (pr2 i_2). }
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _) as [contr_eq | i2_neq_rowsep].
      { rewrite contr_eq in *. contradiction (isirreflnatgth _ i2_gt_rowsep). }
      intros H2.
      rewrite gauss_add_row_inv2.
      * destruct (stn_eq_or_neq (pr1 row_sep,, p') (pr1 (pr2 some))) as [rowsep_eq_some | ne].
        -- revert H2. rewrite (@gauss_switch_row_inv2 n n _).
           2: { simpl. rewrite <- rowsep_eq_some. reflexivity. }
           rewrite (@gauss_switch_row_inv0 n n _).
           3: { rewrite <- rowsep_eq_some in *. apply natlthtoneq. assumption. }
           2: { apply natlthtoneq. assumption. }
           intros. rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption.
        -- revert H2.
           rewrite (@gauss_switch_row_inv0 n n _).
           3: {apply natlthtoneq. apply (natlthlehtrans _ _ _ i1_lt_rowsep (pr1 (pr2 (pr2 some)))). }
           2: {apply natlthtoneq; assumption. }
           intros H2; destruct (stn_eq_or_neq i_2 (pr1 (pr2 some))).
           2: {rewrite (@gauss_switch_row_inv0 n n _); try assumption.
               rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption.
           }
           unfold gauss_switch_row; destruct (stn_eq_or_neq _ _).
           ++ simpl. destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
              { contradiction (isirrefl_natneq i_2). rewrite <- contr_eq in i2_neq_rowsep; assumption. }
              rewrite <- (H1 i_1 (pr1 row_sep,, p') j_1 j_2); try reflexivity; try assumption.
           ++ simpl.
              destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
              { contradiction (isirrefl_natneq i_2). rewrite <- contr_eq in i2_neq_rowsep; assumption. }
              rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption.
        * revert H2.
          assert (i1_lt_some : i_1 < (pr1 (pr2 (some)))).
          { apply (natlthlehtrans _ _ _ i1_lt_rowsep (pr1 (pr2 (pr2 some)))). }
          unfold gauss_switch_row; destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
          {rewrite contr_eq. apply (natlthtoneq) in i1_lt_some. rewrite contr_eq in i1_lt_some.
           pose (contr_neq := (natlthtoneq _ _ (natlthlehtrans _ _ _ i1_lt_rowsep (pr1 (pr2 (pr2 some)))))).
           rewrite contr_eq in contr_neq; apply isirrefl_natneq in contr_neq; contradiction.
          }
          destruct (stn_eq_or_neq _ _) as [contr_eq | ?] ; simpl.
          {apply natlthtoneq in i1_lt_rowsep. rewrite contr_eq in i1_lt_rowsep.
           apply isirrefl_natneq in i1_lt_rowsep.
           contradiction. }
          intros H2.
          destruct (stn_eq_or_neq _ _); simpl.
          -- destruct (stn_eq_or_neq _ _); simpl.
             2: {contradiction (isirrefl_natneq row_sep). }
             rewrite (H1 i_1 (pr1 (pr2 (some))) j_1 j_2); try reflexivity; try assumption.
          -- simpl.
             destruct (stn_eq_or_neq _ _); simpl.
             2: {contradiction (isirrefl_natneq row_sep). }
             rewrite (H1 i_1 (pr1 (pr2 (some))) j_1 j_2); try reflexivity; try assumption.
      + rewrite gauss_clear_column_inv3. 2: {apply natlthtoleh. assumption. }
        rewrite gauss_clear_column_inv3. 2: {assumption.  }
        rewrite (@gauss_switch_row_inv0 n  _).
        3: {apply natlthtoneq. apply (natlthlehtrans _ _ _ i1_lt_rowsep (pr1 (pr2 (pr2 some)))). }
        2: {apply natlthtoneq. assumption. }
        unfold gauss_switch_row; destruct (stn_eq_or_neq _ _); simpl.
        -- destruct (stn_eq_or_neq _ _); simpl; intros.
           ++ rewrite (H1 i_1 (pr1 (pr2 (some))) j_1 j_2); try reflexivity; try assumption.
              apply (natlthlehtrans _ _ _ i1_lt_rowsep (pr1 (pr2 (pr2 some)))).
           ++ rewrite <- (H1 i_1 (pr1 row_sep,, p') j_1 j_2); try reflexivity; try assumption.
        -- destruct (stn_eq_or_neq _ _); simpl.
           ++ intros.
              rewrite (H1 i_1 (pr1 (pr2 (some))) j_1 j_2); try reflexivity; try assumption.
              apply (natlthlehtrans _ _ _ i1_lt_rowsep (pr1 (pr2 (pr2 some)))).
           ++ intros.
              rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption.
    - rewrite gauss_clear_column_inv3.
      2: { rewrite eq. apply isreflnatleh. }
      assert (st_eq  : pr1 i_1 = pr1 row_sep). {apply eq. }
      destruct (stn_eq_or_neq j_1 j_2) as [j1_eq_j2 | j1_neq_j2]; try assumption.
      + rewrite j1_eq_j2 in *.
        rewrite gauss_clear_column_inv0.
        3: { simpl. rewrite <- st_eq; exact (i1_lt_i2). }
        2: { exact (pr2 i_2). }
        rewrite <- gauss_clear_column_step_eq.
        unfold gauss_switch_row.
        destruct (stn_eq_or_neq _ _) as [eq'' | ?].
        { simpl.
          destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
          2: {simpl in contr_neq. rewrite <- st_eq in contr_neq. contradiction (isirrefl_natneq _ contr_neq). }
          intros.
          destruct (stn_eq_or_neq j j_2) as [j_eq_j2 | j_neq_j2].
          - simpl; rewrite j_eq_j2 in *.
            intros.
            rewrite gauss_clear_column_step_inv1; try reflexivity; try assumption.
            2: { apply natgthtoneq. simpl. rewrite <- st_eq. assumption.  }
            destruct (stn_eq_or_neq _ _) as [? | contr_neq].
            2: { simpl in contr_neq. apply fromempty. simpl in st_eq.
                 try contradiction (isirrefl_natneq _ contr_neq).
                 rewrite <- eq'' in contr_neq.
                 rewrite eq in contr_neq.
                 contradiction (isirrefl_natneq _ contr_neq).
            }
            destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
            2: { contradiction (isirrefl_natneq _ contr_neq). }
            rewrite <- j_eq_j2.
            apply (pr1 (pr2 (pr2 (pr2 (some))))).
          - intros.
            destruct (natneqchoice j j_2); try assumption.
            + pose (H3 := @leading_entry_compute_internal_correct1 n
                        (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
              contradiction (pr1 H3).
              rewrite (pr2 (pr2 (pr2 (pr2( some))))); try assumption; try reflexivity.
              apply (pr1 (pr2 (pr2 (some)))).
            + contradiction (pr1 (pr2 (pr2 (pr2( some))))).
              pose (H3 := @leading_entry_compute_internal_correct1 n
                        (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
              rewrite (pr2 H3 j); try assumption; try reflexivity.
              exact (pr2 j).
        }
        destruct (stn_eq_or_neq _ _) as [eq'' | contr_neq]; simpl.
        2: { simpl in contr_neq. apply fromempty. rewrite eq in contr_neq. apply (isirrefl_natneq _ contr_neq). }
        destruct (stn_eq_or_neq j j_2) as [j_eq_j2 | j_neq_j2].
        simpl; rewrite j_eq_j2 in *.
        intros.
        rewrite gauss_clear_column_step_inv1; try reflexivity; try assumption.
        2: { apply natgthtoneq. simpl. rewrite <- st_eq. assumption.  }
        destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
        * simpl in contr_eq.
          rewrite <- contr_eq in h.
          simpl in h.
          rewrite eq in h. contradiction (isirrefl_natneq _ h).
        * destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
          2: { contradiction (isirrefl_natneq _ contr_neq). }
          rewrite <- j_eq_j2.
          apply (pr1 (pr2 (pr2 (pr2 (some))))).
        *
          intros.
          destruct (natneqchoice j j_2); try assumption.
          -- pose (H3 := @leading_entry_compute_internal_correct1 n
                        (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
              contradiction (pr1 H3).
              rewrite (pr2 (pr2 (pr2 (pr2( some))))); try assumption; try reflexivity.
              apply (pr1 (pr2 (pr2 (some)))).
          --  contradiction (pr1 (pr2 (pr2 (pr2( some))))).
              pose (H3 := @leading_entry_compute_internal_correct1 n
                        (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
              rewrite (pr2 H3 j); try assumption; try reflexivity.
              exact (pr2 j).
      +

      rewrite gauss_clear_column_inv0.
      3: { refine (natlehlthtrans _ _ _ _ _). try rewrite <- eq. {apply isreflnatleh. }
           simpl. rewrite <- st_eq. assumption. }
      2: { exact (pr2 i_2). }
      destruct (stn_eq_or_neq i_2 (pr1 row_sep,, p')) as [contr_eq | ?] ; simpl.
      { contradiction (isirreflnatgth row_sep).
        etrans. {apply maponpaths. rewrite <- eq. reflexivity. }
        apply natlthtoneq in i1_lt_i2. rewrite contr_eq in i1_lt_i2. rewrite eq in i1_lt_i2.
        (contradiction (isirrefl_natneq _ i1_lt_i2)).
      }
      unfold gauss_switch_row.
      destruct (stn_eq_or_neq _ _) as [eq' | ?]; simpl.
      { destruct (stn_eq_or_neq _ _) as [? | contr_neq] ; simpl.
        2: { simpl in contr_neq. rewrite eq in contr_neq. contradiction (isirrefl_natneq _ contr_neq). }
        destruct (stn_eq_or_neq i_2 (pr1 row_sep,, p')) as [i1_eq_some | i1_neq_some].
        { unfold gauss_clear_column_step'.
          contradiction (isirrefl_natneq row_sep).
          rewrite i1_eq_some in h.
          contradiction (isirrefl_natneq _ h). }
        intros.
        destruct (natgthorleh j j_1); try assumption.
        2: {unfold leading_entry_compute in H2.
          pose (H3 := @leading_entry_compute_internal_correct1 n
                    (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
          contradiction (pr1 (pr2 (pr2 (pr2 (some))))).
          rewrite (pr2 H3 (j)); try reflexivity.
          2: {apply (pr2 j). }
          destruct (natlehchoice j_1 j_2) as [lt' | contr_eq]; try assumption.
          { apply (natlthlehtrans _ _ _ h0 lt'). }
          (* use h, j_1 ≠ j_2 *)
          simpl in contr_eq. simpl in h. simpl in j1_neq_j2. rewrite <- contr_eq in j1_neq_j2.
          contradiction (isirrefl_natneq _ j1_neq_j2).
        }
        unfold gauss_clear_column_step'.
        destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
        {rewrite contr_eq in h.
         contradiction (isirrefl_natneq _ h). }
        destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
        { rewrite <- contr_eq in eq'. rewrite eq' in i1_lt_i2. contradiction (isirreflnatlth _ i1_lt_i2). }
        try intros H2.
        destruct (natgthorleh j j_1) as [? | contr_le]; try assumption.
        2: { contradiction (natlehtonegnatgth _ _ contr_le). }
        rewrite gauss_add_row_inv2.
        destruct (stn_eq_or_neq _ _) as [i2_eq_some | i2_neq_some].
        + destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
          { try rewrite <- contr_eq. try rewrite <- contr_eq in i2_eq_some.
            rewrite i2_eq_some in h.
            rewrite contr_eq in h1.
            contradiction (isirrefl_natneq _ h1).
          }
          destruct (natgthorleh j j_1) as [? | contr_le]; try assumption.
          2: { contradiction (natlehtonegnatgth _ _ contr_le). }
          unfold leading_entry_compute in H1.
          rewrite (pr2 (pr2 (pr2 (pr2 (some))))); try reflexivity; try assumption.
          {apply isreflnatleh.  }
      + destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
        { simpl in h0.
          rewrite contr_eq in h1.
          contradiction (isirrefl_natneq _ h1). }
        rewrite (pr2 (pr2 (pr2 (pr2 some)))); try reflexivity; try assumption.
        apply natlthtoleh.
        simpl.
        rewrite <- st_eq; assumption.
      +
        destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
        2: { try rewrite contr_eq in p0. try rewrite p0 in h1. try apply isirrefl_natneq in h1.
             try contradiction.
             rewrite <- p0 in contr_neq.
             rewrite eq' in contr_neq.
             contradiction (isirrefl_natneq _ contr_neq).
        }
        destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
        2: {apply isirrefl_natneq in contr_neq; contradiction. }
        rewrite (pr2 (pr2 (pr2 (pr2 some)))); try reflexivity; try assumption.
        apply (pr1 (pr2 (pr2 (some)))).
      }
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _) as [? | contr_neq].
      2: { simpl in contr_neq. contradiction (isirrefl_natneq row_sep).
           try rewrite eq in contr_neq; try assumption.
      }
      destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
      {rewrite contr_eq in h.
       contradiction (isirrefl_natneq _ h). }
      intros.
      rewrite gauss_add_row_inv2; try assumption.
      * intros.
        destruct (stn_eq_or_neq _ _) as [i2_eq_some | i2_neq_some].
        -- destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
        { rewrite contr_eq in h1.
          try contradiction (isirrefl_natneq _ h1).
        }
        destruct (natgthorleh j j_1); try assumption.
        2: {intros.
            unfold leading_entry_compute in H2.
            pose (H3 := @leading_entry_compute_internal_correct1 n
                      (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
            contradiction (pr1 (pr2 (pr2 (pr2 (some))))).
            rewrite (pr2 H3 (j)); try reflexivity.
            2: {apply (pr2 j). }
            destruct (natlehchoice j_1 j_2) as [lt' | contr_eq]; try assumption.
            { apply (natlthlehtrans _ _ _ h3 lt'). }
            (* use h, j_1 ≠ j_2 *)
              simpl in contr_eq. simpl in h. simpl in j1_neq_j2. rewrite <- contr_eq in j1_neq_j2.
              contradiction (isirrefl_natneq _ j1_neq_j2).
        }
        unfold leading_entry_compute in H1.
        rewrite (pr2 (pr2 (pr2 (pr2 (some))))); try reflexivity; try assumption.
        {apply isreflnatleh.  }
        --
          destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
        { rewrite contr_eq in h1.
          contradiction (isirrefl_natneq _ h1). }
        intros.
        rewrite (pr2 (pr2 (pr2 (pr2 some)))); try reflexivity; try assumption.
        { apply natlthtoleh.
          simpl. rewrite <- st_eq. assumption.
        }
        destruct (natgthorleh j j_1); try assumption.
        intros.
        pose (H3 := @leading_entry_compute_internal_correct1 n
                      (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
        contradiction (pr1 (pr2 (pr2 (pr2 (some))))).
        rewrite (pr2 H3 (j)); try reflexivity.
        2: {apply (pr2 j). }
        destruct (natlehchoice j_1 j_2) as [lt | contr_eq]; try assumption.
        { apply (natlehlthtrans  _ _ _ h3 lt). }
        simpl in h, j1_neq_j2; rewrite <- contr_eq in j1_neq_j2.
        contradiction (isirrefl_natneq _ j1_neq_j2).
      * destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
        { try rewrite contr_eq in p0. try rewrite p0 in h1. try apply isirrefl_natneq in h1.
          try contradiction.
          rewrite <- contr_eq in h0.
          simpl in h0. rewrite eq in h0.
          contradiction (isirrefl_natneq _ h0).
        }
        destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
        2: {apply isirrefl_natneq in contr_neq; contradiction. }
        rewrite (pr2 (pr2 (pr2 (pr2 some)))); try reflexivity; try assumption.
        {apply (pr1 (pr2 (pr2( some)))). }
        destruct (natgthorleh j j_1); try assumption.
        intros.
        pose (H3 := @leading_entry_compute_internal_correct1 n
                      (λ i : (⟦ n ⟧)%stn, mat (pr1 (pr2 some)) (i)) (n,, natgthsnn n) j_2 H2).
        contradiction (pr1 (pr2 (pr2 (pr2 (some))))).
        rewrite (pr2 H3 (j)); try reflexivity.
        2: {apply (pr2 j). }
        destruct (natlehchoice j_1 j_2) as [lt | contr_eq]; try assumption.
        { apply (natlehlthtrans  _ _ _ h3 lt).
        }
        simpl in j1_neq_j2.
        rewrite <- contr_eq in j1_neq_j2.
        contradiction (isirrefl_natneq _ j1_neq_j2).
  Defined.


  (* TODO : is_row_echelon_partial_2  (gauss_clear_rows_up_to mat p row_sep) row_sep. *)
  Lemma gauss_clear_rows_up_to_internal_inv0
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0) (* Remove p when gcc is refactored *)
    (row_sep : (⟦ S n ⟧%stn))
   : ∏ i_1 : ⟦ n ⟧%stn, i_1 < row_sep
  -> (gauss_clear_rows_up_to mat p row_sep) i_1 = const_vec 0%hq
  -> ∏ i_2 : ⟦ n ⟧%stn, i_1 < i_2
  -> (gauss_clear_rows_up_to mat p row_sep) i_2 = const_vec 0%hq.
  Proof.
    unfold is_row_echelon_partial_2.
    intros i_1 i1_lt_rowsep (*eq_constv0*) le_nought (*i_2 i1_lt_i2*).
    (*intros i_1 i_2 ? ? i1_lt_rowsep (*eq_constv0*) le_nought i1_lt_i2. *)
    (*intros i_1 i1_lt_rowsep le_nought.*)
    unfold gauss_clear_rows_up_to in *.
    destruct row_sep as [row_sep lt].
    induction row_sep as [? | row_sep IH]. {simpl. contradiction (negnatgth0n i_1 i1_lt_rowsep). }
    rename  i1_lt_rowsep into i1_lt_srowsep.
    set (lt' := (istransnatlth row_sep (S row_sep) (S n) (natgthsnn row_sep) lt)).
    unfold gauss_clear_rows_up_to_internal in *.
    rewrite nat_rect_step in *.
    unfold gauss_clear_row in *.
    destruct (natchoice0 n) as [contr_eq | ?]. { apply fromstn0. rewrite contr_eq; assumption. }
    revert (*le_nought*)le_nought.
    destruct (natlehchoice i_1 row_sep) as [i1_lt_rowsep | eq]. {apply natlthsntoleh. assumption. }
    - destruct (select_uncleared_column _ _) as [opt_col H].
      destruct H as [some | none].
      2: { intros; simpl;
           rewrite IH; try reflexivity; try assumption.
      }
      destruct (pr2 (opt_col,, inl some)) as [t | ?].
      2: { intros;
           rewrite IH; try reflexivity; try assumption.
      }
      intros ? ? i1_lt_i2.
      destruct (natgthorleh i_2 row_sep) as [i2_gt_rowsep | i2_le_rowsep].
      + rewrite (@gauss_switch_row_inv1  n n _) in le_nought; try assumption.
        * rewrite gauss_clear_column_inv3 in le_nought. 2: { apply natlthtoleh. assumption. }
          rewrite gauss_clear_column_inv0; try assumption.
          2: {apply (pr2 i_2). }
          unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
          { contradiction (isirreflnatgth row_sep). rewrite contr_eq in *. assumption. }
          rewrite gauss_add_row_inv1; try assumption.
          -- rewrite (@gauss_switch_row_inv1 n n _).
             ++ rewrite IH; try assumption; try reflexivity.
             ++ rewrite IH; try reflexivity; try assumption.
                rewrite IH; try reflexivity; try assumption.
                apply (natgehgthtrans (*(pr1 t)*) (pr1 (pr2 t)) row_sep); try assumption.
                apply (*(pr2 t)*) ((((pr1 (pr2 ( pr2 t)))))).
          -- rewrite (@gauss_switch_row_inv1 n n _); try reflexivity; try assumption.
             ++ rewrite IH; try assumption; try reflexivity.
             ++ rewrite IH; try assumption; try reflexivity.
                rewrite IH; try assumption; try reflexivity.
                apply (natgehgthtrans (pr1 (pr2 t)) row_sep); try assumption.
                apply (pr1 (pr2 ( pr2 t))).
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natlthtoleh. assumption. }
          rewrite (@gauss_switch_row_inv0 n n _) in le_nought.
          3: { apply natlthtoneq. apply (natgehgthtrans (pr1 (pr2 t)) row_sep); try assumption.
               apply (pr1 (pr2 (pr2 t))). }
          2: { apply natlthtoneq. assumption. }
          rewrite IH; try assumption; try reflexivity.
          rewrite IH; try assumption; try reflexivity.
          apply (natgehgthtrans (pr1 (pr2 t)) row_sep); try assumption. apply (pr1 (pr2 (pr2 t))).
      + rewrite (@gauss_switch_row_inv1  n n _) in le_nought; try assumption.
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natgthtogeh in i1_lt_i2. apply (istransnatleh i1_lt_i2 i2_le_rowsep). }
          rewrite gauss_clear_column_inv3; try assumption.
          rewrite (@gauss_switch_row_inv1 n n _); try assumption.
          -- rewrite IH; try assumption; try reflexivity.
          -- rewrite IH; try reflexivity; try assumption.
             rewrite IH; try reflexivity; try assumption.
             apply (natgehgthtrans (pr1 (pr2 t)) row_sep); try assumption. apply (pr1 (pr2 (pr2 t))).
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natlthtoleh in i1_lt_rowsep. assumption. }
          rewrite (@gauss_switch_row_inv0 n n _) in le_nought.
          3: { apply natlthtoneq. refine (natlthlehtrans _ _ _ i1_lt_i2 _).
               apply (istransnatleh i2_le_rowsep (pr1 (pr2 (pr2 t)))). }
          2: {apply natlthtoneq.  apply (natlthlehtrans _ _ _ i1_lt_i2 i2_le_rowsep). }
          rewrite IH; try assumption; try reflexivity.
          rewrite IH; try assumption; try reflexivity.
          apply (natgehgthtrans (pr1 (pr2 t)) row_sep); try assumption. apply (pr1 (pr2 (pr2 t))).
    - intros.
      unfold gauss_clear_row in *.
      destruct (select_uncleared_column _ _) as [opt_col H].
      destruct H as [col | no_col].
      2: { set (inner := nat_rect _ _ _ _).
           set (inner' := inner (istransnatlth row_sep (S row_sep) (S n) (natgthsnn row_sep) lt)).
           apply funextfun; intros j_2.
           assert (le : row_sep ≤ i_2). {apply natgthtogeh. rewrite <- eq. assumption. }
           apply no_col; try assumption.
           apply (pr2 j_2).
      }
      destruct (pr2 (opt_col,, inl col)) as [contr | col_eq]; intros.
      2: {assert (eq' : (row_sep,, lt) = i_1).
        { apply subtypePath_prop.
          apply pathsinv0. apply eq.
        }
        set (inner := nat_rect _ _ _ _).
        rewrite <- eq' in *; clear eq'.
        About leading_entry_compute_eq.
        try rewrite leading_entry_compute_eq in le_nought.
        unfold leading_entry_compute in le_nought.
        unfold leading_entry_compute_internal in le_nought.
        try destruct (@maybe_stn_choice _ _  le_nought).
        try rewrite gauss_clear_column_inv3 in le_nought.
        try assert (le_nought' : leading_entry_compute_dual_internal _  (n,, natlthnsn n) = nothing).
        contradiction (pr1( pr2 ( pr2 (pr2 (col ))))).
        try rewrite gauss_clear_column_inv3 in le_nought.
        try rewrite <- (H' ( dualelement (opt_col))).
        unfold gauss_switch_row.
        destruct (stn_eq_or_neq i_1 i_1) as [? | contr_neq].
        2: { contradiction (isirrefl_natneq _ contr_neq). }
        try rewrite coprod_rect_compute_1.
        try apply maponpaths_12.
        rewrite col_eq; try reflexivity; try assumption.
        2: {apply (pr2 opt_col). }
        apply (pr1 (pr2 (pr2 ( col)))).
        }
      set (p' :=  (istransnatlth row_sep (S row_sep) (S n) (natgthsnn row_sep) lt)).
      unfold leading_entry_compute in le_nought.
      contradiction (pr1 (pr2 (pr2 (pr2 (contr)))) ).
      refine (const_vec_eq _ _ _ _).
      rewrite <- le_nought.
      unfold gauss_switch_row.
      rewrite gauss_clear_column_inv3.
      2: { rewrite eq. apply isreflnatleh. }
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _).
      + destruct (stn_eq_or_neq _ _) as [? | contr_neq].
        2: { contradiction (nat_neq_to_nopath contr_neq). }
        reflexivity.
      + destruct (stn_eq_or_neq _ _) as [? | contr_neq].
        2: { contradiction (nat_neq_to_nopath contr_neq). }
        simpl.
        reflexivity.
  Defined.

  (* (p' : row_sep < n)
    : is_row_echelon_partial_1 mat p
        (pr1 row_sep,, istransnatlth (pr1 row_sep) n (S n) (p') (natgthsnn n))
    -> is_row_echelon_partial_1 (gauss_clear_row mat p (pr1 row_sep,, p')) p
        (S (pr1 row_sep),, p'). *)

  Lemma gauss_clear_rows_up_to_inv1
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0)
    (row_sep : (⟦ S n ⟧%stn))
    : is_row_echelon_partial_1
        (gauss_clear_rows_up_to_internal mat p row_sep) p row_sep.
  Proof.
    About gauss_clear_row_internal_inv4.
    pose ( H:= @gauss_clear_row_internal_inv4).
    unfold gauss_clear_rows_up_to_internal.
    destruct row_sep as [row_sep p''].
    induction row_sep.
    { simpl. intros ? ? ? ? contr.
      contradiction (negnatlthn0 n contr). }
    rewrite nat_rect_step.
    About gauss_clear_row_internal_inv4.
    set (inner := nat_rect _ _ _ _).
    set (inner' := inner ( (istransnatlth row_sep (S row_sep) (S n) (natgthsnn row_sep) p''))).
    set (rowstn := make_stn n row_sep p'').
    change row_sep with (pr1 rowstn).
    assert (lt' : row_sep < S n). {apply (istransnatlth _ _ _ (natgthsnn row_sep) p''). }
    set (H' := H n inner' p (row_sep,, lt') p'').
    apply H'.
    change (pr1 (row_sep,, lt')) with row_sep.
    assert (eq : (istransnatlth row_sep n (S n) p'' (natgthsnn n))
                 = (istransnatlth row_sep (S row_sep) (S n) (natgthsnn row_sep) p'')).
    { apply proofirrelevance. apply propproperty. }
    rewrite eq.
    apply IHrow_sep.
  Defined.

  Lemma gauss_clear_rows_up_to_inv2
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0)
    (row_sep : (⟦ S n ⟧%stn))
    : is_row_echelon_partial_2
        (gauss_clear_rows_up_to_internal mat p row_sep) row_sep.
  Proof.
    pose ( H:= @gauss_clear_rows_up_to_internal_inv0).
    unfold is_row_echelon_partial_2.
    unfold gauss_clear_rows_up_to in H.
    intros.
    rewrite <- (H _ _ p row_sep i_1 X X0 i_2); try assumption.
    destruct row_sep as [row_sep p''].
    reflexivity.
  Defined.

  Lemma is_row_echelon_1_eq
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0)
    : is_row_echelon_partial_1
        (gauss_clear_rows_up_to mat p (n,, natgthsnn n)) p (n,, natgthsnn n)
    -> ∏ i_1 i_2 j_1 j_2 : ⟦ n ⟧%stn,
       i_1 < i_2
    -> leading_entry_compute (gauss_clear_rows_up_to mat p (n,, natgthsnn n) i_1) = just j_1
    -> leading_entry_compute (gauss_clear_rows_up_to mat p (n,, natgthsnn n) i_2) = just j_2
    -> j_1 < j_2.
  Proof.
    unfold is_row_echelon_partial_1.
    intros H1.
    intros i_1 i_2 j_1 j_2 lt.
    destruct (natgthorleh j_2 j_1) as [gt | ?]. {intros; apply gt. }
    unfold leading_entry_compute; intros H2 H3.
    pose (H4 := @leading_entry_compute_internal_correct1 n
                  _ (n,, natgthsnn n) _ H2).
    pose (H5 := @leading_entry_compute_internal_correct1 n
                  _ (n,, natgthsnn n) _ H3).
    destruct (natlehchoice j_2 j_1) as [lt' | eq]. {assumption. }
    - contradiction (pr1 H5).
      rewrite (H1 i_1 i_2 j_2 j_1); try assumption; try reflexivity.
      exact (pr2 i_1).
    - contradiction (pr1 H5).
      rewrite  eq in *.
      rewrite (H1 i_1 i_2 j_2 j_1); try assumption; try reflexivity.
      {exact (pr2 i_1). }
      rewrite eq.
      apply (isreflnatleh).
  Defined.

  Lemma prev_nat (n : nat) (p : n > 0): ∑ m, S m = n.
  Proof.
    destruct n as [c | ?]. {contradiction (negnatlthn0 _ p). }
    use tpair; try apply n; reflexivity.
  Defined.

  Lemma prev_stn {n : nat} (i : ⟦ n ⟧%stn) (p : i > 0): ∑ j : ⟦ n ⟧%stn, S j = i.
  Proof.
    pose (m := prev_nat i p).
    destruct m as [m eq].
    use tpair.
    - use tpair. {exact m. } simpl. refine (istransnatlth _ _ _ (natgthsnn m) _ ).
      rewrite eq. apply (pr2 i).
    - exact eq.
  Defined.


  Lemma row_echelon_partial_to_upper_triangular_partial
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0)
    (iter : ⟦ S n ⟧%stn)
    : @is_row_echelon_partial n  mat p iter
   -> @is_upper_triangular_partial hq n n iter mat.
  Proof.
    unfold is_row_echelon_partial, is_upper_triangular_partial.
    destruct iter as [iter p'].
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    induction iter as [| iter IH]. {simpl. intros ? ? ? ? contr. contradiction (nopathsfalsetotrue contr). }
    intros isre.
    destruct isre as [re_1 re_2].
    intros i j lt lt'.
    simpl in p'.
    assert (iter_lt_sn : iter < S n). {apply (istransnatlth _ _ _ p' (natgthsnn n)). }
    destruct (natlehchoice i iter) as [? | eq]. {apply natlthsntoleh; assumption. }
    - destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute (mat i))) as [t | none].
      + destruct t as [t eq].
        rewrite (IH iter_lt_sn); try reflexivity; try assumption.
        use tpair.
        * intros i_1 i_2 j_1 j_2  i1_lt_iter H ? ?.
          rewrite (re_1 i_1 i_2 j_1 j_2); try assumption; try reflexivity.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
        * simpl.
          intros i_1 i_2 (*j_1 j_2*) i1_lt_iter ? ?.
          rewrite (re_2 i_1 i_2 (*j_1 j_2*)); try assumption; try reflexivity.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
      + pose (H := @leading_entry_compute_internal_correct2 n _ _ none).
        rewrite H; try reflexivity.
        exact (pr2 (dualelement j)).
    - unfold stntonat in eq.
      assert (eq' : i = (iter,,  p')).
      { apply subtypePath_prop; apply eq. }
      destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute (mat i))) as [t | none].
      + destruct t as [t jst].
        destruct (natlthorgeh j t) as [j_lt_t | contr_gt].
        * pose (H := @leading_entry_compute_internal_correct1 n _ (n,, natgthsnn n)  _ jst).
          rewrite <- (pr2 H); try reflexivity; try assumption.
          exact (pr2 j).
        * pose (H1 := @leading_entry_compute_internal_correct1 n _ (n,, natgthsnn n)  _ jst).
          destruct (natchoice0 i) as [contr0 | ?].
          { apply fromempty; refine  (negnatgth0n _ _). rewrite contr0. apply lt. }
          destruct (prev_stn i) as [u u_lt]; try assumption.
          destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute (mat u))) as [prev | none_prev].
          -- destruct prev as [prev eq''].
             unfold leading_entry_compute in  prev.
             pose (H2 := @leading_entry_compute_internal_correct1 n _ (n,, natgthsnn n) _ eq'').
             contradiction (pr1 H2).
             rewrite (IH iter_lt_sn); try reflexivity; try assumption.
             use tpair.
             ** intros i_1 i_2 j_1 j_2  i1_lt_iter H' ? ?.
                rewrite (re_1 i_1 i_2 j_1 j_2); try assumption; try reflexivity.
                apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
             ** simpl.
                intros i_1 i_2 i1_lt_iter ? ?.
                rewrite (re_2 i_1 i_2); try assumption; try reflexivity.
                apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
             ** destruct (natgthorleh u prev); try assumption.
                contradiction (pr1 H1).
                rewrite (re_1 u i t prev); try assumption; try reflexivity; try assumption.
                --- apply natgehsntogth.
                    rewrite u_lt.
                    rewrite eq'.
                    apply natgehsnn.
                --- apply natgehsntogth.
                     rewrite u_lt.
                     rewrite eq'.
                     apply (isreflnatleh).
                --- destruct (natgthorleh t prev); try assumption.
                    apply (istransnatleh contr_gt).
                    refine (istransnatleh _ h0).
                    apply natlehsntolth.
                    apply natlthsntoleh.
                    rewrite u_lt.
                    apply lt.
             ** apply natgehsntogth.
                rewrite u_lt.
                rewrite eq'.
                apply (isreflnatleh).
            -- rewrite (re_2 u i ); try assumption; try reflexivity.
             ++ simpl; apply natlthtolths. rewrite <- eq.
                try apply (natlehlthtrans _ _ _ contr_gt lt ).
                apply natgehsntogth.
                rewrite u_lt.
                rewrite eq'.
                apply (isreflnatleh).
             ++ pose (H := @leading_entry_compute_internal_correct2 n _ (n,, natgthsnn n) none_prev).
                apply funextfun; intros j'; rewrite (H j'); try reflexivity.
                exact (pr2 (dualelement j')).
             ++ try apply (natlehlthtrans _ _ _ contr_gt lt ).
                apply natgehsntogth.
                rewrite u_lt.
                rewrite eq'.
                apply (isreflnatleh).
      + pose (H := @leading_entry_compute_internal_correct2 n _ _ none).
        rewrite H; try reflexivity.
        exact (pr2 (dualelement j)).
  Defined.

  Lemma row_echelon_to_upper_triangular
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0)
    (iter : ⟦ S n ⟧%stn)
    : @is_row_echelon n mat
   -> @is_upper_triangular hq n n mat.
  Proof.
    pose (H := @row_echelon_partial_to_upper_triangular_partial).
    try unfold row_echelon_partial_to_upper_triangular_partial in H.
  Abort.

  Lemma gauss_inv_row_echelon {n : nat} (mat : Matrix hq n n) :
    @is_row_echelon n (gauss_clear_all_row_segments mat ).
  Abort.

  Lemma gauss_inv_upper_triangular {n : nat} (mat : Matrix hq n n) :
    @is_upper_triangular hq n n (gauss_clear_all_row_segments mat ).
  Abort.

  Lemma gauss_inv_upper_triangular {n : nat} (mat : Matrix hq n n) :
    @is_upper_triangular hq n n (gauss_clear_all_row_segments mat ).
  Proof.
    intros i j i_gt_j.
    unfold gauss_clear_all_row_segments.
    destruct (natchoice0 n) as [n0 | n_gt_0].
    { simpl. clear i_gt_j. generalize i. rewrite <- n0 in i. apply (fromstn0 i). }
    simpl.
    destruct (@maybe_stn_choice hq n (leading_entry_compute (gauss_clear_rows_up_to mat n_gt_0 (n,, natgthsnn n) j) )) as [t | nothing].
    - unfold gauss_clear_rows_up_to.
      apply (gauss_clear_rows_up_to_inv1 _ n_gt_0 (n,, natgthsnn n) j _ j (pr1 t)); try assumption.
      2: {admit. }
      {admit . }
      destruct (natgthorleh j (pr1 t)); try assumption.
      pose (H := @leading_entry_compute_internal_correct1 n
                     (gauss_clear_rows_up_to mat n_gt_0 (n,, natgthsnn n) j) (n,, natgthsnn n) ).
      unfold leading_entry_compute in t.
      destruct t as [t eq].
      pose (H' := @leading_entry_compute_internal_correct1 n
                     (gauss_clear_rows_up_to mat n_gt_0 (n,, natgthsnn n) j) (n,, natgthsnn n) _ eq ).
      contradiction (pr1 H').
      About gauss_clear_rows_up_to_inv1.
      rewrite (gauss_clear_rows_up_to_inv1 _ _  _ j j t t); try reflexivity.
      (* Want a simple helper lemma that shows that the leading entry always ≥ diagonal *)
  Admitted.

  Lemma gauss_clear_columns_up_to_no_switch_inv0
        ( n : nat ) (mat : Matrix hq n n) (p' : n > 0)
        (iter1 iter2 : ⟦ S n ⟧%stn)  :
        iter1 ≤ iter2 ->
           @is_lower_triangular hq n n (@gauss_clear_columns_up_to_no_switch n p' iter1 mat)
        -> @is_lower_triangular hq n n (@gauss_clear_columns_up_to_no_switch n p' iter2 mat).
  Proof.
    intros iter1_le_iter2.
    destruct (natlehchoice iter1 iter2) as [iter1_lt_iter2 | eq]. {assumption. }
    2: { intros H. clear iter1_le_iter2. unfold is_lower_triangular. intros ? ? ?.
         replace iter2 with iter1. {apply H; assumption. }
         apply subtypePath_prop in eq. {rewrite eq; reflexivity. }
    }
    clear iter1_le_iter2.
    destruct iter1 as [iter1 iter1p].
    destruct iter2 as [iter2 iter2p].
    induction iter2.
    { apply fromempty. apply negnatlthn0 in iter1_lt_iter2. contradiction. }
    unfold gauss_clear_columns_up_to_no_switch in *.
    rewrite nat_rect_step.
    destruct (isdeceqhq _ _).
    - intros lt i j i_lt_j.
      destruct (natlehchoice iter1 iter2) as [? | iter1_eq_iter2]. { apply natlthsntoleh. exact iter1_lt_iter2. }
      + apply (IHiter2 (istransnatlth _ _ _ (natgthsnn iter2) iter2p));
          try reflexivity; try assumption.
      + simpl in iter2p.
        replace iter2 with (iter1).
        2: {rewrite <- iter1_eq_iter2. reflexivity. }
        rewrite <- (lt i j); try assumption.
        set (f := nat_rect _ _ _).
        revert iter1_lt_iter2.
        revert p. revert iter2p.
        rewrite <- iter1_eq_iter2.
        intros.
        apply maponpaths_3.
        apply proofirrelevance.
        apply propproperty.
    - intros lt i j i_lt_j.
      destruct (natlehchoice iter1 iter2) as [lt' | eq']. { apply natlthsntoleh in iter1_lt_iter2. assumption.  }
      + rewrite gauss_clear_column_inv5; try reflexivity; try assumption.
        intros i' j' i'_lt_j'.
        rewrite (IHiter2 (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) iter2p) lt' lt i' j' i'_lt_j').
        reflexivity.
      + rewrite gauss_clear_column_inv5; try reflexivity; try assumption.
        intros i' j' i'_lt_j'.
        rewrite <- (lt i' j'); try assumption.
        simpl in iter2p.
        revert iter1_lt_iter2.
        revert n0. revert iter2p.
        rewrite <- eq'.
        intros.
        change (S iter2 < S n) with (iter2 < n) in iter2p.
        set (f := nat_rect _ _ _).
        try rewrite <- eq'.
        apply maponpaths_3.
        intros.
        apply proofirrelevance.
        apply propproperty.
  Defined.

  Lemma gauss_clear_columns_up_to_no_switch_inv4
      ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
      (iter : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
      (k : ⟦ n ⟧%stn) :
      (@gauss_clear_columns_up_to_no_switch n p iter mat) k k = mat k k.
  Proof.
    destruct iter as [iter p''].
    pose (inv0 := gauss_clear_columns_up_to_no_switch_inv0).
    unfold is_lower_triangular in *.
    unfold gauss_clear_columns_up_to_no_switch in *.
    induction iter. { simpl. reflexivity. }
    rewrite nat_rect_step.
    destruct (isdeceqhq _ _).
    { rewrite IHiter; reflexivity. }
    destruct (natgthorleh k iter).
    2: { rewrite gauss_clear_column_inv3; try reflexivity; try assumption. apply IHiter. }
    rewrite gauss_clear_column_inv0. 2: { apply (pr2 k). }
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _); try apply IHiter; try assumption.
    2: {assumption. }
    set (f := nat_rect _ _ _ _).
    set (s := (istransnatlth iter (S iter) (S n) (natgthsnn iter) p'')).
    unfold gauss_add_row; rewrite stn_neq_or_neq_refl; simpl.
    etrans.
    { apply maponpaths.
      destruct (natgthorleh k iter).
      - rewrite hqmultcomm; replace  (f s _ k) with 0%hq.
        {rewrite (@rigmult0x hq); reflexivity. }
        unfold f, s; change 0%rig with 0%hq in inv0.
        set (iter_stn := make_stn (S n ) iter (istransnatlth _ _ _ (natgthsnn iter) p'')).
        change iter with (pr1 iter_stn).
        rewrite (inv0 n _ p  (0,, natgthsn0 n)); try reflexivity; try assumption.
      - replace  (f s k _) with 0%hq.
        + etrans.
          { rewrite hqmultcomm; apply maponpaths; rewrite hqmultcomm; rewrite (@rigmultx0 hq).
            pose (riu1 := ringinvunel1 hq).
            change (- 0)%ring with (- 0)%hq in riu1; change 0%ring with 0%hq in riu1.
            change 0%rig with 0%hq; rewrite riu1; reflexivity.
          }
          rewrite (@rigmultx0 hq); reflexivity.
        + unfold f, s.
          change 0%rig with 0%hq in inv0.
          set (iter_stn := make_stn (S n ) iter (istransnatlth _ _ _ (natgthsnn iter) p'')).
          change iter with (pr1 iter_stn).
          rewrite (inv0 n _ p  (0,, natgthsn0 n)); try reflexivity; try assumption.
          destruct (natlehchoice k iter); try assumption.
          simpl in h. rewrite p0 in h.
          contradiction (isirreflnatgth _ h).
    }
    rewrite (@rigrunax1 hq).
    apply IHiter.
  Admitted. (* TODO - WHY slow ?*)


  Lemma gauss_clear_columns_up_to_no_switch_inv3
      ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
      (iter1 iter2 : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
      (i j : ⟦ n ⟧%stn)  (le' : i ≤ j)  (* (p'' : (mat k) = (const_vec 0%hq))*)
      :
      iter1 ≤ iter2
      -> (@gauss_clear_columns_up_to_no_switch n p iter1 mat ) i j = (0%hq)
      -> (@gauss_clear_columns_up_to_no_switch n p iter2 mat ) i j = (0%hq).
  Proof.
    destruct (natlehchoice i j) as [lt | eq]. {try assumption.  }
    2: { intros le H.
         replace j with i in *. 2: {apply subtypePath_prop in eq. rewrite eq. reflexivity. }
         rewrite  gauss_clear_columns_up_to_no_switch_inv4 in *; try assumption. }
    intros le.
    destruct (natlehchoice iter1 iter2) as [lt' | eq]. {assumption. }
    2: { clear le. intros H. rewrite <- H. apply maponpaths_4. symmetry. apply subtypePath_prop. assumption. }
    clear le.
    destruct iter2 as [iter2 p2].
    intros H. revert H. revert lt. revert le'. revert i j.
    revert lt'.
    revert p'.
    unfold is_lower_triangular.
    induction iter2. (* generalize i j first ? *)
    { simpl. intros.  apply fromempty. apply nopathsfalsetotrue. assumption. (*apply p'. assumption.*) }
    intros lowt iter1_lt_siter2. intros i j. intros le. intros lt. intros H (*lt*).
    pose( inv0 := gauss_clear_columns_up_to_no_switch_inv0 ).
    unfold gauss_clear_columns_up_to_no_switch in *.
    assert (iter1_le_iter2 : iter1 ≤ iter2). {apply natlthsntoleh in iter1_lt_siter2. assumption. }
    rewrite nat_rect_step.
    destruct (isdeceqhq _ _).
    - destruct (natlehchoice iter1 iter2) as [lt' | eq]. {assumption. }
      + assert (iter1_lt_iter2 : iter1 < iter2). {assumption. }
      {rewrite  (IHiter2  (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) p2) lowt iter1_lt_iter2  i j); try reflexivity; try assumption. }
      + try rewrite <- eq in gccutns.
        symmetry. etrans.
        { rewrite <- H. reflexivity. }
        revert p0.  revert iter1_lt_siter2. revert lt. revert p2. rewrite <- eq.
        change (pr1 iter1) with (iter1).
        intros.
        apply maponpaths_3.
        apply propproperty.
    - rewrite gauss_clear_column_inv5; try reflexivity; try assumption.
      destruct (natlehchoice iter1 iter2) as [? | eq]. {assumption. }
      2: {unfold is_lower_triangular. intros i' j' ?.
          set (f := nat_rect _ _ _ _).
          set (s := (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) p2)).
          set (f' := f s).
          unfold f', f.
          try rewrite (inv0 n f' p iter1 (iter2,, s) iter1_le_iter2 lowt i' j').
          change 0%rig with 0%hq.
          set (iter2_stn := make_stn (S n) iter2 s).
          change (iter2) with (pr1 iter2_stn).
          rewrite (inv0 n  _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
      }
      intros i' j' lt''.
      destruct (natgthorleh i' j') as [gt | le'].
      + apply fromempty. apply isasymmnatlth in gt; try contradiction; assumption.
      + destruct (natlehchoice i' j') as [lt''' | eq]. {assumption. }
        * symmetry. etrans. { change 0%rig with 0%hq. rewrite <- H. reflexivity. } (* i' j' *)
          assert (iter1_lt_iter2 : iter1 < iter2). {assumption. }
          rewrite  (IHiter2  (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) p2) lowt iter1_lt_iter2 i' j'); try reflexivity; try assumption.
          unfold gauss_clear_columns_up_to_no_switch in inv0.
          destruct (natchoice0 n) as [? | gt]. {rewrite p0 in p. apply isirreflnatgth in p. contradiction. }
          assert (obv'' : 0 < S n). {apply natgthsn0. }
          destruct (natchoice0 iter1) as [z | eqz].
          { rewrite (inv0 n _ p (0,, obv'')); try reflexivity; try assumption. }
          apply natlthtoleh in eqz.
          refine (inv0 n _ gt (0,, obv'') iter1 eqz _ _ _ _ ); assumption.
        * rewrite  (IHiter2); try reflexivity; try assumption.
          rewrite eq in lt''.
          apply isirreflnatlth in lt''.
          apply fromempty; assumption.
  Defined.


  (* This is in a way an invariant for a failure case during elimination;
     if we have constructed an upper triangular matrix,
     this matrix has an inverse iff it's lower triangular transpose has an inverse.
     Working on the transpose, we can turn this into a diagonal matrix,
     and if the input matrix to gccut is lower triangular with a 0 entry on the diagonal,
     we can use elementary row operations to attain a matrix A' with a constant 0 row,
     a witness to non-invertibility. *)
  Lemma gauss_clear_columns_up_to_no_switch_inv2
      ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
      (iter : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
      (*(k : ⟦ n ⟧%stn) (p'' : mat k k = 0%hq)*)
    : coprod
        (∏ i j: ⟦ n ⟧%stn, j < iter ->  j < i
          -> (@gauss_clear_columns_up_to_no_switch n p iter mat) i j = 0%hq)
        (∑ i : ⟦ n ⟧%stn, (@gauss_clear_columns_up_to_no_switch n p iter mat) i = (const_vec 0%hq)).
  Proof.
    destruct iter as [n' lt_n'_n].
    unfold const_vec.
    induction n'.
    { left.  simpl. intros. apply nopathsfalsetotrue in X. contradiction. }
    unfold gauss_clear_columns_up_to_no_switch in *.
    (* assert (obv : n' < S n). {admit. } *)
    set (s :=  (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) ).
    pose (inv0 := gauss_clear_columns_up_to_no_switch_inv0).
    pose( inv4 :=  gauss_clear_columns_up_to_no_switch_inv4).
    destruct (IHn' s) as [IH1 | IH2].
    - rewrite nat_rect_step.
      destruct (isdeceqhq _ _).
      + right.
        use tpair.
        {exact  (n',, lt_n'_n). }
        apply funextfun. intros j.
        destruct (natgthorleh n' j) as [gt | le].
        * rewrite IH1; try reflexivity; try assumption.
        * destruct (natlehchoice n' j). {assumption. }
          -- unfold is_lower_triangular in inv0.
             unfold gauss_clear_columns_up_to_no_switch in inv0.
             set (n'_stn := (make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n))).
             change 0%rig with 0%hq in inv0.
             change n' with (pr1 n'_stn).
             rewrite (inv0 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
          -- pose (inv3 := gauss_clear_columns_up_to_no_switch_inv3).
             unfold gauss_clear_columns_up_to_no_switch in inv3.
             set (n_stn := make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) ).
             change n' with (pr1 n_stn).
             rewrite (inv3 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
             simpl. revert IH1. revert s. revert p0. revert n_stn. revert lt_n'_n. rewrite p1.
             intros.
             rewrite <- p0.
             apply maponpaths.
             apply subtypePath_prop.
             reflexivity.
      + left. intros i j ? ?.
        destruct (natlehchoice j n'). {apply natlthsntoleh in X.  assumption. }
        * symmetry. etrans. { rewrite <- (IH1 i j); try assumption. reflexivity. }
          rewrite gauss_clear_column_inv6; try reflexivity; try assumption.
          rewrite IH1; try reflexivity; try assumption.
        * rewrite gauss_clear_column_inv0; try assumption.
          3: { rewrite p0 in X0. apply X0. }
          2: {apply (pr2 i). }
          rewrite <- gauss_clear_column_step_eq.
          revert IH1. revert s. revert n0. revert X. revert lt_n'_n. rewrite <- p0.
          intros.
          simpl in lt_n'_n.
          replace (stntonat _ j,, lt_n'_n) with j.
          2: { revert X. revert n0. revert IH1. revert s. revert lt_n'_n. (*rewrite  p0.*)
               intros.
               set (rhs := stntonat n j,, lt_n'_n).
               assert (eq : pr1 j = pr1 rhs). { unfold rhs. reflexivity.  }
               rewrite  (subtypePath_prop   eq  ).
               reflexivity.
          }
          apply gauss_clear_column_step_inv1. try assumption.
          2: {apply natgthtoneq. apply X0. }
          unfold gauss_clear_columns_up_to_no_switch in inv4.
          rewrite  (inv4 n _ p (pr1 j,,  (istransnatlth j (S j) (S n) (natgthsnn j) lt_n'_n))); try assumption.
          replace (stntonat _ j,, lt_n'_n) with j in n0; try assumption.
          unfold stntonat. change j with (pr1 j,, pr2 j).
          simpl.
          assert (eq :  (pr2 j) = lt_n'_n). { apply proofirrelevance. apply propproperty. }
          rewrite eq; reflexivity.
    - right.
      rewrite nat_rect_step.
      destruct IH2 as [IH2 IH2p].
      use tpair. {apply IH2.  }
      destruct (isdeceqhq _ _).
      + pose (inv3 := gauss_clear_columns_up_to_no_switch_inv3).
        unfold gauss_clear_columns_up_to_no_switch in * .
        set (n'_stn := make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n)).
        unfold const_vec in inv3.
        change n' with (pr1 n'_stn).
        apply funextfun; intros j.
        destruct (natgthorleh (pr1 IH2) j).
        * try rewrite (inv3 n'_stn). try rewrite IHn'. change (pr1 n'_stn) with n'. unfold s in IH2p.
          rewrite IH2p; reflexivity.
        * rewrite  (inv3 _ _ p n'_stn); try reflexivity; try assumption.
          {try apply isreflnatgeh. }
          destruct IH2 as [IH_idx IH_p].
          clear inv3.
          change n' with (pr1 n'_stn) in IH2p.
          change s with (pr2 n'_stn) in IH2p.
          change (pr1 (IH_idx,, IH_p)) with IH_idx.
          change (pr2 n'_stn) with lt_n'_n.
          try simpl in *; try rewrite IH2p; try apply idpath.
      + apply funextfun. intros j.
        destruct IH2 as [inv rw].
        destruct (natgthorleh n' inv).
        { rewrite gauss_clear_column_inv3.
          change (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) with s.
          rewrite IH2p; reflexivity.
          apply natgthtogeh.
          assumption.
        }
        destruct (natlehchoice n' inv). { assumption. }
        2: { rewrite gauss_clear_column_inv3.
             - change (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) with s.
               rewrite IH2p; reflexivity.
             - change (stntonat _ (inv,, rw )) with inv.
               change (stntonat _ (n',, lt_n'_n)) with n'.
               rewrite p0.
               apply isreflnatgeh.
        }
        rewrite gauss_clear_column_inv0.
        3: { apply h0. }
        2: { simpl. assumption. }
        try rewrite gauss_clear_column_step_eq.
        unfold gauss_clear_column_step'.
        destruct (stn_eq_or_neq _ _).
        { change (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) with s.
          try apply rw.
          revert IH2p.
          set (f := nat_rect  _ _ _).
          simpl.
          intros.
          rewrite IH2p.
          reflexivity.
        }
        unfold gauss_clear_columns_up_to_no_switch in *.
        set (n'_stn := make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n)).
        change n' with (pr1 n'_stn).
        unfold is_lower_triangular in *.
        set (f := nat_rect _  _ _ _).
        set (s' := istransnatlth _ _ _ _).
        set (f' := f (s' lt_n'_n)).
        unfold gauss_add_row.
        rewrite (stn_neq_or_neq_refl).
        rewrite coprod_rect_compute_1.
        replace (f' (inv,, rw) j) with 0%hq.
        2: { unfold f', f. change n' with (pr1 n'_stn) in IH2p.
             change s with (s' lt_n'_n) in IH2p. rewrite IH2p; reflexivity. }
        replace (f' (inv,, rw) (pr1 n'_stn,, lt_n'_n)) with 0%hq.
        2: {unfold f', f. change n' with (pr1 n'_stn) in IH2p.
            change s with (s' lt_n'_n) in IH2p. rewrite IH2p; reflexivity.  }
        rewrite (@riglunax1 hq).
        etrans. {apply maponpaths_2. apply maponpaths.  rewrite (@rigmult0x hq). apply idpath. }
        change 0%rig with 0%hq. replace (- 0)%hq with 0%hq.
        2: {try rewrite (@ringinvunel1 hq ).
            pose (eq := @ringinvunel1 hq).
            change 0%ring with 0%hq in eq.
            change (- 0%hq)%ring with ( - 0%hq)%hq in eq.
            rewrite eq.
            reflexivity.
        }
        rewrite hqmult0x.
        apply idpath.
  Defined.

  Lemma gauss_clear_columns_up_to_no_switch_inv5
      ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
      (iter : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
      (k : ⟦ n ⟧%stn) (p'' : mat k k = 0%hq) :
      k < iter ->
      ∑ i : ⟦ n ⟧%stn, (@gauss_clear_columns_up_to_no_switch n p iter mat) i = (const_vec 0%hq).
  Proof.
    pose (inv2 := gauss_clear_columns_up_to_no_switch_inv2).
    pose (inv0 := gauss_clear_columns_up_to_no_switch_inv0).
    pose (inv3 := gauss_clear_columns_up_to_no_switch_inv3).
    pose (inv4 := gauss_clear_columns_up_to_no_switch_inv4).
    unfold gauss_clear_columns_up_to_no_switch in *.
    intros k_lt_iter.
    unfold gauss_clear_columns_up_to_no_switch.
    destruct iter as [iter lt].
    induction iter. {simpl. apply fromempty. apply negnatlthn0  in k_lt_iter. assumption. }
    rewrite nat_rect_step.
    set (s := (istransnatlth iter (S iter) (S n) (natgthsnn iter) lt)).
    destruct (natlehchoice k iter) as [? | eq]. {apply natlthsntoleh in k_lt_iter. assumption. }
    - destruct (IHiter s) as [IH_idx IH_p]. {assumption. }
      use tpair. {exact IH_idx. }
      destruct (isdeceqhq (mat (iter,, lt) (iter,, lt)) 0%hq).
      { apply IH_p. }
      apply funextfun. intros j.
      About gauss_clear_column_inv5. (* Should be ≤ not < *)
      destruct (natgthorleh IH_idx j).
      + (*rewrite <- IH_p.*)
        set (iter_stn := (make_stn (S n) iter  (istransnatlth iter (n) (S n) lt (natgthsnn n)))).
        set (iter_stn' := (make_stn n iter lt)).
        change (iter,, lt) with iter_stn'.
        assert (obv : isaprop (hProptoType (iter < S n))). {apply propproperty. }
        replace s with (pr2 iter_stn).
        2: {unfold iter_stn.
            rewrite (proofirrelevance _ obv s
          ( pr2 (make_stn (S n) iter (istransnatlth iter n (S n) lt (natgthsnn n)))) ). reflexivity. }
        change iter with (pr1 iter_stn).
        try rewrite (inv4 iter_stn').
        destruct (natgthorleh IH_idx iter_stn').
        2: {rewrite gauss_clear_column_inv3; try assumption.
            change (pr1 iter_stn) with (stntonat _ iter_stn).
            assert (eq : (pr2 iter_stn) = s).
            { apply proofirrelevance; apply propproperty. }
            rewrite eq.
            rewrite <- IH_p.
            reflexivity.
        }
        rewrite gauss_clear_column_inv0; try assumption.
        2: {apply (pr2 IH_idx). }
        unfold gauss_clear_column_step'.
        destruct (stn_eq_or_neq _ _).
        { change (pr1 iter_stn) with (iter).
          assert (eq' : (pr2 iter_stn) = s). { apply proofirrelevance. apply propproperty. }
          rewrite eq'.
          rewrite IH_p.
          reflexivity.
        }
        unfold gauss_add_row.
        set (f := nat_rect _ _ _).
        rewrite (stn_neq_or_neq_refl); rewrite coprod_rect_compute_1.
        set (f' := f _ _).
        replace (f' IH_idx j) with 0%hq.
        2: { unfold f', f.
             change (pr1 iter_stn) with (iter).
             assert (eq' : (pr2 iter_stn) = s).
             { apply proofirrelevance. apply propproperty. }
             rewrite eq'. rewrite  IH_p.
             reflexivity.
        }
        replace (f' IH_idx iter_stn') with 0%hq.
        2: { unfold f', f.
             unfold f', f.
             change (pr1 iter_stn) with (iter).
             assert (eq' : (pr2 iter_stn) = s).
             { apply proofirrelevance. apply propproperty. }
             rewrite eq'. rewrite  IH_p.
             reflexivity.
        }
        rewrite (@riglunax1 hq).
        etrans. { apply maponpaths_2. apply maponpaths. rewrite hqmult0x. reflexivity. }
        etrans. {apply maponpaths_2. apply maponpaths.  apply idpath. }
        change 0%rig with 0%hq. replace (- 0)%hq with 0%hq.
        2: {try rewrite (@ringinvunel1 hq ).
            pose (eq := @ringinvunel1 hq).
            change 0%ring with 0%hq in eq.
            change (- 0%hq)%ring with ( - 0%hq)%hq in eq.
            rewrite eq.
            reflexivity.
        }
        rewrite hqmult0x. reflexivity.
      + destruct (natlehchoice IH_idx j). {assumption. }
        * rewrite  gauss_clear_column_inv5; try reflexivity; try assumption.
          unfold is_lower_triangular; intros.
          set (s' := ((istransnatlth iter (S iter) (S n) (natgthsnn iter) lt))).
          set (iter_stn := (make_stn (S n) iter s')).
          change iter with (pr1 iter_stn).
          change s with (pr2 iter_stn).
          rewrite (inv0 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
        * replace j with (IH_idx). 2: {apply subtypePath_prop in p0. rewrite p0.  reflexivity. }
          try rewrite inv4.
           destruct (natgthorleh IH_idx iter).
           2: {rewrite gauss_clear_column_inv3; try assumption.
               rewrite <- IH_p.
               reflexivity.
           }
          rewrite gauss_clear_column_inv0; try assumption.
          2: {apply (pr2 (IH_idx)). }
          unfold gauss_clear_column_step'.
          unfold gauss_add_row.
          set (f := nat_rect _ _ _).
          destruct (stn_eq_or_neq _ _).
          { rewrite <- IH_p. unfold f. reflexivity. }
          rewrite (stn_neq_or_neq_refl); rewrite coprod_rect_compute_1.
          set (f' := f _ _).
          replace (f' IH_idx (iter,, lt)) with 0%hq. 2: {unfold f'. unfold f. rewrite  IH_p. reflexivity. }
          replace (f' IH_idx IH_idx) with 0%hq. 2: {unfold f'. unfold f. rewrite  IH_p. reflexivity. }
          rewrite (@riglunax1 hq).
          etrans. {apply maponpaths_2.
                   apply maponpaths.
                   rewrite hqmult0x.
                   reflexivity. }
          change 0%rig with 0%hq.
          replace (- 0)%hq with 0%hq.
          2: {try rewrite (@ringinvunel1 hq ).
              pose (eq := @ringinvunel1 hq).
              change 0%ring with 0%hq in eq.
              change (- 0%hq)%ring with ( - 0%hq)%hq in eq.
              rewrite eq.
          reflexivity. }
          rewrite hqmult0x.
          reflexivity.
    - revert k_lt_iter. revert s. revert lt. rewrite <- eq in *.
      intros.
      destruct (isdeceqhq _ _).
      2: {rewrite <- p'' in n0. replace (stntonat _ k,, lt) with k in n0.
          2: {change k with (pr1 k,, pr2 k) at 1.
              assert (eq'  : pr1 k = stntonat n k). {reflexivity. }
              revert s. revert k_lt_iter. revert n0. revert lt.
              change (stntonat n k) with (pr1 k).
              intros.
              assert (eq'' :  lt = (pr2 k)). {apply proofirrelevance; apply propproperty. }
              rewrite eq''.
              reflexivity.
          }
          contradiction.
      }
      destruct (inv2 n mat p (pr1 k,, s)) as [c1 | c2] ; try assumption.
      use tpair. {exact k. }
      apply funextfun. intros j.
      destruct (natgthorleh k j).
      { rewrite c1 ; try reflexivity; try assumption. }
      destruct (natlehchoice k j). {assumption. }
      + set (kstn := make_stn (S n) k (istransnatlth k (S k) (S n) (natgthsnn k) lt)).
        change (stntonat _ k) with (pr1 kstn).
        change s with (pr2 kstn).
        rewrite (inv0 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
      + revert c1. revert s. revert k_lt_iter. revert p0. revert lt.
        replace k with j. 2 : {apply subtypePath_prop in p1. symmetry. rewrite p1. reflexivity.  }
        intros.
        set (j_stn := (make_stn (S n) j ( (istransnatlth j n (S n)  (pr2 j) (natgthsnn n) )))).
        change (stntonat _ j) with (pr1 j_stn).
        assert (eq' : s = (pr2 j_stn)). {apply proofirrelevance; apply propproperty. }
        rewrite eq'.
        rewrite inv4; try assumption.
        rewrite <- p0.
        unfold const_vec.
        apply maponpaths_12; try apply subtypePath_prop; try reflexivity.
  Defined.

  Lemma upper_triangular_iff_transpose_lower_triangular
    { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
    :
    (@is_upper_triangular hq n n mat)
    <->
    (@is_lower_triangular hq n n (transpose mat)).
  Proof.
    unfold  is_upper_triangular,  is_lower_triangular, transpose, flip.
    split.
    - intros inv i j i_lt_j.
      rewrite inv; try assumption; reflexivity.
    - intros inv i j i_gt_j.
      rewrite inv; try assumption; reflexivity.
  Defined.

  Lemma matrix_product_transpose
    { n : nat } (A B : Matrix hq n n)
    :
    (transpose (A ** B)) = ((transpose B) ** (transpose A)).
  Proof.
    intros.
    unfold transpose, flip.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    symmetry; rewrite matrix_mult_eq; unfold matrix_mult_unf.
    apply funextfun. intros i.
    apply funextfun. intros j.
    etrans. {apply maponpaths. apply funextfun. intros ?. rewrite hqmultcomm. reflexivity. }
    reflexivity.
  Defined.

  Lemma invertible_to_transpose_invertible
    { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
    :
    (@matrix_inverse hq n mat)
    (*<*)->
    (@matrix_inverse hq n (transpose mat)).
  Proof.
    assert (eq : transpose (@identity_matrix hq n) = @identity_matrix hq n).
    { unfold transpose. unfold flip.
      apply funextfun; intros ?. apply funextfun; intros ?.
      unfold identity_matrix.
      destruct (stn_eq_or_neq _) as [eq' | neq]; try simpl.
      - symmetry in eq'.
        rewrite (stn_eq_or_neq_left eq'); simpl.
        reflexivity.
      - destruct (stn_eq_or_neq _ _) as [contr | ?].
        2: {simpl. reflexivity. }
        simpl.
        rewrite contr in neq.
        apply isirrefl_natneq in neq.
        contradiction.
    }
    try split.
    - intros inv1.
      destruct inv1 as [inv1 isinv1].
      destruct isinv1 as [isrightinv1 isleftinv1].
      use tpair.
      {exact (transpose inv1). }
      split.
      + rewrite <- matrix_product_transpose in *.
        rewrite isleftinv1.
        assumption.
      + rewrite <- matrix_product_transpose in *.
        rewrite isrightinv1.
        assumption.
  Defined.

  (* Updating vec/b "in place"  *)
  Definition back_sub_step { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n) (b : Vector hq n) (vec : Vector hq n) : Vector hq n.
  Proof.
    intros i.
    set ( m := pr1 i ).
    destruct (nat_eq_or_neq iter i).
    2 : {exact ((*vec*) b i). }
    destruct (natlehchoice (S (pr1 iter)) n) as [? | ?]. {apply iter. }
    - exact (((vec i) * hqmultinv (mat i i)) - ((Σ (mat i ^ (*vec*) b)  - ((*vec*) b  i)* (mat i i))  * (hqmultinv (mat i i) )))%hq.
    - exact ((hqmultinv (mat i i)) * (vec i))%hq.
  Defined.

  (* TODO moderately large cleanup needed - rename temp variables *)
  Lemma back_sub_step_inv0 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (b : Vector hq n) (vec : Vector hq n)
        (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_filled mat):
    (((mat ** (col_vec (back_sub_step iter mat b (*vec*) vec))) iter  = (col_vec vec) iter )).
  Proof.
    intros.
    unfold back_sub_step, col_vec.
    rewrite matrix_mult_eq; unfold matrix_mult_unf, pointwise.
    set (m := n - (S iter)).
    assert (spliteq : n = (S iter) + m ).  (* Could do away with this if iter is ⟦ S n ⟧ instead of ⟦ n ⟧ ? *)
    { unfold m.
      rewrite natpluscomm.
      rewrite minusplusnmm.
      - apply idpath.
      - simpl. exact (pr2 iter).
    }
    generalize iter mat  vec p' p b.
    set (itersucc := (stn_inhabited_implies_succ iter)).
    destruct itersucc as [pr1_ pr2_].
    rewrite pr2_ in *.
    intros iter' mat' vec' filled' is_upper_t' b'.
    apply funextfun. intros x.
    rewrite (@rigsum_dni hq (pr1_)  _ iter').
    rewrite nat_neq_or_neq_refl.
    destruct (natlehchoice (S (Preamble.pr1 iter')) (S pr1_)).
    -   etrans. { apply maponpaths_2; apply maponpaths; reflexivity. }
        etrans.
        { apply maponpaths_2.
          apply maponpaths.
          apply funextfun. intros q.
          unfold funcomp.
          rewrite (nat_eq_or_neq_right (dni_neq_i iter' q)).
          reflexivity.
        }
        rewrite (@rigsum_dni hq ( pr1_)  _ iter').
        (* simpl. unfold dni. unfold di. simpl. *)
        set (f := λ q : (⟦ pr1_ ⟧%stn), _).
        set (a := mat' iter' iter').
        set (b'' := b' iter').
        etrans.
        { apply maponpaths.
          etrans.
          { apply maponpaths.
            rewrite hqmultcomm.
            apply maponpaths.
            rewrite hqmultcomm.
            reflexivity. }
            apply (@ringminusdistr hq a).
        }
        etrans.
        {apply maponpaths.
         apply map_on_two_paths.
         rewrite <- (@rigassoc2 hq).
         rewrite hqisrinvmultinv.
         2: {unfold a.
             apply  filled'. }
             apply (@riglunax2 hq).
             apply maponpaths.
             rewrite <- (@rigassoc2 hq).
             rewrite hqisrinvmultinv. 2: { apply filled'. }
             apply (@riglunax2 hq).
        }
        set (sum := iterop_fun _ _ _).
        clear x.
        assert (eq: ∏ sum b'' a : hq, (sum + b''*a - b''*a)%hq = sum ).
        { clear sum b'' a. intros sum b'' a.
          replace (sum + b'' * a - b'' * a)%hq with (sum + b'' * a + (- b'' * a))%hq.
          - rewrite hqplusassoc.
            replace (b'' * a + - b'' * a)%hq with (b'' * a  - b'' * a)%hq.
            + rewrite hqrminus; apply (@rigrunax1 hq).
            + symmetry.
              rewrite hqpluscomm.
              rewrite hqrminus.
              change (- b'' * a)%hq with ((- b'') * a)%hq.
              replace  (- b'' * a)%hq with (- (b'' *a))%hq.
              * rewrite (hqlminus (b'' * a)%hq).
                reflexivity.
              * rewrite  (@ringlmultminus hq).
                reflexivity.
          - symmetry.
            rewrite hqpluscomm.
            replace  (- b'' * a)%hq with (- (b'' *a))%hq.
            * reflexivity.
            * rewrite  (@ringlmultminus hq).
              reflexivity.
        }
        etrans.
        { do 3 apply maponpaths.
          rewrite (@rigcomm2 hq).
          rewrite eq.
          reflexivity.
        }
        rewrite (@rigcomm1 hq).
        rewrite (@rigassoc1 hq).
        unfold funcomp.
        rewrite hqlminus.
        rewrite hqplusr0.
        apply idpath.
      - rewrite (@zero_function_sums_to_zero hq).
        rewrite (@riglunax1 hq).
        rewrite <- (@rigassoc2 hq).
        rewrite hqisrinvmultinv.
        2 : { apply filled'.  }
        rewrite (@riglunax2 hq).
        reflexivity.
      + simpl.
        apply funextfun. intros q.
        etrans.
        { apply maponpaths_2.
          rewrite is_upper_t'. {reflexivity. }
          unfold dni, di; simpl.
          destruct (natlthorgeh q iter') as [gt | ?].
          { apply gt. }
          apply invmaponpathsS in p0.
          apply fromempty.
          assert (q_ge_iter' : q ≥ (pr1 iter')).
          { apply h. }
          rewrite p0 in q_ge_iter'.
          apply natgehtonegnatlth in q_ge_iter'.
          assert (q_le_iter_absurd : q < pr1_).
          { apply (pr2 q). }
          exact (q_ge_iter' q_le_iter_absurd).
         }
        rewrite (@rigmult0x hq).
        reflexivity.
  Defined.

  Lemma back_sub_step_inv1 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (b : Vector hq n) (vec : Vector hq n) (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_filled mat): ∏ i : ⟦ n ⟧%stn, i ≠ iter ->
    (col_vec (back_sub_step iter mat b vec) i  = ( (col_vec  (*vec*) b)) i).
  Proof.
    intros i ne.
    unfold back_sub_step.
    unfold col_vec.
    apply funextfun. intros j.
    simpl.
    destruct (nat_eq_or_neq iter i) as [eq | ?].
    - rewrite eq in ne.
      apply isirrefl_natneq in ne.
      contradiction.
    - apply idpath.
  Defined.

  Definition transpose_vector {X : UU} {n : nat} (vec : Vector X n)
    := (λ i : (⟦ n ⟧)%stn, vec (dualelement i)).

  Lemma back_sub_step_inv2 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (b : Vector hq n) (vec : Vector hq n) (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_filled mat):
     ∏ i : ⟦ n ⟧%stn, (*i > iter*) i ≥ iter ->
       (mat ** (col_vec b )) i  = (( (col_vec  vec)))  i
    -> (mat ** (col_vec (back_sub_step iter mat b vec))) i  = ((col_vec vec) i).
  Proof.
    intros i lt H.
    unfold transpose, flip in *.
    destruct iter as [iter p''].
    rewrite <- H.
    destruct (natlehchoice iter i). {apply lt. }
      - rewrite matrix_mult_eq.
        apply pathsinv0.
        rewrite matrix_mult_eq.
        unfold matrix_mult_unf.
        rewrite matrix_mult_eq in H.
        unfold matrix_mult_unf in H.
        apply funextfun; intros ?.
        apply maponpaths.
        apply funextfun. intros i'.
        destruct (stn_eq_or_neq i' (iter,, p'')).
        2: { rewrite back_sub_step_inv1; try assumption; reflexivity. }
        replace (mat i i') with 0%hq.
        2: {rewrite p; try reflexivity.
            change (stntonat _ i) with (pr1 i) in lt.
            change (stntonat _ (iter,, p'')) with (iter) in lt.
            replace iter with (pr1 i') in lt.
            2: {rewrite p0. reflexivity. }
            rewrite p0.
            try apply lt.
            apply h.
        }
        do 2 rewrite (@rigmult0x hq); reflexivity.
      -  revert lt. revert p''. rewrite p0.
         intros.
         replace (stntonat _ i,, p'') with i.
         2: { do 2 change (stntonat _ i) with (pr1 i).
              change i with (pr1 i,, pr2 i).
              simpl.
              assert (eq : (pr2 i) = p'').
              { apply proofirrelevance. apply propproperty. }
              rewrite eq. reflexivity.
         }
         rewrite back_sub_step_inv0; try reflexivity; try assumption.
         apply pathsinv0. apply H.

  Defined.

  Lemma back_sub_step_inv3 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (b : Vector hq n) (vec : Vector hq n) (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_filled mat):
     ∏ i : ⟦ n ⟧%stn, i > iter ->
       (mat ** (col_vec b )) i = (mat ** (col_vec (back_sub_step iter mat b vec))) i.
  Proof.
    intros i lt.
    unfold transpose, flip in *.
    destruct iter as [iter p''].
    destruct (natlehchoice iter i). {apply natlthtoleh in lt. apply lt. }
    - rewrite matrix_mult_eq.
      apply pathsinv0.
      rewrite matrix_mult_eq.
      unfold matrix_mult_unf.
      apply funextfun; intros ?.
      apply maponpaths.
      apply funextfun. intros i'.
      destruct (stn_eq_or_neq i' (iter,, p'')).
      2: { rewrite back_sub_step_inv1; try assumption; reflexivity. }
      replace (mat i i') with 0%hq.
      2: {rewrite p; try reflexivity.
          change (stntonat _ i) with (pr1 i) in lt.
          change (stntonat _ (iter,, p'')) with (iter) in lt.
          replace iter with (pr1 i') in lt.
          2: {rewrite p0. reflexivity. }
          rewrite p0.
          try apply lt.
          apply h.
      }
      do 2 rewrite (@rigmult0x hq); reflexivity.
    - rewrite <- p0 in lt.
      apply isirreflnatgth in lt. contradiction.
  Defined.



  (* TODO: document what this is meant to do? *)
  (* TODO fix signature *)
  Definition back_sub_internal
    { n : nat }  (mat : Matrix hq n n) (b : Vector hq n) (vec : Vector hq n) (iter : ⟦ S n ⟧%stn)
    : Vector hq n.
  Proof.
    destruct iter as [iter p].
    induction iter as [ | m IHn] .
    - exact b.
    - assert (p' : m < S n). {apply (istransnatlth _ _ _ (natgthsnn m) p). }
      set (m' := dualelement (m,, p)).
      assert (p'' : (pr1 m') <  S n). {apply (istransnatlth _ _ _  (pr2 m') (natgthsnn n) ). }
      exact (back_sub_step (m') mat (IHn (p')) vec).
  Defined.


  (* TODO  H not even used here ??? *)
  Lemma back_sub_internal_inv0
        { n : nat } (mat : Matrix hq n n) (b : Vector hq n)
        (vec : Vector hq n) (ut : @is_upper_triangular hq _ _ mat)
        (df : diagonal_filled mat) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < (dualelement iter)(* i < iter *)
    -> (((col_vec (back_sub_internal mat b vec iter)))) i = ((col_vec b) i).
  Proof.
    destruct iter as [iter p].
    induction iter.
    { intros i H.
      unfold dualelement in H.
      destruct (natchoice0 (S n)) in H. {clear H. apply negpaths0sx in p0. contradiction. }
      simpl.
      unfold back_sub_internal.
      simpl.
      simpl in H.
      reflexivity. }
    unfold back_sub_internal.
    intros i i_lt_dual.
    rewrite nat_rect_step.
    assert (p': iter < S n). { apply (istransnatlth _ _ _ (natgthsnn iter) p).  }
    assert (lt : i < dualelement (iter,, p')).
    {unfold dualelement in *.
     destruct (natchoice0 (S n)) in *. { pose (contr := (natneq0sx n)). rewrite p0 in contr.
                                         apply isirrefl_natneq in contr. contradiction. }
      simpl in *.
      refine (istransnatgth _ _ _ _ _).
      { set (n' := n - 0 - iter).
        apply natminus1lthn.
        rewrite minus0r.
        apply minusgth0.
        exact p.
      }
      replace (n - 0 - iter - 1) with (n - 0 - (S iter)); try apply i_lt_dual.
      rewrite minus0r.
      rewrite natminusminus.
      replace (S iter) with (iter + 1); try reflexivity.
      rewrite <- plus_n_Sm, natplusr0.
      reflexivity.
    }
    rewrite <- (IHiter p'); try assumption.
    rewrite back_sub_step_inv1; try reflexivity; try assumption.
    2: { unfold dualelement in i_lt_dual.
         unfold dualelement.
         apply natlthtoneq.
         unfold dualelement in *.
         destruct (natchoice0 n).
         {apply fromstn0. clear i_lt_dual. clear lt. rewrite <- p0 in i.
          assumption. }
          destruct (natchoice0 (S n)) in *.
         {simpl. pose (contr := natneqsx0 n). rewrite  p0 in contr.
          apply isirrefl_natneq in contr. contradiction.  }
         simpl in *.
         rewrite minus0r in i_lt_dual.
         replace (S iter) with (iter + 1) in i_lt_dual.
         2: { rewrite <- plus_n_Sm, natplusr0. reflexivity. }
         rewrite natpluscomm in i_lt_dual.
         rewrite <- natminusminusassoc in i_lt_dual. assumption.
         }
    unfold back_sub_internal.
    apply maponpaths_2.
    apply maponpaths.
    apply proofirrelevance; apply propproperty.
  Defined.

  Lemma back_sub_internal_inv1
        { n : nat } (mat : Matrix hq n n) (b : Vector hq n)
        (vec : Vector hq n) (ut : @is_upper_triangular hq _ _ mat)
        (df : diagonal_filled mat) (iter : ⟦ S n ⟧%stn)
    : ∏ i : ⟦ n ⟧%stn,
      i ≥ (dualelement iter)
      -> (((col_vec (back_sub_internal mat b vec iter)))) i
         = (col_vec (back_sub_step i mat b vec)) i.
  Proof.
    destruct iter as [iter p'].
    unfold back_sub_internal.
    induction iter.
    { intros ? H. unfold dualelement in H.
      destruct (natchoice0 (S n)) in H.
      { pose (contr := natneqsx0 n).
        rewrite p in contr.
        apply isirrefl_natneq in contr.
        contradiction. }
      rewrite coprod_rect_compute_2 in H.
      try rewrite minus0r in H.
      assert (eq' : ∏ n : nat, S n = (n + 1)%nat).
      { intros. rewrite <- plus_n_Sm, natplusr0. apply idpath.  }
      unfold make_stn in H.
      try rewrite minus0r in H.
      assert (H' : (pr1 i) ≥ (S n - 1 - (stntonat _ (0,, p')))).
      {apply H. }
      try rewrite minus0r in H'.
      rewrite eq' in H'.
      rewrite plusminusnmm in H'.
      apply natgehtonegnatlth in H'.
      pose (contr := (pr2 i)).
      contradiction.
    }
    intros i eq.
    assert (obv:  dualelement (iter,, p') < n).
    { unfold dualelement.
      unfold dualelement in eq.
      destruct (natchoice0 n).
      { apply fromstn0. rewrite p. assumption. }
      rewrite coprod_rect_compute_2.
      unfold make_stn.
      apply minusgth0inv. (* TODO minusn1 can be replaced by this *)
      simpl.
      rewrite  natminusminus.
      rewrite <- natminusminusassoc.
      rewrite minusgth0inv; try reflexivity.
      rewrite minus0r.
      apply minusgth0.
      rewrite natminusminusassoc.
      apply natminuslthn; try assumption.
      reflexivity.
    }
    rewrite nat_rect_step.
    About back_sub_step_inv2. (* Retains a solution *)
    destruct (natlehchoice (dualelement (S iter,, p')) (i)). {assumption. }
    - set (iter_stn := (make_stn (S n) iter (istransnatlth iter (S iter) (S n) (natgthsnn iter) p'))).
      change ((istransnatlth iter (S iter) (S n) (natgthsnn iter) p')) with (pr2 iter_stn).
      change iter with (pr1 iter_stn).
      rewrite back_sub_step_inv1; try assumption.
      2: { clear IHiter. unfold dualelement in *.
         destruct (natchoice0 n). {apply fromstn0. rewrite p. assumption. }
         destruct (natchoice0 (S n)) in *. { pose (contr := (natneq0sx n)). rewrite p in contr.
             apply isirrefl_natneq in contr. contradiction. }
         simpl.
         pose (contr := natneqsx0 n).
         apply natgthtoneq. simpl in h.
         rewrite minus0r in h.
         assert (eq' : ∏ n : nat, S n = (n + 1)%nat).
         { intros. rewrite <- plus_n_Sm, natplusr0. apply idpath.  }
         rewrite natminusminus.
         rewrite natpluscomm. rewrite <- eq'.
         assumption.
      }
      rewrite IHiter; try reflexivity; try assumption.
      { unfold dualelement in *;
        clear IHiter.
        destruct (natchoice0 (S n)) in *. { pose (contr := (natneq0sx n)). rewrite p in contr.
                                            apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2.
        unfold make_stn.
        rewrite coprod_rect_compute_2 in h.
        apply natgthtogehp1 in h.
        destruct (natchoice0 n). {apply fromstn0. rewrite p. assumption. }
        unfold make_stn in h.
        refine (istransnatgeh _ _ _ _ _).
        { apply h. }
        cbn.
        rewrite minus0r.
        assert (eq' : ∏ n : nat, S n = (n + 1)%nat).
        { intros. rewrite <- plus_n_Sm, natplusr0. apply idpath.  }
        rewrite eq'.
        rewrite <- natminusminusassoc.
        set (n' := n - iter).
        rewrite minusplusnmm.
        2: { simpl.
             apply minusgth0.
             exact p'.
        }
        unfold n'.
        admit.
      }
    - admit.
  Abort.


  Lemma back_sub_internal_inv2
        { n : nat } (mat : Matrix hq n n) (b : Vector hq n)
        (vec : Vector hq n) (ut : @is_upper_triangular hq _ _ mat)
        (df : diagonal_filled mat) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i ≥  (dualelement iter)
    -> ((mat ** (col_vec (back_sub_internal mat b vec iter)))) i = ( ( (col_vec vec))) i.
  Proof.
    unfold transpose, flip.
    intros i i_le_iter.
    unfold back_sub_internal.
    destruct iter as [iter p].
    induction iter as [eq | ?].
    { apply fromempty.
      unfold dualelement in i_le_iter.
      destruct (natchoice0 (S n)) in i_le_iter.
      {apply fromempty. clear i_le_iter. apply negpaths0sx in p0; contradiction. }
      unfold make_stn in i_le_iter.
      rewrite coprod_rect_compute_2 in i_le_iter.
      simpl in i_le_iter.
      do 2 rewrite minus0r in i_le_iter.
      pose (contr := pr2 i); simpl in contr.
      change (stntonat _ i) with (pr1 i) in i_le_iter.
      apply natgthtonegnatleh in contr.
      contradiction.
    }
    (*assert (obv : iter < S n). {admit. }*)
    rewrite nat_rect_step.
    destruct (natlehchoice (dualelement (iter,, p)) (i)).
      { unfold dualelement in i_le_iter.
        unfold dualelement.
        destruct (natchoice0 n) as [p0 | ?]. {apply fromstn0. rewrite p0. assumption. }
        destruct (natchoice0 (S n)) as [p0 | ?] in *.
        { pose (contr := (natneq0sx n)). rewrite <- p0 in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2 in *.
        unfold make_stn in *.
        simpl in p.
        simpl.
        assert (eq' : ∏ n : nat, S n = (n + 1)%nat).
        { intros. rewrite <- plus_n_Sm, natplusr0. apply idpath.  }
        simpl in i_le_iter.
        rewrite eq' in i_le_iter.
        rewrite minus0r in i_le_iter.
        rewrite natpluscomm in i_le_iter.
        rewrite <- natminusminus in i_le_iter.
        symmetry.
        change (iter,, _) with iter.
        rewrite i_le_iter; reflexivity.
      }
    - rewrite back_sub_step_inv2; try reflexivity; try assumption.
      { unfold dualelement. unfold dualelement in h.
        destruct (natchoice0 n) as [p0 | ?]. {apply fromstn0. rewrite p0. assumption. }
        rewrite coprod_rect_compute_2 in *.
        apply natgthtogeh.
        assumption.
      }
      rewrite IHiter; try reflexivity.
      { unfold dualelement.
        destruct (natchoice0 (S n)) as [p0 | ?] in *.
        { pose (contr := (natneq0sx n)). rewrite <- p0 in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2.
        unfold dualelement in h.
        destruct (natchoice0 n) as [p0 | ?]. {apply fromstn0. rewrite p0. assumption. }
        rewrite coprod_rect_compute_2 in *.
        simpl; simpl in h.
        rewrite minus0r.
        apply natgthtogehsn in h.
        rewrite pathssminus in h.
        2: { rewrite pathssminus.
             - rewrite PAdics.lemmas.minussn1.
               exact p.
             - simpl; apply h1. }
        assert (e : n = S (n - 1)).
        { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
          apply pathsinv0. apply minusplusnmm. assumption. }
        rewrite <- e in h.
        apply h.
      }
    - assert (eq: (dualelement (iter,, p)) = i).
      { unfold dualelement in *.
           try rewrite  p0.
           destruct (natchoice0 n) as [? | ?]. {apply fromstn0. rewrite p1. assumption. }
           rewrite coprod_rect_compute_2 in *.
           unfold make_stn in *; simpl in *.
           change (stntonat _ i) with (pr1 i) in p0.
           symmetry in p0.
           change i with (pr1 i,, pr2 i).
           set (rhs := make_stn n (n - 1 - iter) (StandardFiniteSets.dualelement_lt iter n h)).
           change (n - 1 - iter) with (pr1 rhs).
           try rewrite <- p0. try apply p0. try assumption.
           clear IHiter.
           simpl.
           simpl in p0.
           apply subtypePath_prop.
           rewrite p0.
           reflexivity.
      }
      rewrite eq.
      rewrite back_sub_step_inv0; try reflexivity; try assumption.
  Defined.

  Lemma hqplusminus (a b : hq) : (a + b - b)%hq = a.
  Proof.
    replace (a + b - b)%hq with (a + b + (- b))%hq.
    - rewrite hqplusassoc.
      replace (b + - b)%hq with (b  - b)%hq.
      + rewrite hqrminus; apply (@rigrunax1 hq).
      + reflexivity.
   - symmetry.
     rewrite hqpluscomm.
     reflexivity.
  Defined.

  Lemma zero_row_to_non_invertibility { n : nat } (A : Matrix hq n n)
        (i : ⟦ n ⟧%stn) (zero_row : A i = (const_vec 0%hq)) :
    (@matrix_inverse hq n A) -> empty.
  Proof.
    intros invA.
    destruct invA as [inv isinv].
    destruct isinv as [isrightinv isleftinv]. (* TODO fix order *)
    assert (∏ i j : ⟦ n ⟧%stn, (A ** inv) i j = identity_matrix i j).
    { intros.  rewrite isrightinv. reflexivity. }
    destruct (natchoice0 n) as [eq | gt].
    { apply fromstn0. clear zero_row. rewrite <- eq in i. assumption. }
    assert (contr : (A ** inv) i i = 0%hq).
    { rewrite matrix_mult_eq. unfold matrix_mult_unf.
      rewrite zero_function_sums_to_zero. {reflexivity. }
      apply funextfun. intros k.
      replace (A i k) with 0%hq.
      { apply (@rigmult0x hq). }
      rewrite zero_row. reflexivity.
    }
    pose (id_ii := (@id_mat_ii hq n)).
    rewrite isrightinv in contr.
    rewrite id_ii in contr.
    change 1%rig with 1%hq in contr.
    pose (t1 := intpart 1%hq).
    pose (t2 := intpart 0%hq).
    assert (contr' : t1 != t2).
    {apply hzone_neg_hzzero. }
    unfold t1, t2 in contr'.
    rewrite contr in contr'.
    contradiction.
  Defined.


  Lemma inverse_iff_transpose_inverse { n : nat } (A : Matrix hq n n) :
        (@matrix_inverse hq _ A) <-> (@matrix_inverse hq _ (transpose A)).
  Proof.
  Admitted.


  Lemma upper_triangular_0_in_diagonal_to_non_invertible
        {n : nat} (A : Matrix hq n n) (k : ⟦ n ⟧%stn)
        (p : A k k = 0%hq) (p' : @is_upper_triangular hq _ _ A)
    : (@matrix_inverse hq _ A) -> empty.
  Proof.
    intros H. apply inverse_iff_transpose_inverse in H.
    assert (@is_lower_triangular hq n n (transpose A)). {admit. }
    unfold is_lower_triangular in X.
    remember H as H'. clear HeqH'.
    destruct H' as [inv is_right_left_inv].
    destruct is_right_left_inv as [is_right_inv is_left_inv].
    destruct (natchoice0 n) as [? | gt]. {admit. }
    set (x := make_stn n (n - 1) (natminus1lthn n gt)).
    destruct (isdeceqhq (A x x) 0%hq) as [eq0 | neq0].
    { apply (zero_row_to_non_invertibility A x).
  Abort.


  Lemma diagonal_nonzero_iff_transpose_nonzero
    { n : nat } (A : Matrix hq n n)
    :
    diagonal_filled A
    <->
    (diagonal_filled (transpose A)).
  Proof.
    split ; intros H; unfold diagonal_filled, transpose, flip; apply H.
  Defined.

  Lemma upper_triangular_transpose_is_lower_triangular
    { n : nat } (A : Matrix hq n n)
    (H: @is_upper_triangular hq n n A)
    :
    (@is_lower_triangular hq n n (transpose A)).
  Proof.
    intros i j lt; unfold is_upper_triangular; apply H; assumption.
  Defined.

  (* TODO realize this better using the elimination procedure invariants *)
  Lemma invertible_upper_triangular_to_diag_filled { n : nat } (A : Matrix hq n n)
        (p : @is_upper_triangular hq n n A)
        (p': @matrix_inverse hq n A)
        (B : (@matrix_inverse hq n A))
    : (@diagonal_filled n A).
  Proof.
    apply diagonal_nonzero_iff_transpose_nonzero.
    set (At := (λ y x : (⟦ n ⟧)%stn, A x y)).
    assert (@is_lower_triangular hq n n At).
    { apply upper_triangular_transpose_is_lower_triangular. assumption. }
    unfold diagonal_filled.
    intros i.
    destruct (isdeceqhq (At i i) 0%hq) as [contr | ne].
    2: { assumption. }
    apply fromempty.
    destruct (natchoice0 n) as [contr' | gt]. {apply fromstn0. rewrite contr'; exact i. }
    set (M :=  @clear_columns_up_to_no_switch_as_left_matrix n gt (n,, natgthsnn n) A).
    assert (invertible : matrix_inverse (M ** A)).
    { apply inv_matrix_prod_is_inv; try assumption.
      apply clear_columns_up_to_matrix_no_switch_invertible.
      apply i. (* TODO remove unnecessary argument *)
    }
    pose (inv := gauss_clear_columns_up_to_no_switch_inv5).
    pose (contr' := inv n At gt (n,, natgthsnn n) X i contr (pr2 i)).
    destruct contr' as [idx contr'].
    set ( At' := gauss_clear_columns_up_to_no_switch gt (n,, natgthsnn n) At).
    pose (noninv := @zero_row_to_non_invertibility n At' idx contr').
    pose (is_inv_at' := @inv_matrix_prod_is_inv).
    pose (@clear_columns_up_to_no_switch_as_left_matrix).
    try contradiction.
  Admitted.


  (* TODO do this one for clear_column (no prime ?) *)
  Lemma clear_column_eq_matrix_def { n : nat } (iter : ⟦ S n ⟧%stn)
     (k_i k_j : (⟦ n ⟧%stn)) (mat : Matrix hq n n) :
     ((gauss_clear_column_as_left_matrix iter mat k_i k_j) ** mat )
   =  gauss_clear_column_old mat k_i k_j iter.
  Proof.
    intros.
    (* rewrite <- gauss_clear_column_eq'. *)
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - apply matlunax2.
    - rename IHpr1_ into IHpr1_'.
      remember IHpr1_' as IHpr1_.
      unfold gauss_clear_column_old.
      unfold gauss_clear_column_old in IHpr1_'.
      unfold gauss_clear_column_as_left_matrix.
      unfold gauss_clear_column_as_left_matrix in IHpr1_'.
      rewrite nat_rect_step.
      rewrite nat_rect_step.
      rewrite  gauss_clear_column_step_eq.
      destruct (natgthorleh pr1_ k_i).
      2: { rewrite matlunax2.
           rewrite IHpr1_'.
           induction pr1_.
           - simpl. apply idpath.
           - rewrite nat_rect_step.
             destruct (natgthorleh pr1_ k_i).
             + apply natgehsntogth in h.
               apply fromempty. apply (isasymmnatgth _ _  h h0).
             + reflexivity.
      }
      rewrite matrix_mult_assoc.
      rewrite <- IHpr1_'.
      set (x := nat_rect _ _ _ _).
      try rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _).
      { apply fromempty. apply neggth_logeq_leh in h; try assumption.
        rewrite <- p. apply isreflnatgeh.  }
      rewrite add_row_mat_elementary.
      2 : {apply issymm_natneq. apply natgthtoneq. assumption. }
      apply pathsinv0.
      apply maponpaths.
      etrans.
      { unfold x.
        set (x' := ((nat_rect _ _ _ ) pr1_ )).
        set (x'' := x' (istransnatlth pr1_ (S pr1_) (S n) (natlthnsn pr1_) pr2_)).
        replace (hqmultinv (@matrix_mult hq _  _ x'' _ mat k_i k_j)%hq) with (hqmultinv (mat k_i k_j)%hq).
        - reflexivity.
        - clear HeqIHpr1_ IHpr1_.
          clear x.
          clear IHpr1_'.
          induction pr1_.
          {apply fromempty. apply  negnatgth0n in h; assumption. }
          unfold x'', x'.
          rewrite nat_rect_step.
          destruct (natgthorleh pr1_ _).
          2 : {rewrite matlunax2.
               set (f := @gauss_clear_column_as_left_matrix_inv0 n ).
               unfold gauss_clear_column_as_left_matrix  in f.
               symmetry.
               assert (obv: S pr1_ < S n). { apply (istransnatlth _ _ _ pr2_ (natgthsnn (S n)) ). }
               set (f' := @gauss_clear_column_as_left_matrix_inv1 n).
               unfold gauss_clear_column_as_left_matrix in f'.

               rewrite f'; try reflexivity; apply isreflnatleh.
          }
          set (f := @gauss_clear_column_as_left_matrix_inv1 n ).
          unfold gauss_clear_column_as_left_matrix  in f.
          assert (obv: S pr1_ < S n). { apply (istransnatlth _ _ _ pr2_ (natgthsnn (S n)) ). }
          rewrite (IHpr1_ obv); try assumption.
          rewrite f. 2: {apply isreflnatleh. }

          rewrite matrix_mult_assoc.
          rewrite add_row_mat_elementary. 2: {apply issymm_natneq. apply natgthtoneq; assumption. }
          rewrite gauss_add_row_inv0.
          2: { apply natgthtoneq. assumption. }

          set (f' := @gauss_clear_column_as_left_matrix_inv1 n ).
          unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
          rewrite f'; try reflexivity.
          apply isreflnatgeh.
          apply natgthtoneq.
          assumption.
      }
      induction pr1_.
      + {apply fromempty. apply negnatgth0n in h. assumption. }
      + unfold x.
        rewrite nat_rect_step.
        destruct (natgthorleh _ _).
        2: {rewrite matlunax2.
          set (f' := @gauss_clear_column_as_left_matrix_inv0 n ).
          unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
          rewrite f'; try reflexivity.
          apply natlehnsn.
        }
        rewrite matrix_mult_assoc.
        rewrite add_row_mat_elementary.
        2: {apply natgthtoneq in h1. apply issymm_natneq. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply issymm_natneq.
            apply natgthtoneq.
            apply natgthsnn. }
        unfold x in IHpr1_0.
        set (f := @gauss_clear_column_as_left_matrix_inv0 n ).
        unfold gauss_clear_column_as_left_matrix  in f.
        rewrite f.
        2: {apply natlehnsn.  }
        apply idpath.
  Defined.

  Lemma clear_row_eq_matrix_def { n : nat }
     (mat : Matrix hq n n) (r : ⟦ n ⟧%stn) :
     ((gauss_clear_row_as_left_matrix mat r) ** mat )
   =  gauss_clear_row mat r.
  Proof.
    intros.
    unfold gauss_clear_row, gauss_clear_row_as_left_matrix.
    destruct (natchoice0 n) as [contr_eq | ?]. {apply fromstn0. rewrite contr_eq. assumption. }
    destruct (pr2 (select_uncleared_column mat r h)).
    2: { apply matlunax2. }
    rewrite <- clear_column_eq_matrix_def.
    rewrite <- switch_row_mat_elementary.
    rewrite  matrix_mult_assoc.
    reflexivity.
  Defined.

  Lemma gauss_clear_rows_up_to_as_matrix_eq  { n : nat } (iter : ⟦ S n ⟧%stn)
    (mat : Matrix hq n n) (p : n > 0) :
    ((@clear_rows_up_to_as_left_matrix_internal _ mat p iter) ** mat)
      = (gauss_clear_rows_up_to_internal  mat p iter).
  Proof.
    intros.
    unfold clear_rows_up_to_as_left_matrix,
           gauss_clear_rows_up_to_internal,
           clear_rows_up_to_as_left_matrix_internal,
           gauss_clear_rows_up_to_internal.
    destruct iter as [iter p'].
    induction iter as [| iter IH ]. {simpl. rewrite matlunax2. apply idpath. }
    do 2 rewrite nat_rect_step.
    rewrite <- IH.
    rewrite <- clear_row_eq_matrix_def.
    rewrite <- matrix_mult_assoc.
    rewrite IH.
    reflexivity.
  Defined.

  Lemma gauss_clear_columns_up_to_no_switch_as_matrix_eq  { n : nat } (iter : ⟦ S n ⟧%stn)
    (mat : Matrix hq n n) (p : n > 0) :
    ((@clear_columns_up_to_no_switch_as_left_matrix _ p iter mat) ** mat)
    = (gauss_clear_columns_up_to_no_switch p iter mat).
  Proof.
    intros.
    unfold clear_columns_up_to_no_switch_as_left_matrix, gauss_clear_columns_up_to_no_switch,
           clear_columns_up_to_no_switch_as_left_matrix_internal.
    destruct iter as [iter p'].
    induction iter. {simpl. rewrite matlunax2. apply idpath. }
    do 2 rewrite nat_rect_step.
    unfold clear_columns_up_to_no_switch_as_left_matrix_internal in *.
    rewrite <- IHiter.
    set (inner_expr := nat_rect _ _ _ _).
    rewrite <- clear_column_eq_matrix_def.
    repeat rewrite matrix_mult_assoc.
    destruct (isdeceqhq _ _).
    - reflexivity.
    - rewrite matrix_mult_assoc.
      rewrite IHiter.
      reflexivity.
  Defined.

  (* output: a solution [x] to [mat ** x = vec] (if one exists?) *)
  (* TODO: what conditions on [mat] are needed to ensure this is a solution? *)
  Definition back_sub { n : nat } (mat : Matrix hq n n) (vec : Vector hq n) : Vector hq n.
  Proof.
    intros.
    destruct (natchoice0 n) as [n_eq_0 | n_gt_0].
    - exact vec.
    - exact (back_sub_internal mat vec vec (n,, natgthsnn n)).
  Defined.

  Lemma back_sub_inv0 { n : nat } (mat : Matrix hq n n) (b vec : Vector hq n)
        (ut : @is_upper_triangular hq _ _ mat)
    (df: diagonal_filled mat) : (mat ** (col_vec (back_sub mat vec))) = (col_vec vec).
  Proof.
    intros.
    unfold back_sub.
    destruct natchoice0 as [p | ?].
    { apply funextfun. intros i. apply fromstn0. rewrite p. simpl. assumption. }
    apply funextfun; intros i.
    try apply back_sub_internal_inv0; try assumption.
    apply back_sub_internal_inv2; try assumption.
    unfold dualelement.
    destruct (natchoice0 (S n)). { apply fromempty. apply negpaths0sx in p. assumption. }
    simpl.
    rewrite minus0r.
    rewrite minusnn0.
    reflexivity.
  Defined.

  (* Construct the inverse, if additionally mat is upper triangular with non-zero diagonal *)
  Definition upper_triangular_inverse_construction
    { n : nat } (mat : Matrix hq n n) (vec : Vector hq n)
    : Matrix hq n n.
  Proof.
    destruct (natchoice0 n).  { unfold Matrix, Vector. intros i. apply fromstn0. rewrite p. assumption. }
    set (ret :=  (transpose (λ i : ⟦ n ⟧%stn, (back_sub mat (@stdb_vector hq n i))))).
    apply ret.
  Defined. (* TODO remove n -> S n' *)

  Lemma col_vec_to_veq_eq { X : rig } { n : nat } (v1 v2 : Vector X n)
    : col_vec v1 = col_vec v2 -> v1 = v2.
  Proof.
    intros H.
    unfold col_vec in H.
    pose (H' := @isinclfromstn1).
    pose (@weqbfun).
    pose (hmm := @isweqinvmap).
  Admitted.

  Lemma col_vec_mult_eq { X : rig } { m n : nat } (mat : Matrix X m n) (v : Vector X n)
    : matrix_mult mat (col_vec v) = (col_vec (λ i : ⟦ m ⟧%stn, (iterop_fun 0%rig op1 ( (mat i) ^ (v ))))).
  Proof.
  Admitted.

  Definition upper_triangular_inverse_is_inverse
    { n : nat } (mat : Matrix hq n n) (vec : Vector hq n)
    (ut : @is_upper_triangular hq _ _ mat)
    (df: diagonal_filled mat)
    :
    (mat ** (upper_triangular_inverse_construction mat vec (*ut df*))) = (@identity_matrix hq n).
  Proof.
    apply funextfun; intros i.
    unfold upper_triangular_inverse_construction.
    destruct (natchoice0 _) as [eq | ?]. { apply fromstn0. rewrite eq; assumption. }
    unfold transpose, flip.
    unfold identity_matrix.
    pose (@back_sub_inv0).
    apply funextfun; intros j.
    destruct (stn_eq_or_neq i j) as [eq | neq].
    - rewrite coprod_rect_compute_1.
      rewrite eq.
  Abort.

  Definition upper_triangular_inverse
    { n : nat } (mat : Matrix hq n n) (b vec : Vector hq n) (ut : @is_upper_triangular hq _ _ mat)
    (df: diagonal_filled mat) : Matrix hq n n.
  Proof.
  Abort.

  Definition gaussian_elimination_1 {n : nat} (A : Matrix hq n n) (b : Vector hq n): Matrix hq n n.
  Proof.
    destruct (natchoice0 n) as [? | p]. (* TODO resolve *)
    { exact A. }
    (* TODO equivalent row operations on b *)
    set (A' := (clear_rows_up_to_as_left_matrix A p (n,, natgthsnn n))).
    exact A'.
  Defined.

  Definition gaussian_elimination_2 {n : nat} (A : Matrix hq n n) (b : Vector hq n): Vector hq n.
  Proof.
    destruct (natchoice0 n) as [? | p]. (* TODO resolve *)
    { exact b. }
    (* TODO equivalent row operations on b *)
    set (A' := (clear_rows_up_to_as_left_matrix A p (n,, natgthsnn n)) ** A).
    set (x := back_sub A' ( b ) ).
    exact x.
  Defined.

  Definition gaussian_elimination {n : nat} (A : Matrix hq n n) (b : Vector hq n): Matrix hq n n ×  Vector hq n.
  Proof.
    exact ((gaussian_elimination_1 A b)
             ,, gaussian_elimination_2 A b).
  Defined.

  Lemma gauss_inv_upper_triangular' {n : nat} (mat : Matrix hq n n) (*(p : diagonal_filled mat)*):
    @is_upper_triangular hq n n (gauss_clear_all_row_segments mat ).
  Proof.
    intros i j i_gt_j.
    unfold gauss_clear_all_row_segments.
    destruct (natchoice0 n) as [n0 | n_gt_0].
    { simpl. clear i_gt_j. generalize i. rewrite <- n0 in i. apply (fromstn0 i). }
    simpl.
  Abort.

  (*Lemma gauss_clear_all_column_segments_eq { n : nat } (mat : Matrix hq n n):
    (gauss_clear_all_row_segments_as_left_matrix mat ** mat)
    = gauss_clear_all_row_segments mat.
  Proof.
    unfold gauss_clear_all_column_segments_by_left_mult,
    gauss_clear_all_column_segments.
    destruct natchoice0 as [eq | ?].
    {rewrite matrix_mult_eq. unfold matrix_mult_unf. apply funextfun.
     intros i. apply fromstn0. rewrite eq. assumption. }
    rewrite <- gauss_clear_columns_up_to_as_matrix_eq.
    apply idpath.
  Defined.*)

  (* The full procedure returns invertible L s.t. L ** A is upper triangular *)
  (*Lemma gaussian_elimination_inv0 {n : nat} (A : Matrix hq n n) (b : Vector hq n)
    : @is_upper_triangular hq n n ( (gaussian_elimination_1 A b) ** A)
        × (@matrix_inverse hq n (gaussian_elimination_1 A b)).
  Proof.
    unfold gaussian_elimination_1.
    intros.
    set (prop := @gauss_inv_upper_triangular n A).
    rewrite <- gauss_clear_all_column_segments_eq in prop.
    unfold gauss_clear_all_column_segments in prop.
    use tpair.
    - intros.
      apply prop.
    - simpl.
      unfold gaussian_elimination_1.
      destruct natchoice0.
      { unfold matrix_inverse.  use tpair.
        - exact A.
        - use tpair.
          + apply funextfun. intros i. apply fromstn0. rewrite p. assumption. (* TODO p ?*)
          + simpl. apply funextfun.  intros i. apply fromstn0. rewrite p. assumption.
      }
      apply clear_columns_up_to_matrix_invertible.
      exact (0,, h). (* TODO remove superfluous argument. *)
  Defined.*)

    (* The full procedure finds a inverse of A, if any such exists. *)
  Lemma gaussian_elimination_inv1 {n : nat} (A : Matrix hq n n) (b : Vector hq n)
    :  (@matrix_inverse hq n A)
       -> ((gaussian_elimination_1 A b)
       **  upper_triangular_inverse_construction ((gaussian_elimination_1 A b) ** A) b
       **  A)
       =   @identity_matrix hq n.
  Proof.
  Abort.


  (* A invertible =>  We can solve A ** x = b   *)
  Lemma gaussian_elimination_inv2 {n : nat} (A : Matrix hq n n) (b : Vector hq n)
    : (@matrix_inverse hq n A) ->
      ((col_vec (gaussian_elimination_2 (gaussian_elimination_1 A b) b))) = col_vec b.
  Proof.
    intros H1.
    unfold gaussian_elimination_1, gaussian_elimination_2.
    destruct natchoice0.
    { admit. }
    try set (prop := @gaussian_elimination_inv0 n A b).
    pose (@back_sub_inv0).
    (* apply invertible_upper_triangular_to_diag_filled. *)
    (* apply inv_matrix_prod_is_inv; assumption. *)
  Admitted.


  (*Lemma gaussian_elimination_inv3 {n : nat} (A : Matrix hq n n) (b : Vector hq n) :
    (@matrix_inverse hq n A)
     ->
    (upper_triangular_inverse_construction (gaussian_elimination_1 A b))
     ** (gaussian_elimination_1 A b)
     ** A
     = identity_matrix.
  Proof.*)


End Gauss.



Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.
  Local Notation Σ := (iterop_fun 0%hz op1).


  Local Notation "A ** B" := (@matrix_mult hz _ _ A _ B) (at level 80).

  Definition mat_to_square_mat { m n : nat } (mat : Matrix I m n) : Matrix I (min m n) (min m n).
  Proof.
    intros.
    (* exact (λ i j : ⟦min m n⟧%stn, mat (minabstn_to_astn i) (minabstn_to_bstn j)). *)
  Abort.

  (* Such code might go intro Matrix.v *)
  Definition is_smithnf { m n : nat } (A : Matrix I m n) :
    ∑ (S : Matrix I m m), ∑ (T : Matrix I n n),
    @is_diagonal I m n (S ** A ** T) ×
    ∏ (i j : ⟦ min n m ⟧%stn), i < j ->
    hzdiv (A (minabstn_to_bstn i) (minabstn_to_astn i))
    (A (minabstn_to_bstn j) (minabstn_to_astn i)).
  Abort.

  Definition MinAij {m n : nat} (A : Matrix I m n) (s : nat) (p : s < min m n) : I.
  Proof.
  Abort.


End SmithNF.


Section SmithNFOps.


End SmithNFOps.


Section SmithNFAlgs.

End SmithNFAlgs.
