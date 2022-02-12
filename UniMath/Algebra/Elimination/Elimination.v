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


Section LeadingEntry.

  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition is_leading_entry {n : nat} (v : Vector hq n) (i_1 : ⟦ n ⟧%stn) :=
      (0%hq != v i_1) × (∏ i_2 : ⟦ n ⟧%stn, i_2 < i_1 -> 0%hq = (v i_2)).
      (*(∏ i_2 : ⟦ n ⟧%stn, i_2 < i_1 -> (v i_2) = 0%hq).*)

  Definition is_leading_entry_dual {n : nat} (v : Vector hq n) (i_1 : ⟦ n ⟧%stn) :=
      (0%hq != v i_1) × (∏ i_2 : ⟦ n ⟧%stn, i_1 < i_2 -> (v i_2) = 0%hq).

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
    destruct (leading_entry_compute_dual_internal
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) iter) as [s | ?].
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
    leading_entry_compute_dual_internal 
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn n) = just i_2.
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
    intros i H1 H2.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      apply negnatlthn0 in H1.
      contradiction.
    - rewrite nat_rect_step.
      destruct (isdeceqhq _ _) as [eq | ?]. 2: {simpl. unfold just. apply negpathsii1ii2. }
      simpl.
      destruct (nat_eq_or_neq i (pr1_)) as [eq' | ?].
      2: { simpl. apply IHpr1_.
           assert (k_lt_pr1_ : i ≤ pr1_).  {apply natlthsntoleh; assumption.  }
           apply (natleh_neq k_lt_pr1_ h).
      }
      simpl in H2.
      simpl in eq'.
      apply fromempty.
      rewrite eq in H2.
      assert (absurd : vec i = vec (pr1_,, pr2_)).
      { apply maponpaths.
        apply subtypePath_prop.
        apply eq'.
      }
      rewrite absurd in H2.
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
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - simpl.
      intros.
      contradiction.
    - rewrite nat_rect_step.
      destruct (isdeceqhq _ _) as [eq0 | ?].
      2 : { intros ?. use tpair.
            { exact (iter ,, p). }
            use tpair. {simpl. reflexivity. }
            use tpair.
            - apply (natgthsnn iter).
            - simpl.
              assumption.
      }
      intros H.
      rewrite eq0 in *.
      apply IH in H.
      destruct H as [H1 H2].
      destruct H2 as [H2 H3].
      destruct H3 as [H3 H4].
      use tpair.
      {exact H1. }
      use tpair. {assumption. }
      use tpair.
      { apply (istransnatlth _ _ _  H3 (natgthsnn iter) ). }
      simpl.
      apply H4.
  Defined.

  Definition  leading_entry_compute_dual_internal_correct3
    {n : nat} (v : Vector hq n) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : (( leading_entry_compute_dual_internal v iter)) = nothing )
    : ∏ i : ⟦ n ⟧%stn, i < iter -> v i = 0%hq.
  Proof.
    intros i i_lt_iter.
    revert ne_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter.
    - apply fromempty. apply negnatlthn0 in i_lt_iter; assumption.
    - rewrite nat_rect_step.
      assert (obv : iter < S n). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
      destruct (isdeceqhq 0%hq (v (iter,, p))) as [eq0 | ?].
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice i iter) as [le | eq]. {  apply natlthsntoleh; assumption. }
      + intros H.
        rewrite eq0 in *.
        apply IHiter in H; try assumption.
      + intros ?.
        rewrite eq0.
        apply maponpaths.
        apply subtypePath_prop.
        apply eq.
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
      destruct (isdeceqhq 0%hq (v (iter,, p))) as [eq0 | neq0].
      + apply IHiter.
        intros.
        apply H.  {apply (istransnatgth _ _ _ (natgthsnn iter) X ) . }
      + rewrite H in neq0; try assumption.
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
      use tpair. 
      {
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
    : is_leading_entry v i.
  Proof.
    unfold is_leading_entry.
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
    simpl.
    intros j lt.
    rewrite (H5 (dualelement j)).
    - rewrite dualelement_2x; apply idpath.
    - apply dualelement_lt_comp. (exact lt).
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
      destruct (isdeceqhq 0%hq _) as [eq0 | ?].
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice (dualelement i) (iter)). {  apply natlthsntoleh; assumption. }
      { intros H; rewrite eq0 in *; apply IHiter in H; try assumption. }
      intros ?.
      rewrite eq0.
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
    - destruct (natlthorgeh _ _); simpl; try reflexivity.
      symmetry in ne_nothing. apply negpathsii1ii2 in ne_nothing.
      contradiction.
    - simpl in ne_nothing.
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
    destruct (leading_entry_compute_dual_internal (col mat k) iter) as [s | ?]; simpl; try contradiction.
    destruct (natlthorgeh _ _); intros; try contradiction.
    apply negpathsii1ii2.
  Defined.

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
        set (H2' := (pr1 H2)); symmetry in H2'.
        pose (H3 := @leading_entry_compute_dual_internal_correct5 n (col mat k) (n,, natgthsnn n) H1 (H2')).
        destruct H3 as [H3 H4].
        intros i (*i_lt_iter*) ke_le_i.
        unfold col, transpose, flip in *.
        rewrite <- H4; try reflexivity; try assumption.
        apply (natlthlehtrans H1 row_sep i); assumption.
        apply (pr2 i).
      + apply ii1.
        use tpair. { apply H1. }
        use tpair. {apply gt. }
        unfold col, transpose, flip in *.
        destruct H2 as [? H2].
        destruct H2 as [? H2].
        destruct (isdeceqhq  (mat H1 k) 0%hq) as [contr_eq | ?].
        { rewrite contr_eq in *. contradiction. }
        assumption.
    - apply ii2.
      pose (H' := @leading_entry_compute_dual_internal_correct3).
      intros.
      rewrite <- (H' n (col mat k) (n,, natgthsnn n) none i); try reflexivity.
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
    induction col_iter as [| col_iter IH].
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

End LeadingEntry.

Section Gauss.

  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Context (R : rig).

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
      (k_i k_j : (⟦ n ⟧%stn)) (iter : ⟦ S n ⟧%stn)
    : Matrix hq n n.
  Proof.
    destruct iter as [iter lt].
    induction iter as [ | iter gauss_clear_column_IH ].
    { exact mat. }  (* not applying the step since surely 0 ≤ k *)
    destruct (natgthorleh iter k_i).
    - refine (gauss_clear_column_step n k_i k_j (iter,, lt) (gauss_clear_column_IH _)).
      apply (istransnatlth _ _ _ (natlthnsn iter) lt).
    - exact mat.
  Defined.

  (* A third version that more closely follows the matrix construction -
     we break at iter ≤ k. This however is already done in gauss_clear_column_step. 
     
     Deprecated - to be removed. *)
  (* Definition gauss_clear_column'' { n : nat }
    (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn))  (iter : ⟦ S n ⟧%stn) : Matrix hq n n.
  Proof.
    destruct iter as [pr1_ pr2_].
    induction pr1_ as [ | m gauss_clear_column_IH ].
    {exact mat. }  (* not applying the step since surely 0 ≤ k *)
    set (piv := mat k_i k_j).
    destruct (natgthorleh m k_i).
    2 : {exact mat. }
    assert (m_lt_n : m < S n). {  apply (istransnatlth _ _ _ (natlthnsn m) pr2_) . }
    exact (gauss_clear_column_step n k_i k_j (m,, pr2_) (gauss_clear_column_IH m_lt_n)).
  Defined. *)

  Lemma gauss_clear_column_as_left_matrix  { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn)) : Matrix hq n n.
  Proof.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - exact (@identity_matrix hq n).
    - assert (pr2_' : pr1_ < n). { apply pr2_. }
      assert (pr2_'' : pr1_ < S n). { apply (istransnatlth _ _ _ (natlthnsn pr1_ ) pr2_ ). }
       destruct (natgthorleh pr1_ k_i).
      + exact (make_add_row_matrix k_i  (pr1_,, pr2_) (- ((mat (pr1_,,pr2_) k_j) * hqmultinv (mat k_i k_j)))%hq
              ** (IHpr1_ pr2_'')).
      + exact (@identity_matrix hq n ** (IHpr1_ pr2_'' )).
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
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j']; simpl; try reflexivity.
    simpl.
    rewrite <- i'_eq_j'.
    rewrite eq0.
    unfold const_vec ; simpl.
    rewrite (@ringmultx0 hq).
    rewrite (@rigrunax1 hq).
    reflexivity.
  Defined.

  Lemma gauss_add_row_inv2 {n : nat} (mat : Matrix hq n n) (i_1 i_2: ⟦ n ⟧%stn) (s : hq)
    : ∏ (j_1: ⟦ n ⟧%stn), (mat i_1 j_1 = 0%hq) -> (gauss_add_row mat i_1 i_2 s) i_2 j_1 = mat i_2 j_1.
  Proof.
    intros j_1 eq0.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j']; simpl; try reflexivity.
    rewrite eq0.
    rewrite (@ringmultx0 hq).
    rewrite (@rigrunax1 hq).
    reflexivity.
  Defined.

  (* Restating a similar lemma for the regular version of this operation, in order to prove their
     equivalence 
     TODO this should not be necessary? 
     TODO at least remove 'h' temp variable names*)
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
      destruct (natgthorleh pr1_ k_i) as [gt | ?].
      + unfold gauss_clear_column_as_left_matrix in IHpr1_.
        assert (pr2_': pr1_ < S n). {apply (istransnatlth _ _ _ (natgthsnn pr1_) pr2_). }
        ( rewrite <- (IHpr1_ pr2_')).
        rewrite matrix_mult_assoc.
        2 : { apply natlehtolehs in X; assumption. }
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq.  apply natgthtoneq in gt. assumption. }
        rewrite IHpr1_. 2 : {apply natlehsntolth  in X. apply natlthtoleh in X. assumption. }
        set (x := nat_rect _ _ _ _).
        rewrite gauss_add_row_inv0.
        2: {apply snlehtotonlt in X.
            - apply issymm_natneq. apply natgthtoneq; assumption.
            - apply natneq0togth0.
              destruct (natchoice0 pr1_).
              + rewrite <- p in gt.
                apply negnatgth0n in gt.
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
      destruct (natgthorleh pr1_ k_i) as [gt | ?].
      + assert (pr2_': pr1_ < S n). {apply (istransnatlth _ _ _ (natgthsnn pr1_) pr2_). }
        ( rewrite <- (IHpr1_ pr2_')).
        unfold gauss_clear_column_as_left_matrix in *.
        rewrite IHpr1_.
        rewrite matrix_mult_assoc.
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq. apply natgthtoneq. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply natgthtoneq. apply (natlehlthtrans _ _ _  i_leh_k gt).  }
        unfold gauss_clear_column_as_left_matrix in IHpr1_.
        rewrite IHpr1_.
        reflexivity.
      + rewrite matlunax2.
        unfold gauss_clear_column_as_left_matrix in IHpr1_.
        rewrite IHpr1_.
        reflexivity.
  Defined.

  Lemma clear_column_matrix_invertible  { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn))
        : @matrix_inverse hq _ (gauss_clear_column_as_left_matrix iter mat k_i k_j).
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
    destruct (natchoice0 n) as [contr_eq | p].
    {apply fromstn0. rewrite contr_eq; assumption. }
    destruct (pr2 (select_uncleared_column mat row p)) as [some | none].
    2 : {exact mat. }
    refine (gauss_clear_column_old 
      _  row (pr1 (select_uncleared_column mat row p)) (n ,, natlthnsn n )).
    exact (gauss_switch_row mat row (pr1 (pr2 some))).
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
    refine (gauss_clear_row _ (row_sep,, row_sep_lt_n)).
    refine (gauss_clear_earlier_rows _).
    exact (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ).
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
    assert (lt : row_sep < S n).  {apply (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ). }
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
  (* TODO fix double work being done here - work on step' or use previous lemma *)
  Lemma gauss_clear_column_step_inv1 (n : nat) (k_i k_j : (⟦ n ⟧%stn))
        (j : (⟦ n ⟧%stn)) (mat : Matrix hq n n)  (p_1 : mat k_i k_j != 0%hq)
        (p_2 : j ≠ k_i) :
    (gauss_clear_column_step n k_i k_j j mat) j k_j = 0%hq.
  Proof.
    intros.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step', gauss_add_row.
    destruct (stn_eq_or_neq j k_i) as [p | ?].
    {rewrite p in p_2. apply isirrefl_natneq in p_2. contradiction. }
    assert (p_3 : n > 0). { apply (stn_implies_ngt0 k_i). }
    rewrite stn_eq_or_neq_refl; simpl.
    rewrite <- (@ringrmultminus hq).
    rewrite hqmultassoc.
    rewrite (@ringlmultminus hq).
    rewrite (hqmultcomm _ (mat k_i k_j) ).
    rewrite (hqisrinvmultinv (mat k_i k_j)). 2 : {exact p_1. }
    rewrite hqmultcomm.
    rewrite (@ringlmultminus hq).
    rewrite (@riglunax2 hq).
    apply hqrminus.
  Admitted.  (*Defined.*) (* TOOD really slow proof! Replace admitted by defined when sped up. *)

    (* The clear column step operation only changes the target row*)
  Lemma gauss_clear_column_step_inv2 (n : nat) (k_i k_j : (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix hq n n) (j : ⟦ n ⟧%stn)
        (p : r ≠ j)  : (gauss_clear_column_step n k_i k_j j mat) r = mat r.
  Proof.
    intros.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq j k_i) as [? | ?].
    {apply idpath. }
    apply funextfun; intros ?.
    rewrite gauss_add_row_inv0; try reflexivity.
    apply issymm_natneq; assumption.
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
    assert (b : iterop_fun 0%rig op1  f = f r). {
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
    rewrite (stn_eq_or_neq_refl), coprod_rect_compute_1.
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
  Lemma gauss_clear_column_inv0
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
  (* TODO - not admit, fix some variable naming*)
  Lemma gauss_clear_column_inv1
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
      + assert (le: r ≤ n'). { apply natlthtoleh in h. assumption. }
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
        replace (gauss_clear_column_step n k_i k_j sn'' _ r)
          with (gauss_clear_column_step n k_i k_j sn'' mat r).
        { replace sn'' with r.
          { rewrite gauss_clear_column_step_eq. apply idpath. }
          rewrite (@subtypePath_prop _ _ r (n',, p)). {reflexivity. }
          apply eq.
        }
        assert (commute :
                  gauss_clear_column_step n k_i k_j sn'' (gauss_clear_column_old mat k_i k_j  (n',, p'')) r
               =  gauss_clear_column_old (gauss_clear_column_step n k_i k_j sn'' mat) k_i k_j (n',, p'')  r).
        { do 2 rewrite gauss_clear_column_step_eq.
          unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _).
          {reflexivity. }
          unfold gauss_add_row.
          rewrite gauss_clear_column_inv0.
          2 : { unfold sn''. apply (natlthnsn). }
          assert (eq' : r = sn'').
          { rewrite (@subtypePath_prop _ _ r (n',, p)). {reflexivity. } apply eq. }
          rewrite <- eq'.
          rewrite (stn_eq_or_neq_refl).
          simpl.
          apply pathsinv0.
          etrans.
          { rewrite (gauss_clear_column_inv0).
            - apply idpath.
            - rewrite eq.
              apply natlthnsn.
          }
          apply funextfun. intros y.
          destruct (stn_eq_or_neq k_i y) as [eq'' | ?].
          - rewrite <- eq''.
            rewrite stn_eq_or_neq_refl.
            rewrite coprod_rect_compute_1.
            rewrite gauss_clear_column_inv3.
            + apply idpath.
            + apply isreflnatleh.
          - rewrite (stn_eq_or_neq_refl); simpl.
            rewrite gauss_clear_column_inv3; try reflexivity.
            apply isreflnatleh. 
        }
        unfold gauss_clear_column_old in commute.
        set (f := @gauss_clear_column_inv0).
        rewrite <- (f n k_i k_j ( n' ,, p'')).
        rewrite commute; try reflexivity.
        rewrite eq. apply isreflnatleh.
  Admitted. (*TODO speed up*)

  (* Invariant stating that the clearing procedure does clear all the target entries (r, k) for r > k. *)
  Lemma gauss_clear_column_inv1'
        { n : nat } (k_i k_j : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (mat : Matrix hq n n) (p' : mat k_i k_j != 0%hq) :  ∏ r : (⟦ n ⟧%stn),
    r < iter -> r > k_i -> ((gauss_clear_column_old mat k_i k_j iter) r k_j = 0%hq).
  Proof.
    destruct iter as [n' p].
    intros r r_le_n' r_gt_k.
    rewrite (gauss_clear_column_inv1  k_i k_j (n' ,, p) mat (*p'*) r r_le_n').
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
    - assert (lt: m < S n). { apply (istransnatgth _ _ _ p (natgthsnn m) ). }
      assert (le : S m ≤ k_i). { apply (istransnatgeh _ _ _ p' (natgehsnn (S m) )  ). }
      set (IHn' := IHn lt le).
      rewrite <- IHn'.
      unfold gauss_clear_column_old.
      rewrite nat_rect_step.
      destruct (natgthorleh _ _).
      { clear IHn'. apply fromempty. apply natgehsntogth in lt.
        apply natgehsntogth in le.
        apply isasymmnatgth in le; try assumption; contradiction.
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

  TODO maybe not useful anymore. *)
  (* Definition gauss_columns_cleared { n : nat } (mat : Matrix hq n n)
             (k_i k_j : ⟦ n ⟧%stn) := ∏ i j : ⟦ n ⟧%stn,
              j < k_j ->
              k_i < i ->
              mat i j = 0%hq. *)

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

  (* Proving that if the input matrix is  _lower triangular_, it will remain so after gcc. *)
  Lemma gauss_clear_column_inv5
    { n : nat }  (mat : Matrix hq n n) (k_i k_j : (⟦ n ⟧%stn)) (iter : ⟦ S n ⟧%stn)
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
    destruct (stn_eq_or_neq  _ _) as [eq | ?].
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

  (* 1 : any leading entry is strictly to the right of a previous leading entry
     2 : any zero row is below any non-zero row *)
  Definition is_row_echelon {n : nat} (mat : Matrix hq n n) :=
    ∏ i_1 i_2 : ⟦ n ⟧%stn,
    (∏ j_1 j_2 : ⟦ n ⟧%stn,
       leading_entry_compute (mat i_1) = (just j_2)
    -> i_1 < i_2
    -> j_1 ≤ j_2
    -> mat i_2 j_1 = 0%hq)
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
    intros H ? ?; intros.
    use tpair.
    { intros. refine (pr1 (H) i_1 i_2 j_1 _ _ _ _ _);
      try apply X; try assumption. exact (pr2 i_1).
    }
    simpl; intros.
    refine ((pr2 H) i_1 i_2 _ _ _ ); try assumption.
    exact (pr2 i_1).
  Defined.

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

  Lemma gauss_clear_row_inv1
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

  (* TODO this proof can be cleaned up considerably - many things are repeated, 
     some perhaps not once but twice or more. *)
  Lemma gauss_clear_row_inv2
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
        rewrite gauss_clear_column_inv1; try assumption.
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
      assert (st_eq : pr1 i_1 = pr1 row_sep). {apply eq. }
      destruct (stn_eq_or_neq j_1 j_2) as [j1_eq_j2 | j1_neq_j2]; try assumption.
      + rewrite j1_eq_j2 in *.
        rewrite gauss_clear_column_inv1.
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
        * intros.
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
              (*exact (pr2 j).*)
      + rewrite gauss_clear_column_inv1.
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
            (*2: {apply (pr2 j). }*)
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
          - destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
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
          - destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
            { simpl in h0.
              rewrite contr_eq in h1.
              contradiction (isirrefl_natneq _ h1). }
            rewrite (pr2 (pr2 (pr2 (pr2 some)))); try reflexivity; try assumption.
            apply natlthtoleh.
            simpl.
            rewrite <- st_eq; assumption.
          - destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl. 
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
              destruct (natlehchoice j_1 j_2) as [lt' | contr_eq]; try assumption.
              { apply (natlthlehtrans _ _ _ h3 lt'). }
                simpl in contr_eq. simpl in h. simpl in j1_neq_j2. rewrite <- contr_eq in j1_neq_j2.
                contradiction (isirrefl_natneq _ j1_neq_j2).
          }
          unfold leading_entry_compute in H1.
          rewrite (pr2 (pr2 (pr2 (pr2 (some))))); try reflexivity; try assumption.
          {apply isreflnatleh.  }
          -- destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; simpl.
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
    induction row_sep as [| row_sep IH]. {simpl. contradiction (negnatgth0n i_1 i1_lt_rowsep). }
    rename  i1_lt_rowsep into i1_lt_srowsep.
    set (lt' := (istransnatlth row_sep (S row_sep) (S n) (natgthsnn row_sep) lt)).
    unfold gauss_clear_rows_up_to_internal in *.
    rewrite nat_rect_step in *.
    unfold gauss_clear_row in *.
    destruct (natchoice0 n) as [contr_eq | ?]. { apply fromstn0. rewrite contr_eq; assumption. }
    revert le_nought.
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
          rewrite gauss_clear_column_inv1; try assumption.
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
      2:
        {assert (eq' : (row_sep,, lt) = i_1).
        { apply subtypePath_prop.
          apply pathsinv0. apply eq.
        }
        set (inner := nat_rect _ _ _ _).
        rewrite <- eq' in *; clear eq'.
        unfold leading_entry_compute in le_nought.
        unfold leading_entry_compute_internal in le_nought.
        contradiction (pr1( pr2 ( pr2 (pr2 (col ))))).
        unfold gauss_switch_row.
        destruct (stn_eq_or_neq i_1 i_1) as [? | contr_neq].
        2: { contradiction (isirrefl_natneq _ contr_neq). }
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
    pose ( H:= @gauss_clear_row_inv2).
    unfold gauss_clear_rows_up_to_internal.
    destruct row_sep as [row_sep p''].
    induction row_sep.
    { simpl. intros ? ? ? ? contr.
      contradiction (negnatlthn0 n contr). }
    rewrite nat_rect_step.
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
    -> leading_entry_compute (gauss_clear_rows_up_to mat p (n,, natgthsnn n) i_1)
       = just j_1
    -> leading_entry_compute (gauss_clear_rows_up_to mat p (n,, natgthsnn n) i_2)
       = just j_2
    -> j_1 < j_2.
  Proof.
    unfold is_row_echelon_partial_1.
    intros H1.
    intros i_1 i_2 j_1 j_2 lt.
    destruct (natgthorleh j_2 j_1) as [gt | ?]. {intros; apply gt. }
    unfold leading_entry_compute; intros H2 H3.
    pose (H4 := @leading_entry_compute_internal_correct1 n
                  _ (n,, natgthsnn n) _ H3).
    contradiction (pr1 H4).
    destruct (natlehchoice j_2 j_1) as [lt' | eq]. {assumption. }
    - rewrite (H1 i_1 i_2 j_2 j_1); try assumption; try reflexivity.
      exact (pr2 i_1).
    - rewrite  eq in *.
      rewrite (H1 i_1 i_2 j_2 j_1); try assumption; try reflexivity.
      {exact (pr2 i_1). }
      rewrite eq.
      apply (isreflnatleh).
  Defined.

  Lemma gauss_clear_rows_up_to_inv3
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0)
    (row_sep : (⟦ S n ⟧%stn))
    : is_row_echelon
        (gauss_clear_rows_up_to_internal mat p (n,, natgthsnn n)).
  Proof.
    pose (H := @is_row_echelon_from_partial n _
      (gauss_clear_rows_up_to_internal mat p (n,, natgthsnn n)) p).
    apply H.
    unfold is_row_echelon_partial.
    use tpair.
    - apply gauss_clear_rows_up_to_inv1.
    - apply gauss_clear_rows_up_to_inv2.
  Defined.

  Lemma row_echelon_partial_to_upper_triangular_partial
    { n : nat }
    (mat : Matrix hq n n)
    (p : n > 0)
    (iter : ⟦ S n ⟧%stn)
    : @is_row_echelon_partial n mat p iter
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
          (*exact (pr2 j).*)
        * pose (H1 := @leading_entry_compute_internal_correct1 n _ (n,, natgthsnn n)  _ jst).
          destruct (natchoice0 i) as [contr0 | ?].
          { apply fromempty; refine  (negnatgth0n _ _). rewrite contr0. apply lt. }
          destruct (prev_stn i) as [u u_lt]; try assumption.
          destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute (mat u))) as [prev | none_prev].
          -- destruct prev as [prev eq''].
             unfold leading_entry_compute in prev.
             pose (H2 := @leading_entry_compute_internal_correct1 n _ (n,, natgthsnn n) _ eq'').
             contradiction (pr1 H2).
             rewrite (IH iter_lt_sn); try reflexivity; try assumption.
             use tpair.
             ** intros i_1 i_2 j_1 j_2 i1_lt_iter H' ? ?.
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
    : @is_row_echelon n mat
  -> @is_upper_triangular hq n n mat.
  Proof.
    intros H.
    unfold is_upper_triangular.
    intros.
    rewrite (row_echelon_partial_to_upper_triangular_partial mat p (n,, natgthsnn n));
      try reflexivity; try assumption.
    2: {exact (pr2 i). }
    unfold is_row_echelon in H.
    unfold is_row_echelon_partial.
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    use tpair.
    - intros.
      destruct (H i_1 i_2) as [H1 H2]; try assumption.
      rewrite (H1 j_1 j_2); try assumption; reflexivity.
    - simpl.
      intros.
      destruct (H i_1 i_2) as [H1 H2]; try assumption.
      rewrite H2; try assumption; reflexivity.
  Defined.

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
    destruct (natchoice0 n) as [contr_eq | ?].
    {apply fromstn0. rewrite contr_eq. assumption. }
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

  Lemma gauss_clear_rows_up_to_matrix_invertible { n : nat } (iter : ⟦ S n ⟧%stn)
    (mat : Matrix hq n n) (p : n > 0) :
    (@matrix_inverse hq n ((@clear_rows_up_to_as_left_matrix _ mat p iter))).
  Proof.
    destruct iter as [iter lt].
    induction iter as [| iter IH].
    { unfold clear_rows_up_to_as_left_matrix,
             clear_rows_up_to_as_left_matrix_internal.
      simpl; apply identity_matrix_is_inv. }
    unfold clear_rows_up_to_as_left_matrix,
    clear_rows_up_to_as_left_matrix_internal.
    rewrite nat_rect_step.
    apply inv_matrix_prod_is_inv.
    - apply clear_row_matrix_invertible.
    - apply IH.
  Defined.

  Local Definition flip_hq_bin
    (e : hq) : hq.
  Proof.
    destruct (isdeceqhq 0%hq e).
    - exact 1%hq.
    - exact 0%hq.
  Defined.

  Local Definition flip_hq_bin_vec
    {n : nat} (v : Vector hq n) := λ i : (stn n), flip_hq_bin (v i).

  Definition diagonal_all_nonzero_compute
    {n : nat} (v : Vector hq n)
    : coprod (forall j : (stn n), (v j) != 0%hq)
             (∑ i : (stn n), (v i) = 0%hq).
  Proof.
    pose (H1 := leading_entry_compute (flip_hq_bin_vec v)).
    destruct (@maybe_stn_choice hq n H1) as [some | none].
    - right.
      use tpair. {apply some. }
      simpl. 
      pose (H2 := @leading_entry_compute_internal_correct1
        _ (flip_hq_bin_vec v) (n,, natgthsnn n) _ (pr2 some)).
      destruct H2 as [H2 H3].
      unfold is_leading_entry, flip_hq_bin_vec, flip_hq_bin in *.
      destruct (isdeceqhq 0%hq (v (pr1 some))).
      2: { contradiction. }
      symmetry; assumption.
    - left.
      intros j.
      pose (H3 := @leading_entry_compute_internal_correct2
        _ (flip_hq_bin_vec v) (n,, natgthsnn n ) none j).
      rewrite <- H3; try apply (pr2 (dualelement j)).
      destruct (isdeceqhq 0%hq (v j)) as [eq | neq]; unfold is_leading_entry, flip_hq_bin_vec, flip_hq_bin in *.
      + clear H3. destruct (isdeceqhq 0%hq (v j)); try contradiction.
        rewrite <- eq.
        confirm_not_equal isdeceqhq.
      + clear H3. destruct (isdeceqhq 0%hq (v j)); try contradiction.
        destruct (isdeceqhq (v j) 0%hq) as [contr_eq | ?]; try assumption.
        rewrite contr_eq in neq; contradiction.
  Defined.

  Lemma gaussian_elimination_inv0 {n : nat} {A : Matrix hq n n}
  : ∑ (A' : Matrix hq n n), (@matrix_inverse hq n A') × (is_row_echelon (A' ** A)).
  Proof.
    destruct (natchoice0 n) as [eq0 | gt].
    { use tpair; try assumption; simpl. use tpair.
      { unfold matrix_inverse. use tpair. {exact A. }
        simpl.
        use tpair.
        - apply funextfun; intros i. apply fromstn0. rewrite eq0. assumption.
        - simpl; apply funextfun; intros i. apply fromstn0. rewrite eq0. assumption.
      }
      unfold is_row_echelon. intros i. apply fromstn0. rewrite eq0. assumption.
    }
    use tpair.
    - exact (@clear_rows_up_to_as_left_matrix n A gt (n,, natgthsnn n)).
    - simpl.
      use tpair.
      + apply gauss_clear_rows_up_to_matrix_invertible. 
      + simpl.
        rewrite gauss_clear_rows_up_to_as_matrix_eq.
        pose (H2 := @gauss_clear_rows_up_to_inv3 n A gt (n,, natgthsnn n)).
        apply H2.
  Defined.

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
