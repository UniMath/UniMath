 (** * Matrices

Gaussian Elimination over fields.

Author: @Skantz (April 2022)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Maybe.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.Tactics.Nat_Tactics.

Require Import UniMath.PAdics.z_mod_p.
Require Import UniMath.PAdics.lemmas.

Require Import UniMath.RealNumbers.Prelim.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.
Require Import UniMath.Algebra.Elimination.Matrices.
Require Import UniMath.Algebra.Elimination.RowOps.


(** In this Module we formalize gaussian elimination by means of
    matrix multiplication equivalent elementary row operations.
    
    We first formalize the notion of row echelon form,
    and then present the main theorem resulting from this module.
    
*)

(** TODO interchange j1 j2 
    Possible form: for all i1 j1, is_leading_entry M i1 j1 -> forall i2, j2, i2 > i1, j2 <_ j1, _ = 0
    TODO cover other forms (enforce other)
    *)
Section Summary.

  Context (R: ring).
  Context (F: fld).

  Local Notation Σ := (iterop_fun (@rigunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition is_leading_entry {F : fld} {n : nat} (v : Vector F n) (i_1 : ⟦ n ⟧%stn)
    := (v i_1 != 0%ring)
      × (∏ i_2 : ⟦ n ⟧%stn, i_2 < i_1 -> (v i_2) = 0%ring).

  (* 1 : any leading entry is strictly to the right of a previous leading entry
     2 : any zero row is below any non-zero row *)
  Definition is_row_echelon {F : fld} {m n : nat} (mat : Matrix F m n) :=
    ∏ i_1 i_2 : ⟦ m ⟧%stn,
    (∏ j_1 j_2 : ⟦ n ⟧%stn,
      is_leading_entry (mat i_1) j_2
      -> i_1 < i_2 -> j_1 ≤ j_2
      -> mat i_2 j_1 = 0%ring)
    × ((mat i_1 = const_vec 0%ring)
      -> (i_1 < i_2)
      -> (mat i_2 = const_vec 0%ring)).

  Definition gaussian_elimination_stmt
    {F : fld} {m n : nat} {A : Matrix _ m n}
    := ∑ (B : Matrix _ _ _), (matrix_inverse B)
      × (is_row_echelon (B ** A)).

End Summary.

(** In the proceeding, we provide a sub-module for calculating the leading entry of a vector, 
    and provide suitable correctness lemmata for it. *)

Section LeadingEntry.

  Context (R: ring).
  Context (F: fld).

  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).


  Definition is_leading_entry_dual {n : nat} (v : Vector F n) (i_1 : ⟦ n ⟧%stn)
    := (v i_1 != 0%ring) × (∏ i_2 : ⟦ n ⟧%stn, i_1 < i_2 -> (v i_2) = 0%ring).

  Definition leading_entry_compute_dual_internal
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧%stn).
  Proof.
    destruct iter as [iter lt].
    induction iter.
    { exact nothing. }
    simpl in lt.
    destruct (fldchoice0 (v (iter,, lt))).
    - refine (IHiter _).
      apply (istransnatlth _ _ _ lt (natgthsnn n)).
    - exact (just (iter,, lt)).
  Defined.

  Definition leading_entry_compute_internal
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧)%stn.
  Proof.
    destruct (leading_entry_compute_dual_internal
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) iter) as [s | ?].
    - exact (just (dualelement s)).
    - exact nothing.
  Defined.

  Definition leading_entry_compute {n : nat} (v : Vector F n)
     := leading_entry_compute_internal v (n,, natgthsnn n).

  Definition leading_entry_dual_compute {n : nat} (v : Vector F n)
     := leading_entry_compute_dual_internal v (n,, natgthsnn n).
  Proof.

  Lemma leading_entry_compute_eq  {n : nat} (v : Vector F n)
    (i_1 i_2 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute v = just i_1)
    (e_2 : leading_entry_dual_compute (λ i : ⟦ n ⟧%stn, v (dualelement i)) = just i_2)
    : i_1 = dualelement i_2.
  Proof.
    unfold leading_entry_compute, leading_entry_dual_compute in *.
    unfold leading_entry_compute_internal in *.
    destruct (leading_entry_compute_dual_internal
      (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))
      as [s | contr].
    2: { unfold just, nothing in e_1.
         contradiction (negpathsii1ii2 i_1 tt). apply pathsinv0. apply e_1. }
    assert (e_3 : (dualelement s) = i_1).
    { apply just_injectivity. exact (e_1). }
    assert (e_4 : s = i_2).
    { unfold just in e_2. apply ii1_injectivity in e_2. assumption. }
    rewrite <- e_3; rewrite e_4; apply idpath.
  Defined.

  Lemma leading_entry_compute_internal_eq  {n : nat} (v : Vector F n)
    (i_1 i_2 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute_internal v (n,, natgthsnn n) = just i_1)
    (e_2 : leading_entry_compute_dual_internal
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn n) = just i_2)
    : i_1 = dualelement i_2.
  Proof.
    apply (leading_entry_compute_eq v); try assumption.
  Defined.

  Lemma leading_entry_compute_impl {n : nat} (v : Vector F n)
    (i_1 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute_internal v (n,, natgthsnn n) = just i_1)
    : ∑ (i_2 : ⟦ n ⟧%stn),
      leading_entry_compute_dual_internal
        (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn n) = just i_2.
  Proof.
    unfold leading_entry_compute, leading_entry_dual_compute in *.
    unfold leading_entry_compute_internal in *.
    destruct (leading_entry_compute_dual_internal
      (λ i : (⟦ n ⟧)%stn, _) (n,, natgthsnn n)) as [s | contr].
    - assert (e_2 : dualelement s = i_1). {apply just_injectivity. apply e_1. }
      apply dualelement_eq in e_2.
      rewrite e_2.
      use tpair. {apply s. }
      simpl. rewrite e_2. reflexivity.
    - unfold just, nothing in e_1. contradiction (negpathsii1ii2 (i_1) tt).
      apply pathsinv0. apply e_1.
  Defined.

  Lemma leading_entry_compute_dual_internal_correct2
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : (leading_entry_compute_dual_internal v iter) != nothing)
    : (∑ i : ⟦ n ⟧%stn,
             just i = (leading_entry_compute_dual_internal v iter)
           × i < iter × (v i != 0%ring)).
  Proof.
    revert ne_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    { simpl; intros; contradiction. }
    rewrite nat_rect_step.
    destruct (fldchoice0 _) as [eq0| neq0].
    - intros H.
      apply IH in H.
      destruct H as [e H]; 
        destruct H as [eq H];
        destruct H as [lt neq0].
      use tpair. {exact e. }
      use tpair. {assumption. }
      use tpair. {apply (istransnatlth _ _ _  lt (natgthsnn iter) ). }
      apply neq0.
    - intros ?. use tpair.
      { exact (iter ,, p). }
      use tpair. {simpl. reflexivity. }
      use tpair. {apply (natgthsnn iter). }
      simpl; intros.
      intros contr_eq0.
      contradiction neq0.
  Defined.

  (* TODO upstream? *)
  Local Lemma stn_eq
    {k : nat} (i j : stn k) (eq : pr1 i = pr1 j) : i = j.
  Proof.
    apply subtypePath_prop; assumption.
  Defined.

  Local Lemma stn_eq_2
    {k : nat} (i: stn k) (j : nat) (eq : pr1 i = j) : forall P : j < k, i = (j,, P).
  Proof.
    intros lt.
    apply subtypePath_prop.
    assumption.
  Defined.

  Local Lemma stn_eq_3
    {k : nat} (i: nat) (j : stn k) (eq : i = pr1 j) : forall P : i < k, j = (i,, P).
  Proof.
    apply stn_eq_2; symmetry; assumption.
  Defined.

  Definition leading_entry_compute_dual_internal_correct3
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : (leading_entry_compute_dual_internal v iter) = nothing)
    : ∏ i : ⟦ n ⟧%stn, i < iter -> v i = 0%ring.
  Proof.
    intros i i_lt_iter.
    revert ne_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter.
    {apply fromempty. apply negnatlthn0 in i_lt_iter; assumption. }
    rewrite nat_rect_step.
    destruct (fldchoice0 (v (iter,, p))) as [eq0 | ?].
    2 : { simpl. unfold just.
          intros contr.
          apply negpathsii1ii2 in contr.
          apply fromempty; assumption.
    }
    destruct (natlehchoice i iter) as [le | eq].
      {apply natlthsntoleh; assumption. }
    - intros H.
      apply IHiter in H; try assumption.
    - intros ?.
      rewrite (stn_eq_2 _ _ eq p), eq0.
      apply idpath.
  Defined.

  Definition leading_entry_compute_dual_internal_correct5 {n : nat} (v : Vector F n)
    (iter : ⟦ S n ⟧%stn)
    (i : ⟦ n ⟧%stn)
    (eq : ((leading_entry_compute_dual_internal v iter)) = (just i))
    : (v i != 0%ring) × (∏ i' : ⟦ n ⟧%stn, i < i' -> i' < iter -> v i' = 0%ring).
  Proof.
    unfold leading_entry_compute_dual_internal.
    assert (ne_nothing : leading_entry_compute_dual_internal v iter != nothing).
    { destruct (maybe_choice (leading_entry_compute_dual_internal v iter));
        try assumption.
      rewrite eq; apply negpathsii1ii2. }
    revert ne_nothing.
    destruct iter as [iter p].
    induction iter.
    { simpl. intros. use tpair; contradiction. }
    set (p' :=  (istransnatlth iter n (S n) p (natgthsnn n))).
    pose (@leading_entry_compute_dual_internal n v (S iter,, p) ) as H.
    destruct (@maybe_stn_choice F n H) as [s | ?].
    2: {contradiction. }
    unfold leading_entry_compute_dual_internal.
    rewrite nat_rect_step.
    destruct (fldchoice0 (v (iter,, p) )) as [z | nz].
    - intros H'.
      pose (first_nonzero := leading_entry_compute_dual_internal_correct2
        v (iter,, p') H').
      assert (ne_nothing : leading_entry_compute_dual_internal v (S iter,, p) != nothing).
      { unfold leading_entry_compute_dual_internal.
        rewrite nat_rect_step.
        destruct (fldchoice0 _).
        2: { destruct (!z); contradiction. }
        apply H'. }
      use tpair.
      { pose (C2 := @leading_entry_compute_dual_internal_correct2
          n v (S iter,, p) ne_nothing).
        destruct C2 as [? C2].
        destruct C2 as [eq' C2].
        unfold H in s; destruct s as [s s_eq].
        rewrite eq in eq'.
        apply (just_injectivity) in eq'.
        rewrite <- eq'; apply (pr2 C2).
      }
      simpl; intros i' ? ?.
      destruct (natlehchoice i' iter) as [? | eq']. {assumption. }
      { apply (IHiter p'); try assumption.
        unfold H in eq.
        unfold leading_entry_compute_dual_internal in eq.
        rewrite nat_rect_step in eq.
        destruct (fldchoice0 _) in eq.
        2: {contradiction. }
        unfold leading_entry_compute_dual_internal.
        unfold p'; rewrite eq; reflexivity.
      }
      rewrite (stn_eq_2 _ _ eq' p).
      rewrite z; apply idpath.
    - intros ?; simpl; use tpair.
      { destruct (maybe_choice (leading_entry_compute_dual_internal v (S iter,, p)))
          as [H' | contr_eq].
        2: { destruct (!contr_eq). unfold just in eq.
             symmetry in eq. apply negpathsii1ii2 in eq.
             contradiction.
        }
        pose (C2 := @leading_entry_compute_dual_internal_correct2 n v (S iter,, p) H').
        destruct C2 as [i' C2].
        destruct C2 as [eq' C2].
        destruct s as [s s_eq].
        rewrite eq in eq'.
        destruct C2 as [? neq].
        apply (just_injectivity) in eq'.
        rewrite <- eq'; apply neq.
      }
      intros ? i'_gt_iter i_le_iter.
      apply natlthtonegnatgeh in i'_gt_iter.
      unfold leading_entry_compute_dual_internal in eq.
      rewrite nat_rect_step in eq.
      destruct (fldchoice0 _) as [? | eq'] in eq.
      {contradiction. }
      apply just_injectivity in eq.
      rewrite <- eq in *.
      contradiction.
  Defined.

  Lemma leading_entry_compute_internal_correct1
    {n : nat} (v : Vector F n) (i : ⟦ n ⟧%stn)
    (eq : (leading_entry_compute_internal v (n,, natgthsnn n)) = (just i))
    : is_leading_entry v i.
  Proof.
    unfold is_leading_entry.
    pose (H1 := leading_entry_compute_impl v i eq).
    destruct H1 as [i' H1].
    pose (H2 := leading_entry_compute_eq v i i' eq H1).
    unfold leading_entry_compute_internal in eq.
    pose (H := @leading_entry_compute_dual_internal_correct5 n
              (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n) (dualelement i)).
    destruct (@maybe_stn_choice F n
              (leading_entry_compute_dual_internal
              (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn n))) as [? | contr_eq].
    2: { contradiction (@negpathsii1ii2 ((⟦ n ⟧)%stn) unit i' tt).
         unfold just in H1; rewrite <- H1.
         rewrite contr_eq. reflexivity. }
    destruct t as [t H3].
    destruct (!H2).
    destruct H as [H4 H5].
    { rewrite dualelement_2x. apply H1. }
    use tpair. { rewrite dualelement_2x in H4. assumption. }
    simpl.
    intros j lt.
    change 0%ring with (@rigunel1 F) in *.
    rewrite <- (H5 (dualelement j)).
    - rewrite dualelement_2x; apply idpath.
    - apply dualelement_lt_comp. (exact lt).
    - exact (pr2 (dualelement j)).
  Defined.

  Lemma leading_entry_compute_internal_correct2
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (eq_nothing : (leading_entry_compute_internal v iter) = nothing )
    : ∏ i : ⟦ n ⟧%stn, (dualelement i) < iter -> v i = 0%ring.
  Proof.
    intros i i_lt_iter.
    revert eq_nothing.
    unfold leading_entry_compute_internal, leading_entry_compute_dual_internal.
    destruct iter as [iter pr2_].
    induction iter.
    - apply fromempty. apply negnatlthn0 in i_lt_iter; assumption.
    - rewrite nat_rect_step.
      destruct (fldchoice0 _) as [eq0 | ?].
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice (dualelement i) (iter)). {  apply natlthsntoleh; assumption. }
      + intros H. apply IHiter in H; try assumption.
      + intros ?.
        rewrite (dualelement_eq i (iter,, pr2_)); try reflexivity; try assumption.
        apply subtypePath_prop; assumption.
  Defined.


  Lemma leading_entry_compute_correct2
    {n : nat} (v : Vector F n)
    (eq_nothing : (leading_entry_compute v) = nothing )
    : ∏ i : ⟦ n ⟧%stn, v i = 0%ring.
  Proof.
    intros i.
    rewrite (leading_entry_compute_internal_correct2 _ _ eq_nothing i); try reflexivity.
    unfold dualelement.
    destruct (natchoice0 n) as [eq | neq]; simpl.
    - apply fromstn0; rewrite eq; assumption.
    - refine (natlehlthtrans (n - 1 - i) (n - 1) n _ _ ).
      + apply minusleh.
      + apply natminus1lthn.
        assumption.
  Defined.

  Lemma leading_entry_compute_correct3
    {n : nat} (v : Vector F n)
    (i : ⟦ n ⟧%stn)
    (eq : (leading_entry_compute v) = (just i))
    : (v i != 0%ring) × (∏ i' : ⟦ n ⟧%stn, i' < i -> v i' = 0%ring).
  Proof.
    use tpair.
    - pose (H1 := @leading_entry_compute_internal_correct1).
      unfold is_leading_entry in H1.
      apply H1; exact eq.
    - simpl.
      intros i' i_gt_i'.
      pose (H2 := @leading_entry_compute_impl _ _ _ eq).
      destruct H2 as [H2 H3].
      pose (H4 := @leading_entry_compute_dual_internal_correct5 _ _ _ _ H3).
      simpl in H4.
      destruct H4 as [H4 H5].
      rewrite <- (H5 (dualelement i')).
      + rewrite dualelement_2x; reflexivity.
      + apply dualelement_lt_comp'.
        rewrite dualelement_2x.
        replace (dualelement H2) with i; try assumption.
        rewrite (@leading_entry_compute_internal_eq _ _ _ H2 eq H3).
        reflexivity.
      + exact (pr2 (dualelement i')).
  Defined.

  Lemma leading_entry_compute_correct1
    {n : nat} (v : Vector F n)
    (i : ⟦ n ⟧%stn)
    (eq: (leading_entry_compute v = just i))
    : is_leading_entry v i.
  Proof.
    unfold is_leading_entry.
    use tpair; simpl.
    { apply leading_entry_compute_correct3; assumption. }
    apply leading_entry_compute_correct3; assumption.
  Defined.

  Lemma leading_entry_compute_deceq {n : nat} (v : Vector F n) (i : ⟦ n ⟧%stn)
    : coprod (leading_entry_compute v = just i)
             (leading_entry_compute v = just i -> empty).
  Proof.
    destruct (@maybe_stn_choice F n (leading_entry_compute_internal v (n,, natgthsnn n)))
      as [some | none].
    - destruct some as [t ist].
      destruct (stn_eq_or_neq i t) as [eq | neq].
      + left. unfold is_leading_entry.
        rewrite eq.
        assumption.
      + right.
        intros isle.
        destruct (natgthorleh i t) as [gt | leh].
        * pose (H1 := (@leading_entry_compute_correct3 n v i isle)).
          pose (H2 := (@leading_entry_compute_correct3 n v t ist)).
          contradiction (pr1 H2).
          rewrite (pr2 H1 t); try reflexivity; assumption.
        * pose (H1 := (@leading_entry_compute_correct3 n v i isle)).
          pose (H2 := (@leading_entry_compute_correct3 n v t ist)).
          destruct (natlehchoice i t leh) as [lt | contr_eq].
          -- unfold is_leading_entry in isle.
             contradiction (pr1 H1).
             rewrite (pr2 H2 i); try assumption; reflexivity.
          -- unfold stntonat in neq. 
             rewrite ((subtypePath_prop contr_eq)) in neq;
               contradiction (@isirrefl_natneq _ neq).
    - right.
      intros contr_H.
      pose (H := (@leading_entry_compute_correct3 n v i contr_H)).
      contradiction (pr1 H).
      rewrite ((@leading_entry_compute_correct2 n v none) i);
      reflexivity.
  Defined.

End LeadingEntry.

Section Pivot.

  Context (R: ring).
  Context (F: fld).

  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition select_pivot_row_coprod {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (k : ⟦ n ⟧%stn) :
    coprod ((∑ i: ⟦ m ⟧%stn, row_sep ≤ i × ((mat i k) != 0%ring)))
          (∏ i : ⟦ m ⟧%stn, row_sep ≤ i -> mat i k = 0%ring).
  Proof.
    pose (H := (leading_entry_compute_dual_internal_correct2
      _ (col mat k) (m,, natgthsnn m))).
    destruct (maybe_choice (leading_entry_compute_dual_internal
      _ (col mat k) (m,, natgthsnn m))) as [nnone | none].
    - destruct H as [H1 H2]; try assumption.
      destruct (natlthorgeh H1 row_sep) as [? | gt].
      + apply ii2.
        set (H2' := (pr1 H2)); symmetry in H2'.
        pose (H3 := @leading_entry_compute_dual_internal_correct5
          _ _ (col mat k) (m,, natgthsnn m) H1 (H2')).
        destruct H3 as [H3 H4].
        intros i ke_le_i.
        unfold col, transpose, flip in *.
        rewrite H4; try reflexivity; try assumption.
        apply (natlthlehtrans H1 row_sep i); assumption.
        apply (pr2 i).
      + apply ii1.
        use tpair. { apply H1. }
        use tpair. { apply gt. }
        unfold col, transpose, flip in *.
        destruct H2 as [? H2].
        destruct H2 as [? H2].
        destruct (fldchoice0 (mat H1 k)) as [contr_eq | ?].
        { destruct (!contr_eq). contradiction. }
        assumption.
    - apply ii2.
      pose (H' := @leading_entry_compute_dual_internal_correct3).
      intros.
      rewrite <- (H' _ m (col mat k) (m,, natgthsnn m) none i); try reflexivity.
      apply (pr2 i).
  Defined.

  Definition select_uncleared_column_compute
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn) (p : n > 0)
    : maybe ((⟦ m ⟧%stn) × (⟦ n ⟧%stn)).
  Proof.
    destruct (natchoice0 m) as [contr_eq | ngt0].
    {apply fromstn0. rewrite contr_eq. assumption. }
    destruct col_iter as [col_iter lt].
    induction col_iter as [| col_iter IH].
    - exact nothing.
    - destruct (select_pivot_row_coprod mat row_sep (col_iter,, lt)) as [nz | z].
      + exact (just (pr1 nz,, (col_iter,, lt))).
      + simpl in lt;
          exact (IH (istransnatlth _ _ _ lt (natgthsnn n))).
  Defined.

  Local Definition exists_first_uncleared
  {m n : nat} (mat : Matrix F m n)
  (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn)
    := ((∑ j: ⟦ n ⟧%stn, j < col_iter × (∑ i: ⟦ m ⟧%stn, row_sep ≤ i × ((mat i j) != 0%ring)
      × ∏ i' : (⟦ m ⟧)%stn, ∏ (j' : stn n), row_sep ≤ i' -> j' < j -> mat i' j' = 0%ring))).

  Local Definition lower_left_zero {m n : nat} (mat : Matrix F m n)
  (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn)
    := (∏ i : ⟦ m ⟧%stn, row_sep ≤ i
      -> (∏ j : ⟦ n ⟧%stn, j < col_iter -> mat i j = 0%ring)).

  Lemma select_uncleared_column_internal
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn) (p : n > 0)
    : coprod
      (exists_first_uncleared mat row_sep col_iter)
      (lower_left_zero mat row_sep col_iter).
  Proof.
    destruct (natchoice0 m) as [contr_eq | ngt0].
    {apply fromstn0. rewrite contr_eq. assumption. }
    destruct col_iter as [col_iter lt].
    induction col_iter as [| col_iter IH].
    - right; intros ? ? ? contr.
      contradiction (negnatgth0n n contr).
    - assert (lt' : col_iter < S n).
      { simpl in lt. apply (istransnatlth _ _ _ lt (natgthsnn n)). }
      destruct (IH lt') as [IH_left | IH_right].
      + destruct IH_left as [m' IH_left].
        destruct IH_left as [H1 IH_left].
        destruct IH_left as [H2 H3].
        left.
        use tpair. { apply m'. }
        use tpair. { apply (istransnatlth _ _ _ H1 (natgthsnn col_iter)). }
        use tpair. { simpl in lt. apply H2. } apply H3.
      + destruct (select_pivot_row_coprod mat row_sep (col_iter,, lt)) as [nz | z].
        * left.
          use tpair. {exact (col_iter,, lt). }
          use tpair. { apply (natgthsnn col_iter). }
          do 3 (use tpair; try apply nz); simpl; intros.
          apply IH_right; try assumption.
        * right.
          intros i rowsep_le_i j j_lt_scoliter.
          destruct (natlehchoice j col_iter) as [? | eq]; intros.
          { apply (natlehlthtrans _ _ _ j_lt_scoliter). apply (natgthsnn col_iter). }
          { intros. apply IH_right; try assumption. }
          rewrite <- (z i); try assumption.
          apply maponpaths, subtypePath_prop.
          assumption.
  Defined.

  Definition select_uncleared_column
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (p : n > 0)
    := select_uncleared_column_internal mat row_sep (n,, natgthsnn n) p.

End Pivot.

Section Gauss.

  Context (R : rig).
  Context (F : fld).
  
  Local Notation Σ := (iterop_fun (@ringunel1) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition gauss_clear_column_step
    {m n : nat}
    (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (i : (stn m))
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    destruct (stn_eq_or_neq i k_i) as [? | ?].
    - exact mat.
    - refine ((add_row_matrix k_i i _)%ring ** mat).
      exact (- ((mat i k_j) * fldmultinv' (mat k_i k_j)))%ring.
  Defined.

  Definition gauss_clear_column_step'
    {m n : nat}
    (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (i : (stn m))
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    destruct (stn_eq_or_neq i k_i) as [? | ?].
    - exact mat.
    - exact (gauss_add_row mat k_i i
        (- ((mat i k_j) * fldmultinv' (mat k_i k_j)))%ring).
  Defined.

  Lemma gauss_clear_column_step_eq {m n : nat}
    (k_i i: (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (mat : Matrix F m n)
    : (gauss_clear_column_step k_i k_j i mat)
      = (gauss_clear_column_step' k_i k_j i mat).
  Proof.
    unfold gauss_clear_column_step, gauss_clear_column_step'.
    destruct (stn_eq_or_neq i k_i) as [? | ?].
    { apply idpath. }
    rewrite add_row_mat_elementary.
    - apply idpath.
    - apply issymm_natneq.
      assumption.
  Defined.

  (* TODO generalize some of this material to rigs *)
  Lemma gauss_add_row_inv0
    {m n : nat}
    (mat : Matrix F m n)
    (i : ⟦ m ⟧%stn) (j: ⟦ m ⟧%stn)
    (s : F)
    : ∏ (k : ⟦ m ⟧%stn), j ≠ k -> gauss_add_row mat i j s k = mat k.
  Proof.
    intros k j_ne_k.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j]; try reflexivity.
    rewrite k_eq_j in j_ne_k.
    apply isirrefl_natneq in j_ne_k.
    apply fromempty; assumption.
  Defined.

  (* TODO step invs at same place *)
  Lemma gauss_clear_column_step_inv2
    {m n : nat}
    (k_i : stn m) (k_j : (⟦ n ⟧%stn))
    (r : (⟦ m ⟧%stn))
    (mat : Matrix F m n)
    (j : ⟦ m ⟧%stn)
    (p : r ≠ j)
    : ((gauss_clear_column_step k_i k_j j mat) r) = (mat r).
  Proof.
    intros.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq j k_i) as [? | ?].
    { apply idpath. }
    apply funextfun; intros ?.
    rewrite gauss_add_row_inv0; try reflexivity.
    apply issymm_natneq; assumption.
  Defined. 

  Definition gauss_clear_column { m n : nat }
    (mat : Matrix F m n) (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn)) (row_sep : ⟦ S m ⟧%stn)
    : Matrix F m n.
  Proof.
    destruct row_sep as [iter lt].
    induction iter as [ | iter gauss_clear_column_IH ].
    { exact mat. } 
    destruct (natgthorleh iter k_i) as [gt | leh].
    2: {exact mat. }
    refine (gauss_clear_column_step k_i k_j (iter,, lt) _ ).
    refine (gauss_clear_column_IH _).
    refine (istransnatlth _ _ _ (natgthsnn iter) _).
    assumption.
  Defined.

  Lemma gauss_clear_column_as_left_matrix 
    { m n : nat }
    (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : (⟦ n ⟧%stn))
    : Matrix F m m.
  Proof.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - exact (@identity_matrix F m).
    - assert (p': iter < S m).
      { apply (istransnatlth _ _ _ (natgthsnn iter) p ). }
       destruct (natgthorleh iter k_i).
      + exact (add_row_matrix k_i (iter,, p)
        (- ((mat (iter,, p) k_j) * fldmultinv' (mat k_i k_j) ))%ring ** (IH p')).
      + exact (@identity_matrix F m ** (IH p')).
  Defined.

  Lemma gauss_add_row_inv1
    {m n : nat}
    (mat : Matrix F m n)
    (i : ⟦ m ⟧%stn)
    (j: ⟦ m ⟧%stn)
    (s : F)
    : ∏ (k : ⟦ m ⟧%stn),
      (mat i = const_vec 0%ring) -> gauss_add_row mat i j s = mat.
  Proof.
    intros k eq0.
    apply funextfun; intros i'; apply funextfun; intros j'.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j'];
      simpl; try reflexivity.
    simpl.
    rewrite <- i'_eq_j', eq0.
    unfold const_vec ; simpl.
    rewrite (@ringmultx0 F), (@rigrunax1 F).
    reflexivity.
  Defined.

  (* Restating a similar lemma for the regular version of this operation,
     in order to prove their equivalence *)
  Lemma gauss_clear_column_as_left_matrix_inv0
    { m n : nat }
    (iter : (stn (S m)))
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn))
    (k_j : stn n)
    (i : ⟦ m ⟧%stn)
    : iter ≤ i
    -> ((gauss_clear_column_as_left_matrix iter mat k_i k_j) ** mat) i = mat i.
  Proof.
    intros le.
    unfold gauss_clear_column_as_left_matrix.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - simpl. intros. simpl.
      rewrite matlunax2. reflexivity.
    - unfold gauss_clear_column_as_left_matrix.
      rewrite nat_rect_step.
      destruct (natgthorleh iter k_i) as [gt | ?].
      + unfold gauss_clear_column_as_left_matrix in IH.
        assert (lt: iter < S m). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
        ( rewrite <- (IH lt)).
        rewrite matrix_mult_assoc.
        2 : { apply natlehtolehs in le; assumption. }
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq.  apply natgthtoneq in gt. assumption. }
        rewrite IH. 2 : {apply natlehsntolth in le. apply natlthtoleh in le. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply snlehtotonlt in le.
            - apply issymm_natneq. apply natgthtoneq; assumption.
            - apply natneq0togth0.
              destruct (natchoice0 iter) as [lt' | ?].
              + rewrite <- lt' in gt.
                apply negnatgth0n in gt.
                contradiction.
              + apply natgthtoneq.
                assumption.
        }
        rewrite IH; try apply idpath.
        apply natlehsntolth; apply natlthtoleh; assumption.
      + rewrite matlunax2. 
        assert (lt: iter < S m). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
        unfold gauss_clear_column_as_left_matrix in IH.
        rewrite <- (IH lt).
        2: {apply (istransnatleh (natgehsnn iter) le). }
        unfold matrix_mult.
        apply funextfun; intros q.
        apply maponpaths; do 2 apply maponpaths_2.
        apply maponpaths, proofirrelevance, propproperty.
  Defined.

  Lemma gauss_clear_column_as_left_matrix_inv1
    { m n : nat }
    (iter : stn (S m))
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : (stn n))
    (i : ⟦ m ⟧%stn) (i_leh_k : i ≤ k_i)
    : (gauss_clear_column_as_left_matrix iter mat k_i k_j ** mat) i = mat i.
  Proof.
    unfold gauss_clear_column_as_left_matrix.
    destruct iter as [iter p].
    induction iter as [| iter IH]; intros.
    { simpl; rewrite matlunax2; reflexivity. }
    unfold gauss_clear_column_as_left_matrix.
    rewrite nat_rect_step.
    destruct (natgthorleh iter k_i) as [gt | ?].
    2: { rewrite matlunax2; rewrite IH; reflexivity. }
    assert (lt: iter < S m). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
    rewrite <- (IH lt).
    rewrite IH, matrix_mult_assoc, add_row_mat_elementary.
    2: {apply issymm_natneq. apply natgthtoneq. assumption. }
    rewrite gauss_add_row_inv0.
    2: {apply natgthtoneq. apply (natlehlthtrans _ _ _  i_leh_k gt).  }
    rewrite IH; reflexivity.
  Defined.

  Lemma clear_column_matrix_invertible
    { m n : nat }
    (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn))
    (k_j : stn n)
    : @matrix_inverse F _ (gauss_clear_column_as_left_matrix iter mat k_i k_j).
  Proof.
    unfold gauss_clear_column_as_left_matrix.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    - simpl. apply identity_matrix_is_inv.
    - rewrite nat_rect_step.
      destruct (natgthorleh iter k_i) as [gt | ?].
      2: { apply inv_matrix_prod_is_inv.
           - apply identity_matrix_is_inv.
           - apply IH. }
      apply inv_matrix_prod_is_inv.
      { apply add_row_matrix_is_inv.
        apply natlthtoneq; assumption. }
      apply IH.
  Defined.

  Definition gauss_clear_row
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    : Matrix F m n.
  Proof.
    destruct (natchoice0 n) as [contr_eq | p].
    { unfold Matrix, Vector; intros; apply fromstn0.
      rewrite contr_eq; assumption. }
    destruct (select_uncleared_column F mat row p) as [some | none].
    2: {exact mat. }
    set (piv_col := pr1 some).
    set (piv_row := pr1 (pr2 (pr2 some))).
    refine (gauss_clear_column _ row piv_col (m,, natlthnsn m)).
    exact (gauss_switch_row mat row piv_row).
  Defined.

  Definition gauss_clear_row_as_left_matrix
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    (p : n > 0)
    : Matrix F m m.
  Proof.
    destruct (select_uncleared_column F mat row p) as [some | none].
    2 : {exact (@identity_matrix F m). }
    set (mat_by_normal_op := (gauss_switch_row mat row (pr1 (pr2 (pr2 some))))).
    set (piv_col := pr1 some).
    set (piv_row := pr1 (pr2 (pr2 some))).
    refine ((gauss_clear_column_as_left_matrix (m,, natgthsnn m) mat_by_normal_op row
      (pr1 some)) ** _).
    refine (@switch_row_matrix _ _ row piv_row).
  Defined.

  Lemma clear_row_matrix_invertible
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    (p : n > 0)
    : @matrix_inverse F _ (gauss_clear_row_as_left_matrix mat row p).
  Proof.
    unfold gauss_clear_row_as_left_matrix.
    destruct (select_uncleared_column F mat row p) as [some | none].
    2: { destruct (natchoice0 m); try apply identity_matrix_is_inv;
         try apply nil_matrix_is_inv; try assumption;
         try apply identity_matrix_is_inv; symmetry; assumption.
    }
    apply inv_matrix_prod_is_inv.
    - apply clear_column_matrix_invertible.
    - apply switch_row_matrix_is_inv.
  Defined.

  Definition gauss_clear_rows_up_to
    { m n : nat }
    (mat : Matrix F m n)
    (row_sep : (⟦ S m ⟧%stn))
    : (Matrix F m n).
  Proof.
    destruct row_sep as [row_sep row_sep_lt_n].
    induction row_sep as [ | row_sep gauss_clear_earlier_rows].
    {exact mat. }
    refine (gauss_clear_row _ (row_sep,, row_sep_lt_n)).
    refine (gauss_clear_earlier_rows _).
    exact (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ).
  Defined.

  Definition gauss_clear_rows
      { m n : nat } (mat : Matrix F m n)
    := gauss_clear_rows_up_to mat (m,, natgthsnn m).

  (* invertible matrix, such that left-multiplication by this
     corresponds to [gauss_clear_columns_up_to]  *)
  Lemma clear_rows_up_to_as_left_matrix_internal
      { m n : nat }
      (mat : Matrix F m n)
      (row_sep : (⟦ S m ⟧%stn))
      (p : n > 0)
    : (Matrix F m m).
  Proof.
    destruct row_sep as [row_sep row_sep_lt_n].
    induction row_sep as [ | row_sep gauss_clear_earlier_rows].
    { exact (@identity_matrix F m). }
    assert (lt : row_sep < S m).
    {apply (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ). }
    set (mat_by_normal_op :=  (gauss_clear_rows_up_to mat (row_sep,, lt))).
    refine ((gauss_clear_row_as_left_matrix mat_by_normal_op
      (row_sep,, row_sep_lt_n) p ** _)).
    exact (gauss_clear_earlier_rows lt).
  Defined.

  Lemma clear_rows_up_to_as_left_matrix
    { m n : nat }
    (mat : Matrix F m n)
    (k : (⟦ S m ⟧%stn))
    (p : n > 0)
    : Matrix F m m.
  Proof.
    exact (clear_rows_up_to_as_left_matrix_internal mat k p).
  Defined.

  Lemma clear_rows_up_to_matrix_invertible
    {m n : nat}
    (iter : ⟦ S m ⟧%stn)
    (k : (⟦ m ⟧%stn))
    (mat : Matrix F m n)
    (p : n > 0)
    : @matrix_inverse F _  (clear_rows_up_to_as_left_matrix mat iter p).
  Proof.
    unfold clear_rows_up_to_as_left_matrix.
    set (pre := gauss_clear_column_as_left_matrix iter mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct iter as [pr1_ pr2_].
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
  Definition gauss_clear_all_row_segments
    { m n : nat }
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    refine (gauss_clear_rows_up_to mat (m,,_)).
    exact (natgthsnn m).
  Defined.

  Definition gauss_clear_all_column_segments_by_left_mult
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    : Matrix F m m.
  Proof.
    refine (clear_rows_up_to_as_left_matrix mat (m,,_) p).
    exact (natgthsnn m).
  Defined.

  (* TODO: remove this for the version from RowOps 
     TODO: find what this is referring to ^  *)
  Definition gauss_add_row_comp1
    { m n : nat }
    ( mat : Matrix F m n )
    ( r1 r2 : ⟦ m ⟧%stn )
    (s : F)
    (c : ⟦ n ⟧%stn)
  : (gauss_add_row mat r1 r2 s) r2 c = op1 (mat r2 c) (op2 s (mat r1 c)).
  Proof.
    unfold gauss_add_row.
    rewrite stn_eq_or_neq_refl; simpl; reflexivity.
  Defined.

  Lemma gauss_clear_column_step_inv1 {m n : nat}
        (r_pivot : ⟦m⟧%stn) (c_pivot : ⟦ n ⟧%stn)
        (r : (⟦ m ⟧%stn)) (mat : Matrix F m n)
        (p_1 : mat r_pivot c_pivot != 0%ring)
        (p_2 : r ≠ r_pivot)
    : (gauss_clear_column_step r_pivot c_pivot r mat) r c_pivot = 0%ring.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (stn_eq_or_neq r r_pivot) as [p | ?].
    { rewrite p in p_2. apply isirrefl_natneq in p_2. contradiction. }
    rewrite add_row_mat_elementary.
    2: { apply issymm_natneq; assumption. }
    rewrite gauss_add_row_comp1.
    set (a := (mat r c_pivot)).
    set (b := (mat r_pivot c_pivot)).
    rewrite <- (@ringlmultminus F), ringassoc2.
    etrans. { apply maponpaths, maponpaths, fldmultinvlax'; assumption. }
    rewrite (@rigrunax2 F).
    apply ringrinvax1.
  Defined.

  Lemma gauss_clear_column_step_inv3
    {m n : nat} (k_i : stn m) 
    (k_j : (⟦ n ⟧%stn)) (r : (⟦ m ⟧%stn))
    (mat : Matrix F m n) (j : ⟦ m ⟧%stn)
    (j' : stn n) (p : r < j)
    : (gauss_clear_column_step k_i k_j j mat) r j' = mat r j'.
  Proof.
    assert (p': r ≠ j). {apply issymm_natneq. apply natgthtoneq. assumption. }
    rewrite (gauss_clear_column_step_inv2 k_i k_j r mat j  p').
    apply idpath.
  Defined.

  Lemma gauss_clear_column_step_inv5
    {m n : nat} (mat : Matrix F m n)
    (i : (⟦ m ⟧)%stn)
    (k_i : (⟦ m ⟧)%stn) (k_j : stn n)
    (r : stn m) (c : stn n)
    : mat k_i c = 0%ring -> (gauss_clear_column_step k_i k_j i mat) r c = mat r c.
  Proof.
    intros kj_0.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _); try apply idpath;
      try contradiction.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _) as [eq | neq]; try reflexivity; simpl.
    rewrite eq, kj_0, (@ringmultx0 F), (@ringrunax1 F).
    apply idpath.
  Defined.

  Lemma gauss_clear_column_step_inv6
    {m n : nat} (mat : Matrix F m n)
    (i : (⟦ m ⟧)%stn)
    (k_i : (⟦ m ⟧)%stn) (k_j : stn n)
    : mat k_i k_j = 0%ring -> (gauss_clear_column_step k_i k_j i mat) = mat.
  Proof.
    intros kj_0.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _); try apply idpath;
      try contradiction.
    unfold gauss_add_row.
    apply funextfun; intros i_2.
    apply funextfun; intros i_3.
    unfold fldmultinv'.
    destruct (stn_eq_or_neq _ _) as [eq | neq]; try reflexivity; simpl.
    rewrite eq, (fldchoice0_left _ kj_0), (@ringmultx0 F).
    rewrite ringinvunel1, (@ringmult0x F), (@ringrunax1 F).
    reflexivity.
  Defined.

  (* Proving mat r  is unchanged after column clearance  if r > n'. *)
  Lemma gauss_clear_column_inv0
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : stn n) (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (r : ⟦ m ⟧%stn)
    (r_gt_n' : r ≥ iter)
    : (gauss_clear_column mat k_i k_j iter) r = mat r.
  Proof.
    unfold gauss_clear_column.
    destruct iter as [n' p].
    induction n' as [| n' IH]; try reflexivity.
    rewrite nat_rect_step.
    destruct (natgthorleh n' k_i). 2: { apply idpath. }
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _).
    { unfold gauss_clear_column, gauss_clear_column_step.
      unfold gauss_clear_column in IH.
      apply IH, natgthtogeh; assumption. }
    unfold gauss_clear_column in IH.
    rewrite gauss_add_row_inv0. 2: {apply natlthtoneq. assumption. }
    rewrite IH. { apply idpath. }
    apply natgthtogeh, r_gt_n'.
  Defined.

  (* if the target row r ≤  the pivot row k,
     mat r is not changed by the clearing procedure. *)
  Lemma gauss_clear_column_inv3
        { m n : nat } (k_i : (⟦ m ⟧%stn)) (k_j : stn n) (r : stn m)
        (iter : ⟦ S m ⟧%stn) (p' : r ≤ k_i)
        (mat : Matrix F m n)
        : (gauss_clear_column mat k_i k_j iter) r = mat r.
  Proof.
    unfold gauss_clear_column.
    destruct iter as [n' p].
    induction n' as [| n' IH]; try reflexivity.
    unfold gauss_clear_column.
    apply funextfun. intros q.
    rewrite nat_rect_step.
    destruct (natgthorleh _ _); try reflexivity.
    rewrite gauss_clear_column_step_inv3.
    2 : {refine (natgthgehtrans _ _ _ h _); assumption. }
    unfold gauss_clear_column in IH.
    rewrite IH; reflexivity.
  Defined.

  (* Proving the column clearing procedure equals applying step on a given row *)
  Lemma gauss_clear_column_inv1
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : stn n) (row_sep : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    : ∏ r : (⟦ m ⟧%stn), r < row_sep -> k_i < r ->
      ((gauss_clear_column  mat k_i k_j row_sep) r
      = (gauss_clear_column_step' k_i k_j r mat) r).
  Proof.
    unfold gauss_clear_column.
    destruct row_sep as [n' p].
    revert mat k_i k_j p.
    induction n' as [| n' IHn'].
    - intros mat ? ? ? r r_le_0.
      contradiction (negnatgth0n r r_le_0).
    - intros mat k_i k_j p r r_le_sn k_le_r.
      set (p' := (istransnatlth n' (S n') (S m) (natgthsnn n') p)).
      set (IHnp := IHn' mat k_i k_j p').
      destruct (natlehchoice r n') as [lt| eq]. {assumption. }
      + assert (le: r ≤ n'). { apply natlthtoleh in lt. assumption. }
        unfold gauss_clear_column.
        rewrite nat_rect_step. 
        unfold gauss_clear_column in IHnp.
        destruct (natgthorleh _ _) as [le' | gt].
        * rewrite (gauss_clear_column_step_inv2).
          2 : { apply natgthtoneq in lt. apply issymm_natneq. apply lt. }
          rewrite <- IHnp; try reflexivity; try assumption.
        * assert (absurd : n' ≤ r).
          -- apply natgthtogeh in k_le_r.
             apply (istransnatleh gt k_le_r).
          -- apply fromempty.
             apply natgehtonegnatlth in absurd.
             contradiction.
      + unfold gauss_clear_column.
        rewrite nat_rect_step.
        unfold gauss_clear_column_step'.
        destruct (natgthorleh _ _) as [gt | leh].
        2 : { unfold gauss_clear_column_step.
            destruct (stn_eq_or_neq _ _); try reflexivity.
            assert (absurd : n' ≤ r).
            { apply natgthtogeh in k_le_r. rewrite eq; apply isreflnatgeh. }
            destruct (!eq).
            apply natlehneggth in leh.
            contradiction.
        }
        rewrite <- (stn_eq_2 _ _ eq p) in *.
        destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
        { rewrite contr_eq in k_le_r. contradiction (isirreflnatgth _ k_le_r). }
        replace _ with (gauss_clear_column_step k_i k_j r mat r).
        { rewrite gauss_clear_column_step_eq; unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; try reflexivity.
          rewrite contr_eq in k_le_r; contradiction (isirreflnatgth _ k_le_r).
        }
        assert (commute :
          gauss_clear_column_step k_i k_j (n',, p) (gauss_clear_column mat k_i k_j (n',, p')) r
          =  gauss_clear_column (gauss_clear_column_step k_i k_j (n',, p) mat) k_i k_j (n',, p') r).
        { do 2 rewrite gauss_clear_column_step_eq.
          unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _) as [? | ?]; try reflexivity.
          unfold gauss_add_row.
          rewrite gauss_clear_column_inv0; simpl; try apply natlthnsn.
          generalize p. generalize p'.
          rewrite <- eq.
          intros q q'; simpl.
          destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
          2: { contradiction (isirrefl_natneq _ contr_neq). }
          apply pathsinv0.
          etrans.
          { rewrite (gauss_clear_column_inv0); try reflexivity; simpl.
            rewrite eq; apply natlthnsn. }
          destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
          2: { contradiction (isirrefl_natneq _ contr_neq). }
          apply funextfun. intros y.
          apply maponpaths, maponpaths_12.
          - do 2 apply maponpaths.
            assert (eq'': mat k_i k_j
              = (gauss_clear_column mat k_i k_j (stntonat m r,, q) k_i k_j)).
            { rewrite gauss_clear_column_inv3; try reflexivity; apply isreflnatleh. }
            destruct (!eq'').
            apply idpath.
          - rewrite gauss_clear_column_inv3; try reflexivity; apply isreflnatleh.
        }
        rewrite <- (@gauss_clear_column_inv0 m n k_i k_j (n' ,, p')).
        2: { rewrite eq. apply isreflnatleh. }
        rewrite <- (stn_eq_2 _ _ eq p) in commute.
        rewrite <- commute.
        reflexivity.
  Defined.

  Lemma gauss_clear_column_inv7
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (iter : ⟦ S m ⟧%stn) (mat : Matrix F m n)
    (p' : mat k_i k_j != 0%ring)
    : ∏ r : (⟦ m ⟧%stn), r < iter -> r > k_i
    -> ((gauss_clear_column mat k_i k_j iter) r k_j = 0%ring).
  Proof.
    destruct iter as [n' p].
    intros r r_le_n' r_gt_k.
    rewrite (gauss_clear_column_inv1  k_i k_j (n' ,, p) mat r r_le_n')
      , <- gauss_clear_column_step_eq.
    rewrite (gauss_clear_column_step_inv1 k_i k_j r mat);
      try reflexivity; try assumption.
    - apply natgthtoneq; assumption.
    - apply r_gt_k.
  Defined.

  Lemma gauss_clear_column_inv5
    { m n : nat } (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : stn n)
    (iter : ⟦ S m ⟧%stn)
    (lower : @is_lower_triangular F m n mat)
    : @is_lower_triangular F m n (gauss_clear_column mat k_i k_j iter).
  Proof.
    intros.
    unfold gauss_clear_column, is_lower_triangular, gauss_clear_column.
    destruct iter as [iter lt].
    induction iter as [| iter IHiter].
    { intros i j i_lt_j. simpl.
      apply (lower _ _ i_lt_j). }
    intros i j i_lt_j.
    rewrite nat_rect_step, gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (natgthorleh _ _) as [gt | le].
    2: { apply lower; assumption. }
    destruct (stn_eq_or_neq  _ _) as [eq | neq].
    { rewrite <- eq in gt. apply isirreflnatgth in gt. contradiction. }
    set (q := nat_rect _ _ _ _).
    set (p := istransnatlth _ _ _ _).
    unfold gauss_add_row.
    apply issymm_natneq in neq.
    destruct (stn_eq_or_neq i (iter,, lt)) as [eq | neq']; simpl.
    2: { rewrite IHiter; try reflexivity; try assumption. }
    rewrite IHiter.
    2: { rewrite eq in i_lt_j.
         simpl in i_lt_j; simpl.
         rewrite <- i_lt_j.
         reflexivity. }
    replace (q _ k_i j) with (@ringunel1 F).
    2 : { unfold q.
          rewrite IHiter; try reflexivity.
          rewrite eq in i_lt_j.
          refine (istransnatgth _ _ _ _ _).
          - apply i_lt_j.
          - apply gt.
    }
    rewrite (@rigmultx0 F), (@riglunax1 F).
    apply idpath.
  Defined.

  (* 0 in pivot row -> corresponding col is unchanged after gcc *)
  Lemma gauss_clear_column_inv6
    { m n : nat }  (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : stn n)
    (iter : ⟦ S m ⟧%stn) (j : ⟦ n ⟧%stn)
    (eq0 : mat k_i j = 0%ring)
    : ∏ i : ⟦ m ⟧%stn, gauss_clear_column mat k_i k_j iter i j = mat i j.
  Proof.
    unfold gauss_clear_column.
    destruct iter as [iter lt].
    induction iter.
    { intros i. simpl. reflexivity. }
    intros i.
    rewrite nat_rect_step, gauss_clear_column_step_eq.
    destruct (stn_eq_or_neq (iter,, lt) k_i) as [eq | ?].
    - rewrite <- eq.
      destruct (natgthorleh _ _) as [contr | ?].
      { apply isirreflnatgth in contr. contradiction. }
      reflexivity.
    - rewrite <- (IHiter (istransnatlth _ _ _ (natlthnsn iter) lt)),
        <- gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (natgthorleh _ _) as [? | ?].
      2: { rewrite IHiter. reflexivity. }
      rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _); try reflexivity.
      unfold gauss_add_row.
      destruct (stn_eq_or_neq _ _) as [eq | ?];
        try apply coprod_rect_compute_1; try apply coprod_rect_compute_2.
      + rewrite coprod_rect_compute_1.
        do 3 rewrite IHiter.
        rewrite eq0, <- eq, (@rigmultx0 F), (@rigrunax1 F).
        reflexivity.
      + rewrite coprod_rect_compute_2; reflexivity.
  Defined.

  Definition is_row_echelon_partial_1
    {m n : nat} (mat : Matrix F m n) (p : n > 0) (row_sep : ⟦ S m ⟧%stn) :=
    ∏ i_1 i_2 : ⟦ m ⟧%stn,
    ∏ j_1 j_2 : ⟦ n ⟧%stn,
     i_1 < row_sep
    -> is_leading_entry (mat i_1) j_2
    -> i_1 < i_2
    -> j_1 ≤ j_2
    -> mat i_2 j_1 = 0%ring.

  Definition is_row_echelon_partial_2
    {m n : nat} (mat : Matrix F m n) (iter : ⟦ S m ⟧%stn) :=
    ∏ (i_1 i_2 : ⟦ m ⟧%stn),
    i_1 < iter
    -> (mat i_1 = const_vec 0%ring)
    -> i_1 < i_2
    -> mat i_2 = const_vec 0%ring.

  Definition is_row_echelon_partial
    {m n : nat} (mat : Matrix F m n) (p : n > 0) (iter : ⟦ S m ⟧%stn)
    := is_row_echelon_partial_1 mat p iter × is_row_echelon_partial_2 mat iter.

  Lemma is_row_echelon_from_partial
    {m n : nat} (mat : Matrix F m n) (p : n > 0)
    : (is_row_echelon_partial mat p (m,, natgthsnn m)) -> is_row_echelon mat.
  Proof.
    unfold is_row_echelon, is_row_echelon_partial.
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    intros H ? ?; intros; use tpair.
    { intros j_1 j_2 X. refine (pr1 H i_1 i_2 j_1 _ _ _ );
      try apply X; try assumption. exact (pr2 i_1). }
    simpl; intros.
    refine ((pr2 H) i_1 i_2 _ _ _ ); try assumption.
    exact (pr2 i_1).
  Defined.

  Lemma is_row_echelon_nil_matrix
    {m n : nat} {A : Matrix F m n}
    (eq0 : n = 0)
    : (@is_row_echelon _ m n A).
  Proof.
    unfold is_row_echelon; intros i_1 i_2.
    use tpair. {intros ?; apply fromstn0; rewrite <- eq0; assumption. }
    simpl; intros eq ?.
    unfold const_vec in *; simpl.
    rewrite <- eq.
    apply funextfun; intros j.
    apply fromstn0; rewrite <- eq0; exact j.
  Defined.

  Lemma gauss_clear_row_inv2
    { m n : nat } (mat : Matrix F m n) (p : n > 0)
    (row_sep : (⟦ S m ⟧%stn)) (p' : row_sep < m)
    : is_row_echelon_partial_1 mat p row_sep
    -> is_row_echelon_partial_1 (gauss_clear_row mat (pr1 row_sep,, p')) p
        (S (pr1 row_sep),, p').
  Proof.
     intros H1.
     unfold is_row_echelon_partial_1 in *.
     unfold gauss_clear_rows_up_to.
     intros i_1 i_2 j_1 j_2 i1_lt H2 i1_lt_i2 j1_lt_j2.
     revert H2; unfold gauss_clear_row; clear p.
     destruct (natchoice0 n) as [contr_eq | p].
    { apply fromstn0. rewrite contr_eq; assumption. }
     destruct (select_uncleared_column _ _) as [some | none]; simpl.
     2: { intros isle.
          destruct (natlehchoice i_1 (pr1 row_sep)) as [gt | eq]; try assumption.
          {rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption. }
          rewrite none; intros; try reflexivity; try assumption.
          2: {exact (pr2 (j_1)). }
          apply natgthtogeh; simpl.
          rewrite <- eq; assumption.
     }
     unfold exists_first_uncleared in some.
     set (eq0  := (pr2 (pr2 (pr2 (pr2 (pr2 some)))))).
     set (leh  := (pr1 (pr2 (pr2 (pr2 some))))).
     set (neq0 := (pr1 (pr2 (pr2 (pr2 (pr2 some)))))).
     intros is_le.
     rewrite gauss_clear_column_inv3 in is_le.
     2 : { apply natlthsntoleh; assumption. }
     destruct (natlehchoice i_1 (pr1 row_sep)) as [lt | eq]. { apply natlthsntoleh; assumption.  }
     { rewrite gauss_switch_row_inv0 in is_le.
        3: { apply natlthtoneq. refine (natlthlehtrans _ _ _ lt leh). }
        2: { apply natlthtoneq; assumption. }
        rewrite gauss_clear_column_inv6.
        { rewrite gauss_switch_row_inv2.
          - rewrite (H1 i_1 i_2 j_1 j_2); try reflexivity; try assumption.
          - do 2 (rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption).
            refine (natlthlehtrans _ _ _ lt leh).
        }
        rewrite gauss_switch_row_inv2.
          + rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption.
          + do 2 (rewrite (H1 i_1 _ j_1 j_2); try reflexivity; try assumption).
            refine (natlthlehtrans _ _ _ lt leh).
    }
    destruct (natgthorleh (pr1 some) j_1).
    { rewrite gauss_clear_column_inv6; try reflexivity; try assumption.
      - unfold gauss_switch_row.
        destruct (stn_eq_or_neq _ _) as [eq' | neq]; simpl.
        + destruct (stn_eq_or_neq _ _) as [contr_eq | neq']; simpl.
          { rewrite eq0; try reflexivity; try assumption. }
          rewrite eq0; try reflexivity; try assumption.
          apply (isreflnatleh).
        + destruct (stn_eq_or_neq _ _) as [contr_eq | neq']; simpl.
          { rewrite eq0; try reflexivity; try assumption. } 
          rewrite eq0; try reflexivity; try assumption.
          unfold stntonat in *; simpl.
          rewrite <- eq.
          apply natgthtogeh; assumption.
       - rewrite gauss_switch_row_inv2;
         (rewrite eq0; try reflexivity; try assumption;
           try apply isreflnatleh).
          rewrite eq0; try reflexivity; try assumption.
    }
    destruct (natlehchoice (pr1 some) j_1) as [gt | eq']; try assumption.
    2 : { replace j_1 with (pr1 some).
          2: { rewrite (@subtypePath_prop _ _ _ _ eq'); reflexivity. }
          rewrite gauss_clear_column_inv7; try reflexivity; try assumption.
          - unfold gauss_switch_row.
            rewrite stn_eq_or_neq_refl; simpl.
            apply (pr1 (pr2 (pr2 (pr2 (pr2 some))))). 
          - exact (pr2 i_2).
          - unfold stntonat in *; simpl; rewrite <- eq; assumption.
    }
    contradiction (pr1 (pr2 (pr2 (pr2 (pr2 some))))).
    destruct (natlehchoice i_1 (pr1 row_sep)) as [lt | eq']. { apply natlthsntoleh; assumption.  }
    - rewrite gauss_switch_row_inv0 in is_le.
      3: { apply natlthtoneq. refine (natlthlehtrans _ _ _ lt leh). }
      2: { apply natlthtoneq; assumption. }
      refine (H1 _ _ _ _ _ _ _ _).
      + apply lt.
      + apply is_le.
      + refine (natlthlehtrans _ _ _ lt leh). 
      + refine (istransnatleh _  j1_lt_j2); assumption.
    - rewrite eq in *.
      assert (is_le' : is_leading_entry (mat (pr1 (pr2 (pr2 some)))) j_2).
      { unfold is_leading_entry, gauss_switch_row in *;
        destruct (stn_eq_or_neq _ _) as [? | ?];
          destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl in is_le;
          try apply is_le;
          simpl in contr_neq; rewrite <- eq in contr_neq;
          contradiction (isirrefl_natneq _ contr_neq). }
      unfold is_leading_entry in is_le'.
      rewrite (pr2 (is_le')); try reflexivity.
      refine (natlthlehtrans _ _ _ gt j1_lt_j2).
  Defined.

  Lemma gauss_clear_rows_up_to_inv0
    { m n : nat } (mat : Matrix F m n) (row_sep : (⟦ S m ⟧%stn)) (p : n > 0)
   : ∏ i_1 : ⟦ m ⟧%stn, i_1 < row_sep
  -> (gauss_clear_rows_up_to mat row_sep) i_1 = const_vec 0%ring
  -> ∏ i_2 : ⟦ m ⟧%stn, i_1 < i_2
  -> (gauss_clear_rows_up_to mat row_sep) i_2 = const_vec 0%ring.
  Proof.
    unfold is_row_echelon_partial_2.
    intros i_1 i1_lt_rowsep le_nought.
    unfold gauss_clear_rows_up_to in *.
    destruct row_sep as [row_sep lt].
    induction row_sep as [| row_sep IH].
    {simpl. contradiction (negnatgth0n i_1 i1_lt_rowsep). }
    rename  i1_lt_rowsep into i1_lt_srowsep.
    set (lt' := (istransnatlth row_sep (S row_sep) (S m) (natgthsnn row_sep) lt)).
    unfold gauss_clear_rows_up_to in *.
    rewrite nat_rect_step in *.
    unfold gauss_clear_row in *.
    destruct (natchoice0 n) as [contr_eq | gt].
    { rewrite contr_eq in p.
      contradiction (isirreflnatgth _ p). }
    revert le_nought.
    destruct (natlehchoice i_1 row_sep) as [i1_lt_rowsep | eq].
    {apply natlthsntoleh. assumption. }
    - destruct (select_uncleared_column _ _) as [some | none].
      2: { intros; simpl;
           rewrite IH; try reflexivity; try assumption.
      }
      intros ? ? i1_lt_i2.
      unfold exists_first_uncleared in some.
      set (leh := (pr1 (pr2 (pr2 (pr2 (some)))))).
      destruct (natgthorleh i_2 row_sep) as [i2_gt_rowsep | i2_le_rowsep].
      + rewrite gauss_switch_row_inv1 in le_nought; try assumption.
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natlthtoleh. assumption. }
          rewrite gauss_clear_column_inv1; try assumption.
          2: {apply (pr2 i_2). }
          unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
          { contradiction (isirreflnatgth row_sep). rewrite contr_eq in *. assumption. }
          rewrite gauss_add_row_inv1; try assumption.
          -- rewrite gauss_switch_row_inv1.
             ++ rewrite IH; try assumption; try reflexivity.
             ++ do 2 (rewrite IH; try reflexivity; try assumption).
                apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
          -- rewrite gauss_switch_row_inv1; try reflexivity; try assumption.
             ++ rewrite IH; try assumption; try reflexivity.
             ++ do 2 (rewrite IH; try assumption; try reflexivity).
                apply (natgehgthtrans _ _ _ leh i1_lt_rowsep). 
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natlthtoleh. assumption. }
          rewrite gauss_switch_row_inv0 in le_nought.
          3: { apply natlthtoneq.
               apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
          }
          2: { apply natlthtoneq. assumption. }
          do 2 (rewrite IH; try assumption; try reflexivity).
          apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
      + rewrite gauss_switch_row_inv1 in le_nought; try assumption.
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natgthtogeh in i1_lt_i2;
               apply (istransnatleh i1_lt_i2 i2_le_rowsep). }
          rewrite gauss_clear_column_inv3; try assumption.
          rewrite gauss_switch_row_inv1; try assumption.
          -- rewrite IH; try assumption; try reflexivity.
          -- do 2 (rewrite IH; try reflexivity; try assumption).
             apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
        * rewrite gauss_clear_column_inv3 in le_nought.
          2: { apply natlthtoleh in i1_lt_rowsep. assumption. }
          rewrite gauss_switch_row_inv0 in le_nought.
          3: { apply natlthtoneq.
               apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
          }
          2: {apply natlthtoneq. apply (natlthlehtrans _ _ _ i1_lt_i2 i2_le_rowsep). }
          do 2 (rewrite IH; try assumption; try reflexivity).
          apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
    - intros.
      unfold gauss_clear_row in *.
      destruct (select_uncleared_column _ _) as [col | no_col].
      2: { apply funextfun; intros j_2.
           assert (le : row_sep ≤ i_2). {apply natgthtogeh. rewrite <- eq. assumption. }
           apply no_col; try assumption.
           apply (pr2 j_2).
      }
      unfold leading_entry_compute in le_nought.
      pose (neq0 := (pr1 (pr2 (pr2 (pr2 (pr2 col)))))).
      contradiction neq0.
      refine (const_vec_eq _ _ _ _).
      rewrite <- le_nought.
      unfold gauss_switch_row.
      rewrite gauss_clear_column_inv3.
      2: { rewrite eq. apply isreflnatleh. }
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _); 
       destruct (stn_eq_or_neq _ _) as [? | contr_neq];
       try reflexivity;
       contradiction (nat_neq_to_nopath contr_neq).
  Defined.

  Lemma gauss_clear_rows_up_to_inv1
    { m n : nat } (mat : Matrix F m n)
    (p : n > 0) (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon_partial_1
        (gauss_clear_rows_up_to mat row_sep) p row_sep.
  Proof.
    pose (H:= @gauss_clear_row_inv2).
    unfold gauss_clear_rows_up_to.
    destruct row_sep as [row_sep p''].
    induction row_sep as [| row_sep IH].
    { simpl. intros ? ? ? ? contr.
      contradiction (negnatlthn0 n contr). }
    rewrite nat_rect_step.
    set (inner := nat_rect _ _ _ _).
    set (inner' := inner (istransnatlth row_sep (S row_sep) (S m) (natgthsnn row_sep) p'')).
    set (lt' := (istransnatlth _ _ _ (natgthsnn row_sep) p'')).
    apply (H m n inner' p (row_sep,, lt') p'').
    change (pr1 (row_sep,, lt')) with row_sep.
    apply IH.
  Defined.

  Lemma gauss_clear_rows_up_to_inv2
    { m n : nat } (mat : Matrix F m n)
    (p : n > 0) (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon_partial_2
        (gauss_clear_rows_up_to mat row_sep) row_sep.
  Proof.
    pose (H:= @gauss_clear_rows_up_to_inv0).
    unfold is_row_echelon_partial_2.
    unfold gauss_clear_rows_up_to in H.
    intro i_1; intros i_2 lt eq ?.
    rewrite <- (H _ _ _ row_sep p i_1 lt eq i_2); try assumption.
    destruct row_sep as [row_sep p''].
    reflexivity.
  Defined.

  Lemma is_row_echelon_1_eq
    { m n : nat } (mat : Matrix F m n)
    : is_row_echelon mat
    -> ∏ i_1 i_2 : ⟦ m ⟧%stn, ∏ j_1 j_2 : ⟦ n ⟧%stn,
       i_1 < i_2
    -> is_leading_entry (mat i_1) j_1
    -> is_leading_entry (mat i_2) j_2
    -> j_1 < j_2.
  Proof.
    destruct (natchoice0 n) as [contr_eq0 | p].
    { unfold is_upper_triangular. intros ? ? ? j.
      apply fromstn0; rewrite contr_eq0. assumption. }
    unfold is_row_echelon.
    intros H1 i_1 i_2 j_1 j_2 lt H2 H3.
    destruct (natgthorleh j_2 j_1) as [gt | leh]. {intros; apply gt. }
    destruct (H1 i_1 i_2) as [H4 H5].
    destruct (natgthorleh j_2 j_1); try assumption.
    unfold is_leading_entry in H3.
    contradiction (pr1 H3).
    apply (H4 _ _ H2 lt leh).
  Defined.

  Lemma gauss_clear_rows_up_to_inv3
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon (gauss_clear_rows_up_to mat (m,, natgthsnn m)).
  Proof.
    apply (@is_row_echelon_from_partial m _
      (gauss_clear_rows_up_to mat (m,, natgthsnn m)) p).
    unfold is_row_echelon_partial.
    use tpair.
    - apply gauss_clear_rows_up_to_inv1.
    - apply gauss_clear_rows_up_to_inv2; assumption.
  Defined.

  Lemma row_echelon_partial_to_upper_triangular_partial
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    (iter : ⟦ S m ⟧%stn)
    : @is_row_echelon_partial m n mat p iter
   -> @is_upper_triangular_partial F m n iter mat.
  Proof.
    unfold is_row_echelon_partial, is_upper_triangular_partial.
    destruct iter as [iter p'].
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    induction iter as [| iter IH].
    { simpl. intros ? ? ? ? contr. contradiction (nopathsfalsetotrue contr). }
    intros isre.
    destruct isre as [re_1 re_2].
    intros i j lt lt'.
    simpl in p'.
    assert (iter_lt_sn := (istransnatlth _ _ _ p' (natgthsnn m))).
    destruct (natlehchoice i iter) as [? | eq]. {apply natlthsntoleh; assumption. }
    - destruct (@maybe_stn_choice (⟦ n ⟧%stn) n (leading_entry_compute F (mat i))) as [t | none].
      + destruct t as [t eq].
        rewrite (IH iter_lt_sn); try reflexivity; try assumption.
        use tpair.
        * intros i_1 i_2 j_1 j_2  i1_lt_iter H ? ?.
          rewrite (re_1 i_1 i_2 j_1 j_2); try assumption; try reflexivity.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
        * simpl.
          intros i_1 i_2 i1_lt_iter ? ?.
          rewrite (re_2 i_1 i_2); try assumption; try reflexivity.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
      + pose (H := @leading_entry_compute_correct2 F n _ none).
        rewrite H; try reflexivity.
    - unfold stntonat in eq.
      assert (eq' : i = (iter,, p')).
      { apply subtypePath_prop; apply eq. }
      destruct (@maybe_stn_choice
        (⟦ n ⟧%stn) n (leading_entry_compute F (mat i))) as [t | none].
      + destruct t as [t jst].
        destruct (natlthorgeh j t) as [j_lt_t | contr_gt].
        * pose (H := @leading_entry_compute_correct1
            F n _ _ jst).
          rewrite (pr2 H); try reflexivity; try assumption.
        * pose (H1 := @leading_entry_compute_correct1
            F n _ _ jst).
          destruct (natchoice0 i) as [contr0 | ?].
          { apply fromempty; refine  (negnatgth0n _ _). rewrite contr0. apply lt. }
          destruct (prev_stn i) as [u u_lt]; try assumption.
          destruct (@maybe_stn_choice (⟦ n ⟧%stn) n
            (leading_entry_compute F (mat u))) as [prev | none_prev].
          -- destruct prev as [prev eq''].
             unfold leading_entry_compute in prev.
             pose (H2 := @leading_entry_compute_correct1
              F n _ _ eq'').
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
             ** destruct (natgthorleh u prev) as [gt | leh]; try assumption.  
                contradiction (pr1 H1).
                rewrite (re_1 u i t prev); try assumption;
                  try reflexivity; try assumption.
                --- apply natgehsntogth.
                    rewrite u_lt, eq'.
                    apply natgehsnn.
                --- apply natgehsntogth.
                     rewrite u_lt, eq'.
                     apply (isreflnatleh).
                --- destruct (natgthorleh t prev) as [gt | leh']; try assumption.
                    apply (istransnatleh contr_gt).
                    refine (istransnatleh _ leh).
                    apply natlehsntolth, natlthsntoleh.
                    rewrite u_lt; apply lt.
             ** apply natgehsntogth.
                rewrite u_lt, eq'.
                apply (isreflnatleh).
            -- rewrite (re_2 u i ); try assumption; try reflexivity.
             ++ simpl; apply natlthtolths. rewrite <- eq.
                try apply (natlehlthtrans _ _ _ contr_gt lt ).
                apply natgehsntogth.
                rewrite u_lt, eq'.
                apply (isreflnatleh).
             ++ pose (H := @leading_entry_compute_correct2
                  F n _ none_prev).
                apply funextfun; intros j'; rewrite (H j'); try reflexivity.
             ++ try apply (natlehlthtrans _ _ _ contr_gt lt).
                apply natgehsntogth.
                rewrite u_lt; rewrite eq'.
                apply (isreflnatleh).
      + pose (H := @leading_entry_compute_correct2 _ _ _ none).
        rewrite H; try reflexivity.
  Defined.

  Lemma row_echelon_to_upper_triangular
    { m n : nat }
    (mat : Matrix F m n)
    :  is_row_echelon mat
    -> @is_upper_triangular F _ _ mat.
  Proof.
    destruct (natchoice0 n) as [contr_eq0 | p].
    { unfold is_upper_triangular. intros ? ? j.
      apply fromstn0; rewrite contr_eq0; assumption. }
    intros H.
    unfold is_upper_triangular. 
    intros.
    rewrite (row_echelon_partial_to_upper_triangular_partial mat p (m,, natgthsnn m));
      try reflexivity; try assumption.
    2: {exact (pr2 i). }
    unfold is_row_echelon in H.
    unfold is_row_echelon_partial,
      is_row_echelon_partial_1, is_row_echelon_partial_2.
    use tpair.
    - intros.
      destruct (H i_1 i_2) as [H1 H2]; try assumption.
      rewrite (H1 j_1 j_2); try assumption; reflexivity.
    - simpl; intros.
      destruct (H i_1 i_2) as [H1 H2]; try assumption.
      rewrite H2; try assumption; reflexivity.
  Defined.

  Lemma clear_column_eq_matrix_def { m n : nat } (iter : ⟦ S m ⟧%stn)
    (k_i : (⟦ m ⟧%stn)) (k_j : (⟦ n ⟧%stn)) (mat : Matrix F m n)
    : ((gauss_clear_column_as_left_matrix iter mat k_i k_j) ** mat)
      = gauss_clear_column mat k_i k_j iter.
  Proof.
    intros.
    destruct iter as [iter p].
    set (p' := (stn_implies_ngt0 k_i)).
    induction iter as [| iter IH]; try apply matlunax2.
    - unfold gauss_clear_column, 
        gauss_clear_column_as_left_matrix.
      unfold gauss_clear_column, gauss_clear_column_as_left_matrix in IH.
      do 2 rewrite nat_rect_step.
      rewrite gauss_clear_column_step_eq.
      destruct (natgthorleh iter k_i) as [gt | leh].
      2 : { rewrite matlunax2; rewrite IH.
            induction iter as [| iter IH'].
            - apply idpath.
            - rewrite nat_rect_step.
              destruct (natgthorleh iter k_i) as [gt' | ?]; try reflexivity.
              apply natgehsntogth in gt'.
              apply fromempty, (isasymmnatgth _ _  gt' leh).
      }
      rewrite matrix_mult_assoc, <- IH.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _) as [eq | neq].
      { apply fromempty. apply neggth_logeq_leh in gt; try assumption.
        rewrite <- eq. apply isreflnatgeh. }
      rewrite add_row_mat_elementary.
      2 : {apply issymm_natneq, natgthtoneq. assumption. }
      apply pathsinv0, maponpaths.
      etrans.
      { set (x' := ((nat_rect _ _ _ ) iter )).
        set (x'' := x' (istransnatlth iter (S iter) (S m) (natgthsnn iter) p)).
        replace (fldmultinv' (@matrix_mult F _ _ x'' _ mat k_i k_j)%ring)
          with (fldmultinv' (mat k_i k_j)%ring).
        - reflexivity.
        - clear IH; induction iter as [| iter IH'].
          {apply fromempty. apply negnatgth0n in gt; assumption. }
          unfold x'', x'.
          rewrite nat_rect_step.
          destruct (natgthorleh iter _).
          2 : {rewrite matlunax2.
               set (f := @gauss_clear_column_as_left_matrix_inv0 m ).
               assert (obv: S iter < S m). { apply (istransnatlth _ _ _ p (natgthsnn (S m))). }
               set (f' := @gauss_clear_column_as_left_matrix_inv1 m).
               unfold gauss_clear_column_as_left_matrix in f'.
               pose (f'' := f' _ (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
                  (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))
                  mat k_i k_j k_i (isreflnatleh k_i)).
               rewrite f''; reflexivity.
          }
          set (f := @gauss_clear_column_as_left_matrix_inv1 m n).
          unfold gauss_clear_column_as_left_matrix in f.
          assert (lt: S iter < S m). { apply (istransnatlth _ _ _ p (natgthsnn (S m)) ). }
          rewrite (IH' lt); try assumption.
          2: {apply natgthtoneq. assumption. }
          pose (f' := f (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter) lt))).
          rewrite f'. 2: {apply isreflnatleh. }
          rewrite matrix_mult_assoc,
            add_row_mat_elementary.
          2: {apply issymm_natneq. apply natgthtoneq; assumption. }
          rewrite gauss_add_row_inv0.
          2: { apply natgthtoneq. assumption. }
          clear f'.
          set (f' := @gauss_clear_column_as_left_matrix_inv1 m n).
          unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
          pose (f'' := f' (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
            (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))
              mat k_i k_j k_i (isreflnatleh k_i)).
          rewrite f''.
          reflexivity.
      }
      induction iter as [| iter IH']. {apply fromempty. apply negnatgth0n in gt. assumption. }
      rewrite nat_rect_step.
      destruct (natgthorleh _ _) as [eq | neq'].
      2 : { rewrite matlunax2.
            set (f' := @gauss_clear_column_as_left_matrix_inv0 m n).
            unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
            pose (f'' := f' (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
              (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))).
            rewrite f''; try reflexivity.
            apply natlehnsn.
      }
      rewrite matrix_mult_assoc, add_row_mat_elementary.
      2: {apply natgthtoneq in eq. apply issymm_natneq. assumption. }
      rewrite gauss_add_row_inv0.
      2: {apply issymm_natneq; apply natgthtoneq; apply natgthsnn. }
      set (f' := @gauss_clear_column_as_left_matrix_inv0 m n).
      unfold gauss_clear_column_as_left_matrix in f'.
      pose (f'' := f' (iter,, (istransnatlth iter (S iter) (S m) (natgthsnn iter)
        (istransnatlth (S iter) (S (S iter)) (S m) (natgthsnn (S iter)) p)))).
      rewrite f''; try apply idpath.
      apply natlehnsn.
  Defined.

  Lemma clear_row_eq_matrix_def { m n : nat }
     (mat : Matrix F m n) (r : ⟦ m ⟧%stn) (p : n > 0):
     ((gauss_clear_row_as_left_matrix mat r p) ** mat)
    = gauss_clear_row mat r.
  Proof.
    intros.
    unfold gauss_clear_row, gauss_clear_row_as_left_matrix.
    destruct (natchoice0 n) as [contr_eq | gt].
    { apply fromempty. rewrite contr_eq in p. contradiction (isirreflnatgth _ p). }
    assert (eq : p = gt). { apply propproperty. }
    rewrite eq.
    destruct (select_uncleared_column F mat r _). 2: {apply matlunax2. }
    rewrite matrix_mult_assoc, switch_row_mat_elementary, clear_column_eq_matrix_def.
    apply idpath.
  Defined.

  Lemma gauss_clear_rows_up_to_as_matrix_eq
    { m n : nat } (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (p : n > 0) :
    ((@clear_rows_up_to_as_left_matrix_internal _ _ mat iter p) ** mat)
      = (gauss_clear_rows_up_to mat iter).
  Proof.
    intros.
    unfold clear_rows_up_to_as_left_matrix, gauss_clear_rows_up_to.
    unfold clear_rows_up_to_as_left_matrix_internal, gauss_clear_rows_up_to.
    destruct iter as [iter p'].
    induction iter as [| iter IH ]. {simpl. rewrite matlunax2. apply idpath. }
    do 2 rewrite nat_rect_step; rewrite <- IH.
    rewrite <- (clear_row_eq_matrix_def _ _ p), <- matrix_mult_assoc.
    rewrite IH; apply idpath.
  Defined.

  Lemma gauss_clear_rows_up_to_matrix_invertible { m n : nat } (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (p : n > 0) :
    (@matrix_inverse F m (@clear_rows_up_to_as_left_matrix m n mat iter p)).
  Proof.
    destruct iter as [iter lt].
    induction iter as [| iter IH].
    { unfold clear_rows_up_to_as_left_matrix,
        clear_rows_up_to_as_left_matrix_internal.
      apply identity_matrix_is_inv. }
    unfold clear_rows_up_to_as_left_matrix,
    clear_rows_up_to_as_left_matrix_internal.
    rewrite nat_rect_step.
    apply inv_matrix_prod_is_inv.
    - apply clear_row_matrix_invertible.
    - apply IH.
  Defined.

  Theorem gaussian_elimination
    {m n : nat} {A : Matrix F m n}
    : @gaussian_elimination_stmt _ F _ _ A.
  Proof.
    unfold gaussian_elimination_stmt.
    destruct (natchoice0 n) as [eq0 | gt].
    { use tpair.
      - apply (@identity_matrix F m).
      - use tpair. {apply identity_matrix_is_inv. }
        rewrite matlunax2.
        apply is_row_echelon_nil_matrix; rewrite eq0.
        apply idpath. }
    use tpair.
    - exact (@clear_rows_up_to_as_left_matrix m n A (m,, natgthsnn m) gt).
    - use tpair. {apply gauss_clear_rows_up_to_matrix_invertible. }
      rewrite gauss_clear_rows_up_to_as_matrix_eq; try assumption.
      apply (@gauss_clear_rows_up_to_inv3 _ _ A gt (m,, natgthsnn m)).
  Defined.

End Gauss.

Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.
  Local Notation Σ := (iterop_fun 0%hz op1).

  Local Notation "A ** B" := (@matrix_mult hz _ _ A _ B) (at level 80).

  (* Such code might go intro Matrix.v *)
  Definition is_smithnf_stmt
    { m n : nat } (A : Matrix I m n)
    := ∑ (S : Matrix I m m), ∑ (T : Matrix I n n),
      @is_diagonal I m n (S ** A ** T) ×
      ∏ (i j : ⟦ min n m ⟧%stn), i < j ->
      hzdiv (A (minabstn_to_bstn i) (minabstn_to_astn i))
      (A (minabstn_to_bstn j) (minabstn_to_astn i)).

  Definition MinAij { m n : nat} (A : Matrix I m n) (s : nat) (p : s < min m n) : I.
  Proof.
  Abort.

End SmithNF.