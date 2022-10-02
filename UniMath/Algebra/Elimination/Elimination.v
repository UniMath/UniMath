 (** * Matrices

Gaussian Elimination over fields.

Author: Daniel @Skantz (September 2022)
  With much help from, and thanks to, Peter LeFanu Lumsdaine
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.
Require Import UniMath.MoreFoundations.Tactics.

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

Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.
Require Import UniMath.Algebra.Elimination.Matrices.
Require Import UniMath.Algebra.Elimination.RowOps.


(** In this Module we formalize gaussian elimination by means of
    matrix multiplication equivalent elementary row operations.

    We first formalize the notion of row echelon form,
    and then present the main theorem resulting from this module.

*)

Local Notation Σ := (iterop_fun 0%rig op1).
Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).
Local Notation "R1 +pw R2" := ((pointwise _ op1) R1 R2) (at level 50, left associativity).
Local Notation "A ** B" := (@matrix_mult (_:ring) _ _ A _ B) (at level 40, left associativity).

Section Summary.

  Context {R: ring}.

  Definition is_leading_entry {n : nat}
    (v : Vector R n) (i_1 : ⟦ n ⟧%stn)
    := (v i_1 != 0%ring)
      × (∏ i_2 : ⟦ n ⟧%stn, i_2 < i_1 -> (v i_2) = 0%ring).

  (** 1 : any leading entry is strictly to the right of a previous leading entry
     2 : any zero row is below any non-zero row *)

  Definition is_row_echelon {m n : nat} (mat : Matrix R m n)
  :=
    ∏ i_1 i_2 : ⟦ m ⟧%stn,
    (∏ j_1 j_2 : ⟦ n ⟧%stn,
      is_leading_entry (mat i_1) j_1
      -> i_1 < i_2 -> j_2 ≤ j_1
      -> mat i_2 j_2 = 0%ring)
    × ((mat i_1 = const_vec 0%ring)
      -> (i_1 < i_2)
      -> (mat i_2 = const_vec 0%ring)).

  (** The first condition above implies the following of the perhaps
      more commonly seen definition of row echelon form :
      ...
      -> is_leading_entry (mat i_1) j_1
      -> is_leading_entry (mat i_2) j_2
      -> j_1 < j_2.

    (Shown later in this file) *)

  Definition gaussian_elimination_stmt {m n : nat} {A : Matrix R m n}
    := ∑ (B : Matrix R _ _), (@matrix_inverse R _ B)
      × (is_row_echelon (B ** A)).

End Summary.

(** In the following section, we provide a sub-module
    for calculating the leading entry of a vector,
    and provide suitable invness lemmata for it. *)

Section LeadingEntry.

  Context (F: fld).
  (** This section doesn’t really require full field structure, just a ring with decidable equality *)

  (** The leading entry of a (dual <-> "flipped") vector:
     [... _ _ X 0 0 0] -> index of X  (Up to a separator variable) *)
  Definition leading_entry_compute_dual_internal
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    : maybe (⟦ n ⟧%stn).
  Proof.
    destruct iter as [iter lt].
    induction iter as [| iter IH].
    { exact nothing. }
    simpl in lt.
    destruct (fldchoice0 (v (iter,, lt))).
    - refine (IH _).
      apply (istransnatlth _ _ _ lt (natgthsnn n)).
    - exact (just (iter,, lt)).
  Defined.

  (** Leading entry of a vector in terms of dual *)
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
     := leading_entry_compute_internal v (n,, natgthsnn _).

  Definition leading_entry_dual_compute {n : nat} (v : Vector F n)
     := leading_entry_compute_dual_internal v (n,, natgthsnn _).

  Lemma leading_entry_compute_eq {n : nat} (v : Vector F n)
    (i_1 i_2 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute v = just i_1)
    (e_2 : leading_entry_dual_compute
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) = just i_2)
    : i_1 = dualelement i_2.
  Proof.
    unfold leading_entry_compute, leading_entry_dual_compute,
      leading_entry_compute_internal in * |-.
    destruct (leading_entry_compute_dual_internal
      (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn _))
      as [s | contr].
    2: { contradiction (negpathsii1ii2 i_1 tt); apply pathsinv0, e_1. }
    assert (e_3 : (dualelement s) = i_1).
    { apply just_injectivity; exact (e_1). }
    assert (e_4 : s = i_2).
    { unfold just in e_2; now apply ii1_injectivity in e_2. }
    now rewrite <- e_3, e_4.
  Defined.

  Lemma leading_entry_compute_internal_eq  {n : nat} (v : Vector F n)
    (i_1 i_2 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute_internal v (n,, natgthsnn _) = just i_1)
    (e_2 : leading_entry_compute_dual_internal
      (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn _) = just i_2)
    : i_1 = dualelement i_2.
  Proof.
    now apply (leading_entry_compute_eq v).
  Defined.

  Lemma leading_entry_compute_impl {n : nat} (v : Vector F n)
    (i_1 : ⟦ n ⟧%stn)
    (e_1 : leading_entry_compute_internal v (n,, natgthsnn _) = just i_1)
    : ∑ (i_2 : ⟦ n ⟧%stn),
      leading_entry_compute_dual_internal
        (λ i : ⟦ n ⟧%stn, v (dualelement i)) (n,, natgthsnn _) = just i_2.
  Proof.
    unfold leading_entry_compute_internal in * |-.
    destruct (leading_entry_compute_dual_internal
      (λ i : (⟦ n ⟧)%stn, _) (n,, natgthsnn _)) as [s | contr].
    - assert (e_2 : dualelement s = i_1). {apply just_injectivity. apply e_1. }
      apply dualelement_eq in e_2.
      rewrite e_2.
      exists s; now rewrite e_2.
    - unfold just, nothing in e_1. contradiction (negpathsii1ii2 i_1 tt).
      apply pathsinv0, e_1.
  Defined.

  Lemma leading_entry_compute_dual_internal_inv1
    { n : nat } (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (not_nothing : (leading_entry_compute_dual_internal v iter) != nothing)
    : (∑ i : ⟦ n ⟧%stn,
             just i = (leading_entry_compute_dual_internal v iter)
           × i < iter × (v i != 0%ring)).
  Proof.
    revert not_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter as [| iter IH]. { easy. }
    rewrite nat_rect_step.
    destruct (fldchoice0 _) as [eq0| neq0].
    - intros H.
      apply IH in H.
      destruct H as [e [eq [lt neq0]]].
      exists e, eq.
      use tpair. {apply (istransnatlth _ _ _  lt (natgthsnn iter) ). }
      apply neq0.
    - intros ?.
      exists (iter,, p).
      use tpair. {reflexivity. }
      exists (natgthsnn iter); easy.
  Defined.

  Definition leading_entry_compute_dual_internal_inv2
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (not_nothing : (leading_entry_compute_dual_internal v iter) = nothing)
    : ∏ i : ⟦ n ⟧%stn, i < iter -> v i = 0%ring.
  Proof.
    intros i i_lt_iter.
    revert not_nothing.
    unfold leading_entry_compute_dual_internal.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    { apply fromempty; now apply negnatlthn0 in i_lt_iter. }
    rewrite nat_rect_step.
    destruct (fldchoice0 (v (iter,, p))) as [eq0 | ?].
    2 : { simpl. unfold just.
          intros contr.
          apply negpathsii1ii2 in contr.
          now apply fromempty.
    }
    destruct (natlehchoice i iter) as [le | eq].
      {now apply natlthsntoleh. }
    - intros H; now apply IH in H.
    - intros ?. refine (_ @ eq0). apply maponpaths, stn_eq, eq.
  Defined.

  Definition leading_entry_compute_dual_internal_inv3
    {n : nat} (v : Vector F n)
    (iter : ⟦ S n ⟧%stn)
    (i : ⟦ n ⟧%stn)
    (eq : (leading_entry_compute_dual_internal v iter) = just i)
    : (v i != 0%ring) × (∏ i' : ⟦ n ⟧%stn, i < i' -> i' < iter -> v i' = 0%ring).
  Proof.
    unfold leading_entry_compute_dual_internal.
    assert (not_nothing : leading_entry_compute_dual_internal v iter != nothing).
    { destruct (maybe_choice (leading_entry_compute_dual_internal v iter));
        try assumption.
      rewrite eq; apply negpathsii1ii2. }
    revert not_nothing.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    { intros; now use tpair. }
    set (p' := istransnatlth iter _ _ p (natgthsnn _)).
    pose (@leading_entry_compute_dual_internal n v (S _,, p)) as H.
    destruct (maybe_choice' H) as [s | ?].
    2: {contradiction. }
    unfold leading_entry_compute_dual_internal.
    rewrite nat_rect_step.
    destruct (fldchoice0 (v (iter,, p) )) as [z | nz].
    - intros H'.
      assert (not_nothing
        : leading_entry_compute_dual_internal v (S iter,, p) != nothing).
      { unfold leading_entry_compute_dual_internal.
        rewrite nat_rect_step.
        destruct (fldchoice0 _).
        2: { now destruct (!z). }
        apply H'. }
      use tpair.
      { destruct (@leading_entry_compute_dual_internal_inv1
          _ _ (S _ ,, p) not_nothing) as [? [eq' C2]].
        unfold H in s; destruct s as [s s_eq].
        rewrite eq in eq'.
        apply (just_injectivity) in eq'.
        rewrite <- eq'; apply C2.
      }
      simpl; intros i' ? ?.
      destruct (natlehchoice i' iter) as [? | eq']. {assumption. }
      { apply (IH p'); try assumption.
        unfold H in eq.
        unfold leading_entry_compute_dual_internal in eq.
        rewrite nat_rect_step in eq.
        destruct (fldchoice0 _) in eq.
        2: {contradiction. }
        unfold leading_entry_compute_dual_internal.
        unfold p'; now rewrite eq.
      }
      refine (_ @ z). apply maponpaths, stn_eq, eq'.
    - intros ?; simpl; use tpair.
      { destruct (maybe_choice
        (leading_entry_compute_dual_internal v (S _,, p)))
          as [H' | contr_eq].
        2: { destruct (!contr_eq);
             symmetry in eq; now apply negpathsii1ii2 in eq. }
        pose (C2 := @leading_entry_compute_dual_internal_inv1
          _ v (S iter,, p) H').
        destruct C2 as [? [eq' [_ ?]]].
        rewrite eq in eq'.
        apply (just_injectivity) in eq'.
        now rewrite <- eq'.
      }
      intros ? i'_gt_iter i_le_iter.
      apply natlthtonegnatgeh in i'_gt_iter.
      unfold leading_entry_compute_dual_internal in eq.
      rewrite nat_rect_step in eq.
      destruct (fldchoice0 _) as [? | eq'] in eq.
      {contradiction. }
      apply just_injectivity in eq.
      now rewrite <- eq in * |-.
  Defined.

  Lemma leading_entry_compute_internal_inv1
    {n : nat} (v : Vector F n) (i : ⟦ n ⟧%stn)
    (eq : (leading_entry_compute_internal v (n,, natgthsnn _)) = (just i))
    : is_leading_entry v i.
  Proof.
    unfold is_leading_entry.
    pose (H1 := leading_entry_compute_impl v i eq).
    destruct H1 as [i' H1].
    pose (H2 := leading_entry_compute_eq v i i' eq H1).
    unfold leading_entry_compute_internal in eq.
    pose (H := @leading_entry_compute_dual_internal_inv3 _
      (λ i : (⟦ n ⟧)%stn, v (dualelement i)) (n,, natgthsnn _) (dualelement i)).
    destruct (maybe_choice'
              (leading_entry_compute_dual_internal
              (λ i : (⟦ n ⟧)%stn, v (dualelement i))
              (n,, natgthsnn _))) as [t | contr_eq].
    2: { contradiction (@negpathsii1ii2 ((⟦ n ⟧)%stn) unit i' tt).
         unfold just in H1; rewrite <- H1.
         now rewrite contr_eq. }
    destruct t as [t H3].
    destruct (!H2).
    destruct H as [H4 H5]; try now rewrite dualelement_2x.
    use tpair; simpl. { now rewrite dualelement_2x in H4. }
    intros j lt.
    change 0%ring with (@rigunel1 F) in *.
    rewrite <- (H5 (dualelement j)).
    - now rewrite dualelement_2x.
    - apply dualelement_lt_comp; exact lt.
    - exact (pr2 (dualelement j)).
  Defined.

  Lemma leading_entry_compute_internal_inv2
    {n : nat} (v : Vector F n) (iter : ⟦ S n ⟧%stn)
    (eq_nothing : (leading_entry_compute_internal v iter) = nothing)
    : ∏ i : ⟦ n ⟧%stn, (dualelement i) < iter -> v i = 0%ring.
  Proof.
    intros i i_lt_iter.
    revert eq_nothing.
    unfold leading_entry_compute_internal,
      leading_entry_compute_dual_internal.
    destruct iter as [iter pr2_].
    induction iter as [| iter IH].
    - now apply negnatlthn0 in i_lt_iter.
    - rewrite nat_rect_step.
      destruct (fldchoice0 _) as [? | _].
      2 : { simpl; unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            now apply fromempty.
      }
      destruct (natlehchoice (dualelement i) (iter)).
      { now apply natlthsntoleh. }
      + now apply IH.
      + intros ?.
        rewrite (dualelement_eq i (iter,, pr2_));
          try easy.
        now apply subtypePath_prop.
  Defined.

  Lemma leading_entry_compute_inv1
    {n : nat} (v : Vector F n)
    (eq_nothing : (leading_entry_compute v) = nothing)
    : ∏ i : ⟦ n ⟧%stn, v i = 0%ring.
  Proof.
    intros i.
    rewrite (leading_entry_compute_internal_inv2 _ _ eq_nothing i);
      try reflexivity.
    unfold dualelement.
    destruct (natchoice0 n) as [eq | ?]; simpl.
    - apply fromstn0; now rewrite eq.
    - refine (natlehlthtrans (n - 1 - i) (n - 1) n _ _ ).
      + apply minusleh.
      + now apply natminus1lthn.
  Defined.

  Lemma leading_entry_compute_inv2
    {n : nat} (v : Vector F n)
    (i : ⟦ n ⟧%stn)
    (eq : (leading_entry_compute v) = just i)
    : is_leading_entry v i.
  Proof.
    use tpair.
    { now apply leading_entry_compute_internal_inv1. }
    simpl.
    intros i' i_gt_i'.
    pose (H2 := @leading_entry_compute_impl _ _ _ eq).
    destruct H2 as [entry compeq].
    pose (H4 := @leading_entry_compute_dual_internal_inv3 _ _ _ _ compeq).
    simpl in H4.
    destruct H4 as [neq0 eq0].
    rewrite <- (eq0 (dualelement i')).
    - now rewrite dualelement_2x.
    - apply dualelement_lt_comp'.
      rewrite dualelement_2x.
      replace (dualelement entry) with i; try assumption.
      now rewrite (@leading_entry_compute_internal_eq _ _ _ entry eq compeq).
    - exact (pr2 (dualelement i')).
  Defined.

End LeadingEntry.

Section Pivot.

  Context (F: fld).

  Definition select_pivot_row_coprod {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (k : ⟦ n ⟧%stn) :
    coprod ((∑ i: ⟦ m ⟧%stn, row_sep ≤ i × ((mat i k) != 0%ring)))
          (∏ i : ⟦ m ⟧%stn, row_sep ≤ i -> mat i k = 0%ring).
  Proof.
    pose
      (H := (leading_entry_compute_dual_internal_inv1
      _ (col mat k) (m,, natgthsnn _))).
    destruct
      (maybe_choice (leading_entry_compute_dual_internal
      _ (col mat k) (m,, natgthsnn _))) as [? | none].
    - destruct H as [entry [eq neq]]; try assumption.
      destruct (natlthorgeh entry row_sep) as [? | gt].
      2: { apply ii1; exists entry, gt; apply neq. }
      apply ii2.
      destruct
        (@leading_entry_compute_dual_internal_inv3
        _ _ (col mat k) (m,, natgthsnn _) entry (!eq)) as [H3 H4].
      intros i ke_le_i.
      unfold col, transpose, flip in * |-.
      rewrite H4; try easy.
      now apply (natlthlehtrans _ row_sep i).
      exact (pr2 i).
    - apply ii2.
      pose (H' := @leading_entry_compute_dual_internal_inv2).
      intros.
      rewrite <- (H' _ _ (col mat k) (m,, natgthsnn _) none i);
      try reflexivity.
      apply (pr2 i).
  Defined.

  Local Definition exists_first_uncleared
  {m n : nat} (mat : Matrix F m n)
  (row_sep : ⟦ m ⟧%stn) (col_iter : ⟦ S n ⟧%stn)
    := ((∑ j: ⟦ n ⟧%stn,
      j < col_iter × (∑ i: ⟦ m ⟧%stn, row_sep ≤ i × (mat i j != 0%ring)
      × ∏ i' : (⟦ m ⟧)%stn, ∏ (j' : stn n),
        row_sep ≤ i' -> j' < j -> mat i' j' = 0%ring))).

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
    destruct (natchoice0 m) as [contr_eq | _].
    { apply fromstn0; now rewrite contr_eq. }
    destruct col_iter as [col_iter lt].
    induction col_iter as [| col_iter IH].
    { right; intros ? _ ? contr.
      contradiction (negnatgth0n n contr). }
    assert (lt' : col_iter < S n).
    { simpl in lt. apply (istransnatlth _ _ _ lt (natgthsnn n)). }
    destruct (IH lt') as [IH_left | IH_right].
    - destruct IH_left as [m' [H1 [H2 H3]]].
      left; exists m', (istransnatlth _ _ _ H1 (natgthsnn col_iter)), H2.
      apply H3.
    - destruct (select_pivot_row_coprod mat row_sep
      (col_iter,, lt)) as [nz | z].
      + left;
        exists
          (col_iter,, lt)
        , (natgthsnn col_iter);
        do 3
          (use tpair; try apply nz);
          simpl; intros;
          now apply IH_right.
      + right.
        intros i rowsep_le_i j j_lt_scoliter.
        destruct (natlehchoice j col_iter) as [? | eq]; intros.
        { apply (natlehlthtrans _ _ _ j_lt_scoliter).
          apply (natgthsnn col_iter). }
        { now apply IH_right. }
        rewrite <- (z i); try assumption.
        now apply maponpaths, subtypePath_prop.
  Defined.

  (** Either finding all rows {r} >= [row_sep] are zero,
      or finding the first column segment with a non-zero element *)
  Definition select_uncleared_column
    {m n : nat} (mat : Matrix F m n)
    (row_sep : ⟦ m ⟧%stn) (p : n > 0)
    := select_uncleared_column_internal mat row_sep (n,, natgthsnn _) p.

End Pivot.

Section Gauss.

  (** - Defining procedures for gaussian elimination as
        direct operations on matrix / left matrix multiplication equivalents
      - Proving their correctness
      - First defining & showing procedure for clearing individual entries,
        then segments of columns,
        then working over multiple such segments. *)

  Context (F : fld).

  (** Clearing a target entry [i], if it does not equal the pivot row : [i] != [k_i]. *)
  Definition gauss_clear_column_step
    {m n : nat}
    (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (i : (stn m))
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    destruct (stn_eq_or_neq i k_i).
    - exact mat.
    - refine ((@add_row_mult_matrix F _ k_i i _)%ring ** mat).
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
    destruct (stn_eq_or_neq i k_i).
    - exact mat.
    - refine (add_row_mult k_i i _ mat).
      exact (- ((mat i k_j) * fldmultinv' (mat k_i k_j)))%ring.
  Defined.

  Lemma gauss_clear_column_step_eq {m n : nat}
    (k_i i: (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (mat : Matrix F m n)
    : (gauss_clear_column_step k_i k_j i mat)
      = (gauss_clear_column_step' k_i k_j i mat).
  Proof.
    unfold gauss_clear_column_step, gauss_clear_column_step'.
    destruct (stn_eq_or_neq i k_i).
    { apply idpath. }
    rewrite add_row_mult_as_matrix.
    - apply idpath.
    - now apply issymm_natneq.
  Defined.

  (** Zeroing the column segment below [k_i]:
        elements [mat {i} k_j], for {i} > [k_i]*)
  Definition gauss_clear_column { m n : nat }
    (mat : Matrix F m n) (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn)) (row_sep : ⟦ S m ⟧%stn)
    : Matrix F m n.
  Proof.
    destruct row_sep as [iter lt'].
    generalize lt'; intros lt; clear lt'.
    induction iter as [ | iter gauss_clear_column_IH ].
    { exact mat. }
    destruct (natgthorleh iter k_i). 2: {exact mat. }
    refine (gauss_clear_column_step k_i k_j (iter,, lt) _ ).
    refine (gauss_clear_column_IH _).
    now refine (istransnatlth _ _ _ (natgthsnn iter) _).
  Defined.

  Lemma gauss_clear_column_as_left_matrix
    { m n : nat }
    (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : (⟦ n ⟧%stn))
    : Matrix F m m.
  Proof.
    destruct iter as [iter p].
    generalize p; intros lt; clear p.
    induction iter as [| iter IH]. {exact (@identity_matrix F m). }
    assert (p': iter < S m).
    { apply (istransnatlth _ _ _ (natgthsnn iter) lt). }
    destruct (natgthorleh iter k_i).
    2: { exact (@identity_matrix F m ** (IH p')). }
    refine (@add_row_mult_matrix F _ k_i (iter,, lt) (- (_ * _))%ring ** _).
    - exact (mat (iter,, lt) k_j).
    - exact (fldmultinv' (mat k_i k_j)).
    - exact (IH p').
  Defined.

  Lemma gauss_clear_column_as_left_matrix_inv0
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
    { simpl; now rewrite matlunax2. }
    unfold gauss_clear_column_as_left_matrix.
    rewrite nat_rect_step.
    destruct (natgthorleh iter k_i) as [gt | _].
    2: {rewrite matlunax2; now rewrite IH. }
    assert (lt: iter < S m). {apply (istransnatlth _ _ _ (natgthsnn iter) p). }
    rewrite <- (IH lt).
    rewrite IH, matrix_mult_assoc, add_row_mult_as_matrix.
    2: {now apply issymm_natneq, natgthtoneq. }
    rewrite add_row_mult_nontarget_row.
    2: {apply natgthtoneq. apply (natlehlthtrans _ _ _  i_leh_k gt).  }
    now rewrite IH.
  Defined.

  (** Proving [mat r] is unchanged after column clearance if [r > sep]. *)
  Lemma gauss_clear_column_inv0
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : stn n) (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (r : ⟦ m ⟧%stn)
    (r_gt_sep : r ≥ iter)
    : (gauss_clear_column mat k_i k_j iter) r = mat r.
  Proof.
    unfold gauss_clear_column.
    destruct iter as [sep p].
    induction sep as [| sep IH]. {easy. }
    rewrite nat_rect_step.
    destruct (natgthorleh sep k_i). 2: { apply idpath. }
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _).
    { unfold gauss_clear_column, gauss_clear_column_step.
      unfold gauss_clear_column in IH.
      now apply IH, natgthtogeh. }
    unfold gauss_clear_column in IH.
    rewrite add_row_mult_nontarget_row. 2: {now apply natlthtoneq. }
    rewrite IH. { apply idpath. }
    apply natgthtogeh, r_gt_sep.
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
    unfold gauss_clear_column,
      gauss_clear_column_as_left_matrix.
    unfold gauss_clear_column, gauss_clear_column_as_left_matrix in IH.
    do 2 rewrite nat_rect_step.
    rewrite gauss_clear_column_step_eq.
    destruct (natgthorleh iter k_i) as [gt | leh].
    2 : { rewrite matlunax2; rewrite IH.
          induction iter as [| iter IH']; try apply idpath.
          rewrite nat_rect_step.
          destruct (natgthorleh iter k_i) as [gt' | ?]; try apply idpath.
          apply natgehsntogth in gt'.
          apply fromempty, (isasymmnatgth _ _  gt' leh).
    }
    rewrite matrix_mult_assoc, <- IH.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _) as [eq | neq].
    { apply fromempty. apply neggth_logeq_leh in gt; try assumption.
      rewrite <- eq. apply isreflnatgeh. }
      rewrite add_row_mult_as_matrix.
      2 : { now apply issymm_natneq, natgthtoneq. }
      apply pathsinv0, maponpaths_2.
      etrans.
      { replace (fldmultinv' (@matrix_mult F _ _ _ _ mat k_i k_j)%ring)
          with (fldmultinv' (mat k_i k_j)%ring); try reflexivity.
        set (f := @gauss_clear_column_as_left_matrix_inv0 m n).
        unfold gauss_clear_column_as_left_matrix in f.
        set (lt' := (istransnatlth _ _ _ (natgthsnn iter) p)).
        change iter with (pr1 (make_stn _ iter lt')).
        change (istransnatlth _ _ _ _ p) with (make_stn _ iter lt').
        rewrite f; try reflexivity; apply isreflnatleh.
      }
      apply maponpaths_1, maponpaths_2.
      rewrite IH.
      pose (H := @gauss_clear_column_inv0).
      unfold gauss_clear_column in H.
      set (lt' := (istransnatlth _ _ _  (natgthsnn iter) p)).
      change iter with (pr1 (make_stn _ iter lt')).
      change (istransnatlth _ _ _ _ p) with (make_stn _ iter lt').
      rewrite H; try easy.
      apply isreflnatleh.
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
    induction iter as [| iter IH]. { apply identity_matrix_invertible. }
    rewrite nat_rect_step.
    destruct (natgthorleh iter k_i).
    - apply inv_matrix_prod_invertible.
      { apply add_row_mult_matrix_invertible.
        now apply natlthtoneq. }
      apply IH.
    - apply inv_matrix_prod_invertible.
      { apply identity_matrix_invertible. }
      apply IH.
  Defined.

  (** The notion of clearing a row is finding the
      next uncleared column {c} (having non-zero element below [row] at {r})
      and performing elimination over it.
      We inline a pivoting operation here as well,
      switching [row] and {r} *)
  Definition gauss_clear_row
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    : Matrix F m n.
  Proof.
    destruct (natchoice0 n) as [contr_eq | p].
    { unfold Matrix, Vector; intros; apply fromstn0.
      now rewrite contr_eq. }
    destruct (select_uncleared_column _ mat row p)
      as [[piv_col [? [piv_row ?]]] | none].
    2: {exact mat. }
    refine (gauss_clear_column _ row piv_col (m,, natlthnsn _)).
    exact (@switch_row F _ _ row piv_row mat).
  Defined.

  Definition gauss_clear_row_as_left_matrix
    { m n : nat }
    (mat : Matrix F m n)
    (row : (⟦ m ⟧%stn))
    (p : n > 0)
    : Matrix F m m.
  Proof.
    destruct (select_uncleared_column F mat row p)
      as [[piv_col [_ [piv_row _]]] | none].
    2 : {exact (@identity_matrix F _). }
    set (mat_by_normal_op := (@switch_row F _ _ row piv_row mat)).
    refine ((gauss_clear_column_as_left_matrix
      (m,, natgthsnn _) mat_by_normal_op row piv_col) ** _).
    refine (@switch_row_matrix _ _ row piv_row).
  Defined.

  Lemma clear_row_eq_matrix_def { m n : nat }
     (mat : Matrix F m n) (r : ⟦ m ⟧%stn) (p : n > 0):
     ((gauss_clear_row_as_left_matrix mat r p) ** mat)
    = gauss_clear_row mat r.
  Proof.
    intros.
    unfold gauss_clear_row, gauss_clear_row_as_left_matrix.
    destruct (natchoice0 _) as [contr_eq | gt].
    { apply fromempty; rewrite contr_eq in p;
      contradiction (isirreflnatgth _ p). }
    assert (eq : p = gt). { apply propproperty. }
    rewrite eq.
    destruct (select_uncleared_column F mat r _).
    2: {apply matlunax2. }
    now rewrite matrix_mult_assoc,
      switch_row_as_matrix,
      clear_column_eq_matrix_def.
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
    2: { destruct (natchoice0 m); try apply identity_matrix_invertible;
         now apply nil_matrix_invertible, identity_matrix_invertible.
    }
    apply inv_matrix_prod_invertible.
    - apply clear_column_matrix_invertible.
    - apply switch_row_matrix_invertible.
  Defined.

  Definition gauss_clear_rows_up_to
    { m n : nat }
    (mat : Matrix F m n)
    (row_sep : (⟦ S m ⟧%stn))
    : (Matrix F m n).
  Proof.
    destruct row_sep as [row_sep row_sep_lt_n].
    induction row_sep as [| row_sep gauss_clear_earlier_rows].
    {exact mat. }
    refine (gauss_clear_row _ (row_sep,, row_sep_lt_n)).
    refine (gauss_clear_earlier_rows _).
    exact (istransnatlth _ _ _ (natgthsnn row_sep) row_sep_lt_n ).
  Defined.

  (** invertible matrix, such that left-multiplication by this
     corresponds to [gauss_clear_columns_up_to]  *)
  Lemma clear_rows_up_to_as_left_matrix
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
    set (mat_by_normal_op := (gauss_clear_rows_up_to mat (row_sep,, lt))).
    refine ((gauss_clear_row_as_left_matrix mat_by_normal_op
      (row_sep,, row_sep_lt_n) p ** _)).
    exact (gauss_clear_earlier_rows lt).
  Defined.

  Lemma gauss_clear_rows_up_to_as_matrix_eq
    { m n : nat } (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n) (p : n > 0) :
    ((@clear_rows_up_to_as_left_matrix _ _ mat iter p) ** mat)
      = (gauss_clear_rows_up_to mat iter).
  Proof.
    intros.
    unfold clear_rows_up_to_as_left_matrix, gauss_clear_rows_up_to,
      clear_rows_up_to_as_left_matrix, gauss_clear_rows_up_to.
    destruct iter as [iter ?].
    induction iter as [| iter IH ]. {simpl; now rewrite matlunax2. }
    do 2 rewrite nat_rect_step, <- IH.
    now rewrite <- (clear_row_eq_matrix_def _ _ p), <- matrix_mult_assoc.
  Defined.

  Lemma gauss_clear_rows_up_to_matrix_invertible
    {m n : nat}
    (iter : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    (p : n > 0)
    : @matrix_inverse F _ (clear_rows_up_to_as_left_matrix mat iter p).
  Proof.
    unfold clear_rows_up_to_as_left_matrix.
    set (pre := gauss_clear_column_as_left_matrix iter mat ).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct iter as [iter lt].
    induction iter as [| ? IH].
    - simpl. apply identity_matrix_invertible.
    - unfold clear_rows_up_to_as_left_matrix.
      rewrite nat_rect_step.
      apply inv_matrix_prod_invertible.
      + now apply clear_row_matrix_invertible.
      + apply IH.
  Defined.

  (** Inputting a matrix and transforming it into an upper-triangular matrix by
     elementary matrix operations or equivalent *)
  Definition gauss_clear_all_rows
    { m n : nat }
    (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    refine (gauss_clear_rows_up_to mat (m,,_));
      exact (natgthsnn m).
  Defined.

  Definition gauss_clear_all_rows_as_left_matrix
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    : Matrix F m m.
  Proof.
    refine (clear_rows_up_to_as_left_matrix mat (m,,_) p);
      exact (natgthsnn m).
  Defined.

  Definition gauss_clear_all_rows_as_matrix_eq
  { m n : nat }
  (mat : Matrix F m n)
  (p : n > 0)
  : ((gauss_clear_all_rows_as_left_matrix mat p) ** mat)
    = gauss_clear_all_rows mat.
  Proof.
    apply (gauss_clear_rows_up_to_as_matrix_eq (m,, natgthsnn _) mat p).
  Defined.

  Lemma gauss_clear_all_rows_matrix_invertible
    {m n : nat}
    (mat : Matrix F m n)
    (p : n > 0)
    : @matrix_inverse F _ (gauss_clear_all_rows_as_left_matrix mat p).
  Proof. apply gauss_clear_rows_up_to_matrix_invertible. Defined.

  Lemma gauss_clear_column_step_inv1 {m n : nat}
    (r_pivot : ⟦m⟧%stn) (c_pivot : ⟦ n ⟧%stn)
    (r : (⟦ m ⟧%stn)) (mat : Matrix F m n)
    (p_1 : mat r_pivot c_pivot != 0%ring)
    (p_2 : r ≠ r_pivot)
    : (gauss_clear_column_step r_pivot c_pivot r mat) r c_pivot = 0%ring.
  Proof.
    intros; unfold gauss_clear_column_step.
    destruct (stn_eq_or_neq r r_pivot) as [p | _].
    { rewrite p in p_2. now apply isirrefl_natneq in p_2. }
    rewrite add_row_mult_as_matrix.
    2: { now apply issymm_natneq. }
    rewrite add_row_mult_target_row.
    rewrite <- (@ringlmultminus F), ringassoc2.
    etrans. { now apply maponpaths, maponpaths, fldmultinvlax'. }
    rewrite (@rigrunax2 F); apply ringrinvax1.
  Defined.

  Lemma gauss_clear_column_step_inv2
    {m n : nat}
    (k_i : stn m) (k_j : (⟦ n ⟧%stn))
    (r : (⟦ m ⟧%stn))
    (mat : Matrix F m n)
    (j : ⟦ m ⟧%stn)
    (p : r ≠ j)
    : (gauss_clear_column_step k_i k_j j mat) r = mat r.
  Proof.
    intros.
    rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq j k_i).
    { apply idpath. }
    apply funextfun; intros ?.
    rewrite add_row_mult_nontarget_row; try reflexivity.
    now apply issymm_natneq.
  Defined.

  Lemma gauss_clear_column_step_inv3
    {m n : nat} (k_i : stn m)
    (k_j : (⟦ n ⟧%stn)) (r : (⟦ m ⟧%stn))
    (mat : Matrix F m n) (j : ⟦ m ⟧%stn)
    (j' : stn n) (p : r < j)
    : (gauss_clear_column_step k_i k_j j mat) r j' = mat r j'.
  Proof.
    assert (p': r ≠ j). {now apply issymm_natneq, natgthtoneq. }
    now rewrite (gauss_clear_column_step_inv2 k_i k_j r mat j  p').
  Defined.

  (** if the target row r ≤ the pivot row k,
     mat r is not changed by the clearing procedure. *)
  Lemma gauss_clear_column_inv1
    { m n : nat } (k_i : (⟦ m ⟧%stn)) (k_j : stn n) (r : stn m)
    (iter : ⟦ S m ⟧%stn) (p' : r ≤ k_i)
    (mat : Matrix F m n)
    : (gauss_clear_column mat k_i k_j iter) r = mat r.
  Proof.
    unfold gauss_clear_column.
    destruct iter as [sep p].
    induction sep as [| sep IH]. {easy. }
    unfold gauss_clear_column.
    apply funextfun. intros q.
    rewrite nat_rect_step.
    destruct (natgthorleh _ _)as [gt | ?]; try reflexivity.
    rewrite gauss_clear_column_step_inv3.
    2 : {now refine (natgthgehtrans _ _ _ gt _). }
    unfold gauss_clear_column in IH.
    now rewrite IH.
  Defined.

  (** Proving the column clearing procedure equals applying step on a given row *)
  Lemma gauss_clear_column_inv2
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : stn n) (row_sep : ⟦ S m ⟧%stn)
    (mat : Matrix F m n)
    : ∏ r : (⟦ m ⟧%stn), r < row_sep -> k_i < r ->
      ((gauss_clear_column mat k_i k_j row_sep) r
      = (gauss_clear_column_step' k_i k_j r mat) r).
  Proof.
    unfold gauss_clear_column.
    destruct row_sep as [sep p].
    induction sep as [| sep IH].
    { intros r r_le_0.
      contradiction (negnatgth0n r r_le_0). }
    intros r r_le_sn k_le_r.
    set (p' := istransnatlth _ _ _ (natgthsnn _) p).
    destruct (natlehchoice r sep) as [lt | eq]. {assumption. }
    - assert (le: r ≤ sep). { now apply natlthtoleh in lt. }
      unfold gauss_clear_column.
      rewrite nat_rect_step.
      unfold gauss_clear_column in IH.
      destruct (natgthorleh _ _) as [le' | gt].
      + rewrite (gauss_clear_column_step_inv2).
        2 : { apply natgthtoneq in lt; apply issymm_natneq; apply lt. }
        now rewrite <- (IH p').
      + assert (absurd : sep ≤ r).
        * apply natgthtogeh in k_le_r.
          apply (istransnatleh gt k_le_r).
        * now apply natgehtonegnatlth in absurd.
    - unfold gauss_clear_column.
      rewrite nat_rect_step.
      unfold gauss_clear_column_step'.
      destruct (natgthorleh _ _) as [gt | leh].
      2 : { unfold gauss_clear_column_step.
            destruct (stn_eq_or_neq _ _); try reflexivity.
            assert (absurd : sep ≤ r).
            { apply natgthtogeh in k_le_r. rewrite eq; apply isreflnatgeh. }
            destruct (!eq).
            now apply natlehneggth in leh.
      }
      destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
      { rewrite contr_eq in k_le_r. contradiction (isirreflnatgth _ k_le_r). }
      replace _ with (gauss_clear_column_step k_i k_j r mat r).
      { rewrite gauss_clear_column_step_eq; unfold gauss_clear_column_step'.
        destruct (stn_eq_or_neq _ _) as [contr_eq | ?]; try reflexivity.
        rewrite contr_eq in k_le_r; contradiction (isirreflnatgth _ k_le_r).
      }
      assert (commute :
         gauss_clear_column_step k_i k_j (sep,, p)
          (gauss_clear_column mat k_i k_j (sep,, p')) r
       = gauss_clear_column
          (gauss_clear_column_step k_i k_j (sep,, p) mat) k_i k_j (sep,, p') r).
      { do 2 rewrite gauss_clear_column_step_eq.
        unfold gauss_clear_column_step'.
        destruct (stn_eq_or_neq _ _); try reflexivity.
        unfold add_row_mult.
        rewrite gauss_clear_column_inv0; simpl; try apply natlthnsn.
        generalize p; generalize p'.
        rewrite <- eq.
        intros q q'; simpl.
        destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
        2: { contradiction (isirrefl_natneq _ contr_neq). }
        etrans.
        2: { rewrite (gauss_clear_column_inv0); try reflexivity; simpl.
             rewrite eq; apply natlthnsn. }
        destruct (stn_eq_or_neq _ _) as [? | contr_neq]; simpl.
        2: { contradiction (isirrefl_natneq _ contr_neq). }
        apply funextfun. intros y.
        apply maponpaths, maponpaths_12.
        - do 2 apply maponpaths.
          rewrite gauss_clear_column_inv1. {reflexivity. }
          apply isreflnatgeh.
        - rewrite gauss_clear_column_inv1; try reflexivity;
          apply isreflnatleh.
      }
      rewrite <- (@gauss_clear_column_inv0 m n k_i k_j (sep,, p')).
      2: { rewrite eq; apply isreflnatleh. }
      rewrite <- (stn_eq_2 _ _ eq p).
      rewrite <- (stn_eq_2 _ _ eq p) in commute.
      now rewrite <- commute.
  Defined.

  Lemma gauss_clear_column_inv3
    { m n : nat } (k_i : (⟦ m ⟧%stn))
    (k_j : (⟦ n ⟧%stn))
    (iter : ⟦ S m ⟧%stn) (mat : Matrix F m n)
    (p' : mat k_i k_j != 0%ring)
    : ∏ r : (⟦ m ⟧%stn), r < iter -> r > k_i
    -> ((gauss_clear_column mat k_i k_j iter) r k_j = 0%ring).
  Proof.
    destruct iter as [sep p].
    intros r r_le_sep r_gt_k.
    rewrite (gauss_clear_column_inv2  k_i k_j (sep ,, p) mat r r_le_sep)
      , <- gauss_clear_column_step_eq.
    rewrite (gauss_clear_column_step_inv1 k_i k_j r mat); try easy.
    - now apply natgthtoneq.
    - apply r_gt_k.
  Defined.

  (** 0 in pivot row -> corresponding col is unchanged after gcc *)
  Lemma gauss_clear_column_inv4
    { m n : nat }  (mat : Matrix F m n)
    (k_i : (⟦ m ⟧%stn)) (k_j : stn n)
    (iter : ⟦ S m ⟧%stn) (j : ⟦ n ⟧%stn)
    (eq0 : mat k_i j = 0%ring)
    : ∏ i : ⟦ m ⟧%stn, gauss_clear_column mat k_i k_j iter i j = mat i j.
  Proof.
    unfold gauss_clear_column.
    destruct iter as [iter lt].
    induction iter as [| iter IH]. { easy. }
    intros i.
    rewrite nat_rect_step, gauss_clear_column_step_eq.
    destruct (stn_eq_or_neq (iter,, lt) k_i) as [eq | ?].
    - rewrite <- eq.
      destruct (natgthorleh _ _) as [contr | ?].
      { now apply isirreflnatgth in contr. }
      reflexivity.
    - rewrite <- (IH (istransnatlth _ _ _ (natlthnsn iter) lt))
      , <- gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (natgthorleh _ _) as [_ | _].
      2: { now rewrite IH. }
      rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _); try reflexivity.
      unfold add_row_mult.
      destruct (stn_eq_or_neq _ _) as [eq | ?];
        try apply coprod_rect_compute_1; try apply coprod_rect_compute_2.
      + rewrite coprod_rect_compute_1.
        do 3 rewrite IH.
        now rewrite eq0, <- eq, (@rigmultx0 F), (@rigrunax1 F).
      + now rewrite coprod_rect_compute_2.
  Defined.

  (** Notion of being row echelon "up to" a separator,
      and fulfilling criteria 1 and 2 from the preamble separately.
      For proof reasons. *)
  Definition is_row_echelon_partial_1
    {m n : nat} (mat : Matrix F m n) (row_sep : ⟦ S m ⟧%stn) :=
    ∏ i_1 i_2 : ⟦ m ⟧%stn,
    ∏ j_1 j_2 : ⟦ n ⟧%stn,
     i_1 < row_sep
    -> is_leading_entry (mat i_1) j_2
    -> i_1 < i_2
    -> j_1 ≤ j_2
    -> mat i_2 j_1 = 0%ring.

  Definition is_row_echelon_1
    {m n : nat} (mat : Matrix F m n) :=
    is_row_echelon_partial_1 mat (m,, natlthnsn _).

  Definition is_row_echelon_partial_2
    {m n : nat} (mat : Matrix F m n) (iter : ⟦ S m ⟧%stn) :=
    ∏ (i_1 i_2 : ⟦ m ⟧%stn),
    i_1 < iter
    -> (mat i_1 = const_vec 0%ring)
    -> i_1 < i_2
    -> mat i_2 = const_vec 0%ring.

  Definition is_row_echelon_2
    {m n : nat} (mat : Matrix F m n) :=
    is_row_echelon_partial_2 mat (m,, natlthnsn _).

  Definition is_row_echelon_partial
    {m n : nat} (mat : Matrix F m n) (iter : ⟦ S m ⟧%stn)
    := is_row_echelon_partial_1 mat iter × is_row_echelon_partial_2 mat iter.

  Lemma is_row_echelon_from_partial
    {m n : nat} (mat : Matrix F m n)
    : (is_row_echelon_partial mat (m,, natgthsnn _))
    -> is_row_echelon mat.
  Proof.
    unfold is_row_echelon, is_row_echelon_partial.
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    intros H ? ?; intros; use tpair.
    { intros j_1 j_2 X. refine (pr1 H i_1 i_2 j_2 _ _ _ );
      try apply X; try assumption; exact (pr2 i_1). }
    simpl; intros.
    refine ((pr2 H) i_1 i_2 _ _ _ ); try assumption.
    exact (pr2 i_1).
  Defined.

  (** Step lemma*)
  Lemma gauss_clear_row_inv0
    { m n : nat } (mat : Matrix F m n) (p : n > 0)
    (row_sep : (⟦ S m ⟧%stn)) (p' : row_sep < m)
    : is_row_echelon_partial_1 mat row_sep
    -> is_row_echelon_partial_1 (gauss_clear_row mat (pr1 row_sep,, p'))
        (S (pr1 row_sep),, p').
  Proof.
     intros H1.
     unfold is_row_echelon_partial_1.
     unfold gauss_clear_rows_up_to.
     intros i_1 i_2 j_1 j_2 i1_lt H2 i1_lt_i2 j1_lt_j2.
     revert H2; unfold gauss_clear_row; clear p.
     destruct (natchoice0 n) as [contr_eq | p].
    { apply fromstn0. now rewrite contr_eq. }
     destruct (select_uncleared_column _ _)
     as [[piv_c [_ [piv_r [leh [neq0 eq0]]]]] | none]; simpl.
     2: { intros isle.
          destruct (natlehchoice i_1 (pr1 row_sep)) as [? | eq];
            try assumption.
          {rewrite (H1 i_1 i_2 j_1 j_2); try easy. }
          rewrite none; intros; try easy.
          2: {exact (pr2 (j_1)). }
          apply natgthtogeh; simpl.
          now rewrite <- eq.
     }
     intros is_le.
     rewrite gauss_clear_column_inv1 in is_le.
     2 : { now apply natlthsntoleh. }
     destruct (natlehchoice i_1 (pr1 row_sep)) as [lt | eq].
     { now apply natlthsntoleh. }
     { rewrite switch_row_other_row' in is_le.
        3: { apply natlthtoneq. refine (natlthlehtrans _ _ _ lt leh). }
        2: { now apply natlthtoneq. }
        rewrite gauss_clear_column_inv4.
        { rewrite switch_row_equal_entries.
          - now rewrite (H1 i_1 i_2 j_1 j_2).
          - do 2 (rewrite (H1 i_1 _ j_1 j_2); try easy).
            refine (natlthlehtrans _ _ _ lt leh).
        }
        rewrite switch_row_equal_entries.
          + rewrite (H1 i_1 _ j_1 j_2); easy.
          + do 2 (rewrite (H1 i_1 _ j_1 j_2); try easy).
            refine (natlthlehtrans _ _ _ lt leh).
    }
    destruct (natgthorleh piv_c j_1).
    { rewrite gauss_clear_column_inv4; try easy.
      - unfold switch_row.
        destruct (stn_eq_or_neq _ _) as [eq' | neq]; simpl.
        + destruct (stn_eq_or_neq _ _) as [contr_eq | neq']; simpl.
          { now rewrite eq0. }
          rewrite eq0; try easy.
          apply (isreflnatleh).
        + destruct (stn_eq_or_neq _ _) as [contr_eq | neq']; simpl.
          { now rewrite eq0. }
          rewrite eq0; try easy.
          rewrite <- (stn_eq_2 _ _ eq).
          now apply natgthtogeh.
      - rewrite switch_row_equal_entries;
        (rewrite eq0; try easy;
        try apply isreflnatleh).
        now rewrite eq0.
    }
    destruct (natlehchoice piv_c j_1) as [gt | eq']; try assumption.
    2 : { replace j_1 with piv_c.
          2: { now rewrite (@subtypePath_prop _ _ _ _ eq'). }
          rewrite gauss_clear_column_inv3; try easy.
          - unfold switch_row.
            rewrite stn_eq_or_neq_refl; simpl.
            apply neq0.
          - exact (pr2 i_2).
          - now rewrite <- (stn_eq_2 _ _ eq).
    }
    contradiction neq0.
    destruct (natlehchoice i_1 (pr1 row_sep)) as [lt | eq'].
      { now apply natlthsntoleh. }
    - rewrite switch_row_other_row' in is_le.
      3: { apply natlthtoneq. refine (natlthlehtrans _ _ _ lt leh). }
      2: { now apply natlthtoneq. }
      refine (H1 _ _ _ _ lt is_le _ _).
      + refine (natlthlehtrans _ _ _ lt leh).
      + now refine (istransnatleh _  j1_lt_j2).
    - rewrite eq in * |-.
      assert (is_le' : is_leading_entry (mat piv_r) j_2).
      { unfold is_leading_entry, switch_row in * |-;
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
    intros i_1 i1_lt_rowsep no_leading.
    unfold gauss_clear_rows_up_to in *.
    destruct row_sep as [row_sep lt].
    induction row_sep as [| row_sep IH].
    {contradiction (negnatgth0n i_1 i1_lt_rowsep). }
    rename i1_lt_rowsep into i1_lt_srowsep.
    set (lt' := (istransnatlth _ _ _ (natgthsnn row_sep) lt)).
    rewrite nat_rect_step in *.
    unfold gauss_clear_row in *.
    destruct (natchoice0 n) as [contr_eq | gt].
    { rewrite contr_eq in p.
      contradiction (isirreflnatgth _ p). }
    revert no_leading.
    destruct (natlehchoice i_1 row_sep) as [i1_lt_rowsep | eq].
    {apply natlthsntoleh. assumption. }
    - destruct (select_uncleared_column _ _) as [some | none].
      2: { now apply IH. }
      intros ? ? i1_lt_i2.
      unfold exists_first_uncleared in some.
      set (leh := (pr1 (pr2 (pr2 (pr2 (some)))))).
      destruct (natgthorleh i_2 row_sep) as [i2_gt_rowsep | i2_le_rowsep].
      + rewrite switch_row_equal_rows in no_leading; try assumption.
        * rewrite gauss_clear_column_inv1 in no_leading.
          2: { now apply natlthtoleh. }
          rewrite gauss_clear_column_inv2; try assumption.
          2: {apply (pr2 i_2). }
          unfold gauss_clear_column_step'.
          destruct (stn_eq_or_neq _ _) as [contr_eq | ?].
          { contradiction (isirreflnatgth row_sep).
            now rewrite contr_eq in * |-. }
          rewrite add_row_mult_source_row_zero; try assumption.
          -- rewrite switch_row_equal_rows.
             ++ now rewrite IH.
             ++ do 2 (rewrite IH; try easy).
                apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
          -- rewrite switch_row_equal_rows; try assumption.
             ++ now rewrite IH.
             ++ do 2 (rewrite IH; try assumption; try reflexivity).
                apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
        * rewrite gauss_clear_column_inv1 in no_leading.
          2: { now apply natlthtoleh. }
          rewrite switch_row_other_row' in no_leading.
          3: { apply natlthtoneq, (natgehgthtrans _ _ _ leh i1_lt_rowsep). }
          2: { now apply natlthtoneq. }
          do 2 (rewrite IH; try easy).
          apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
      + rewrite switch_row_equal_rows in no_leading; try assumption.
        * rewrite gauss_clear_column_inv1 in no_leading.
          2: { apply natgthtogeh in i1_lt_i2;
               apply (istransnatleh i1_lt_i2 i2_le_rowsep). }
          rewrite gauss_clear_column_inv1; try assumption.
          rewrite switch_row_equal_rows; try assumption.
          -- now rewrite IH.
          -- do 2 (rewrite IH; try easy).
             apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
        * rewrite gauss_clear_column_inv1 in no_leading.
          2: { now apply natlthtoleh in i1_lt_rowsep. }
          rewrite switch_row_other_row' in no_leading.
          3: { apply natlthtoneq, (natgehgthtrans _ _ _ leh i1_lt_rowsep). }
          2: {apply natlthtoneq, (natlthlehtrans _ _ _ i1_lt_i2 i2_le_rowsep). }
          do 2 (rewrite IH; try easy).
          apply (natgehgthtrans _ _ _ leh i1_lt_rowsep).
    - intros; unfold gauss_clear_row in * |-.
      destruct (select_uncleared_column _ _) as [col | no_col].
      2: { apply funextfun; intros j_2.
           assert (le : row_sep ≤ i_2).
           {apply natgthtogeh. now rewrite <- eq. }
           apply no_col; try assumption.
           apply (pr2 j_2).
      }
      unfold leading_entry_compute in no_leading.
      pose (neq0 := (pr1 (pr2 (pr2 (pr2 (pr2 col)))))).
      contradiction neq0.
      refine (const_vec_eq _ _ _ _).
      rewrite <- no_leading.
      unfold switch_row.
      rewrite gauss_clear_column_inv1.
      2: { rewrite eq. apply isreflnatleh. }
      unfold gauss_clear_column_step'.
      destruct (stn_eq_or_neq _ _);
       destruct (stn_eq_or_neq _ _) as [? | contr_neq];
       try reflexivity;
       contradiction (nat_neq_to_nopath contr_neq).
  Defined.

  Lemma gauss_clear_rows_up_to_inv1
    { m n : nat } (mat : Matrix F m n)
    (p : n > 0)
    (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon_partial_1
        (gauss_clear_rows_up_to mat row_sep) row_sep.
  Proof.
    unfold gauss_clear_rows_up_to.
    destruct row_sep as [row_sep p''].
    induction row_sep as [| row_sep IH].
    { simpl; intros ? ? ? ? contr; contradiction (negnatlthn0 n contr). }
    rewrite nat_rect_step.
    set (inner := nat_rect _ _ _ _).
    set (lt' := (istransnatlth _ _ _ (natgthsnn row_sep) p'')).
    apply (gauss_clear_row_inv0 (inner lt') p (row_sep,, lt') _), IH.
  Defined.

  Lemma gauss_clear_rows_up_to_inv2
    { m n : nat } (mat : Matrix F m n)
    (p : n > 0) (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon_partial_2
        (gauss_clear_rows_up_to mat row_sep) row_sep.
  Proof.
    intro i_1; intros i_2 lt eq ?.
    rewrite (gauss_clear_rows_up_to_inv0 _ row_sep p i_1 lt eq i_2);
      try assumption.
    now destruct row_sep.
  Defined.

  Lemma gauss_clear_rows_up_to_inv3
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    (row_sep : (⟦ S m ⟧%stn))
    : is_row_echelon (gauss_clear_rows_up_to mat (m,, natgthsnn _)).
  Proof.
    apply (@is_row_echelon_from_partial _ _
      (gauss_clear_rows_up_to mat (m,, natgthsnn _))).
    use tpair.
    - now apply gauss_clear_rows_up_to_inv1.
    - now apply gauss_clear_rows_up_to_inv2.
  Defined.

  Definition gauss_clear_all_rows_inv1
  { m n : nat } (mat : Matrix F m n) (p : n > 0)
  : is_row_echelon_1 (gauss_clear_all_rows mat).
  Proof. now apply gauss_clear_rows_up_to_inv1. Defined.

  Definition gauss_clear_all_rows_inv2
  { m n : nat } (mat : Matrix F m n) (p : n > 0)
  : is_row_echelon_2 (gauss_clear_all_rows mat).
  Proof. now apply gauss_clear_rows_up_to_inv2. Defined.

  Definition gauss_clear_all_rows_inv3
  { m n : nat } (mat : Matrix F m n) (p : n > 0)
  : is_row_echelon (gauss_clear_all_rows mat).
  Proof. apply (gauss_clear_rows_up_to_inv3 mat p (m,, natgthsnn _)). Defined.

  Lemma is_row_echelon_nil_matrix
    {m n : nat} {A : Matrix F m n}
    (eq0 : n = 0)
    : (@is_row_echelon _ m n A).
  Proof.
    unfold is_row_echelon; intros i_1 i_2.
    use tpair. {intros ?; apply fromstn0; now rewrite <- eq0. }
    simpl; intros eq ?.
    rewrite <- eq.
    apply funextfun; intros j.
    apply fromstn0; rewrite <- eq0; exact j.
  Defined.

  (** A variant on the echelon form given in the introduction. *)
  Lemma is_row_echelon_eq
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
      apply fromstn0; now rewrite contr_eq0. }
    unfold is_row_echelon.
    intros H1 i_1 i_2 j_1 j_2 lt H2 H3.
    destruct (natgthorleh j_2 j_1) as [gt | leh]. {now apply gt. }
    destruct (H1 i_1 i_2) as [H4 H5].
    destruct (natgthorleh j_2 j_1); try assumption.
    unfold is_leading_entry in H3.
    contradiction (pr1 H3).
    apply (H4 _ _ H2 lt leh).
  Defined.

  (** Row echelon form implies upper triangularity*)
  Lemma row_echelon_partial_to_upper_triangular_partial
    { m n : nat }
    (mat : Matrix F m n)
    (p : n > 0)
    (iter : ⟦ S m ⟧%stn)
    : @is_row_echelon_partial m n mat iter
   -> @is_upper_triangular_partial F m n iter mat.
  Proof.
    unfold is_row_echelon_partial, is_upper_triangular_partial.
    destruct iter as [iter p'].
    unfold is_row_echelon_partial_1, is_row_echelon_partial_2.
    induction iter as [| iter IH].
    { intros ? ? ? ? contr; contradiction (negnatlthn0 n contr). }
    intros [re_1 re_2] i j lt lt'.
    simpl in p'.
    assert (iter_lt_sn := (istransnatlth _ _ _ p' (natgthsnn m))).
    destruct (natlehchoice i iter) as [? | eq]. {now apply natlthsntoleh. }
    - destruct (maybe_choice' (leading_entry_compute _ (mat i))) as [t | none].
      + destruct t as [t eq].
        rewrite (IH iter_lt_sn); try easy.
        use tpair; simpl.
        * intros i_1 i_2 j_1 j_2 i1_lt_iter H ? ?.
          rewrite (re_1 i_1 i_2 j_1 j_2); try easy.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
        * intros i_1 i_2 i1_lt_iter ? ?; rewrite (re_2 i_1 i_2); try easy.
          apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
      + now rewrite (@leading_entry_compute_inv1 _ n _ none).
    - unfold stntonat in eq.
      assert (eq' : i = (iter,, p')). { apply subtypePath_prop; apply eq. }
      destruct (maybe_choice' (leading_entry_compute F (mat i))) as [t | none].
      2: { now rewrite (@leading_entry_compute_inv1 _ _ _ none). }
      destruct t as [t jst].
      destruct (natlthorgeh j t) as [j_lt_t | contr_gt].
      + pose (H := @leading_entry_compute_inv2 _ n _ _ jst).
        rewrite (pr2 H); try easy.
      + pose (H1 := @leading_entry_compute_inv2 _ n _ _ jst).
        destruct (natchoice0 i) as [contr0 | ?].
        { apply fromempty; refine (negnatgth0n _ _); rewrite contr0; apply lt. }
        destruct (prev_stn i) as [u u_lt]; try assumption.
        destruct (maybe_choice' (leading_entry_compute _ (mat u)))
                   as [prev | none_prev].
        * destruct prev as [prev eq''].
          unfold leading_entry_compute in prev.
          pose (H2 := @leading_entry_compute_inv2 _ n _ _ eq'').
          contradiction (pr1 H2); rewrite (IH iter_lt_sn); try easy.
          use tpair; simpl.
          -- intros i_1 i_2 j_1 j_2 i1_lt_iter H' ? ?.
             rewrite (re_1 i_1 i_2 j_1 j_2); try easy.
             apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
          -- intros i_1 i_2 i1_lt_iter ? ?; rewrite (re_2 i_1 i_2); try easy.
             apply (istransnatlth _ _ _ i1_lt_iter (natgthsnn iter)).
          -- destruct (natgthorleh u prev) as [gt | leh]; try assumption.
             contradiction (pr1 H1); rewrite (re_1 u i t prev); try easy.
             ++ apply natgehsntogth; rewrite u_lt, eq'; apply natgehsnn.
             ++ apply natgehsntogth; rewrite u_lt, eq'; apply isreflnatleh.
             ++ destruct (natgthorleh t prev) as [gt | leh']; try assumption.
                apply (istransnatleh contr_gt); refine (istransnatleh _ leh).
                apply natlehsntolth, natlthsntoleh; rewrite u_lt; apply lt.
          -- apply natgehsntogth; rewrite u_lt, eq'; apply (isreflnatleh).
        * rewrite (re_2 u i ); try easy.
          -- simpl; apply natlthtolths. rewrite <- eq.
             try apply (natlehlthtrans _ _ _ contr_gt lt ).
             apply natgehsntogth; rewrite u_lt, eq'; apply isreflnatleh.
          -- pose (H := @leading_entry_compute_inv1 _ n _ none_prev).
             apply funextfun; intros j'; rewrite (H j'); try reflexivity.
          -- try apply (natlehlthtrans _ _ _ contr_gt lt).
             apply natgehsntogth; rewrite u_lt, eq'; apply isreflnatleh.
  Defined.

  Lemma row_echelon_to_upper_triangular
    { m n : nat }
    (mat : Matrix F m n)
    : is_row_echelon mat
    -> @is_upper_triangular F _ _ mat.
  Proof.
    destruct (natchoice0 n) as [contr_eq0 | p].
    { unfold is_upper_triangular. intros ? ? j.
      apply fromstn0; now rewrite contr_eq0. }
    intros H; unfold is_upper_triangular; intros.
    rewrite (row_echelon_partial_to_upper_triangular_partial
      mat p (m,, natgthsnn _));
      try easy.
    2: {exact (pr2 i). }
    unfold is_row_echelon in H.
    unfold is_row_echelon_partial,
      is_row_echelon_partial_1, is_row_echelon_partial_2.
    use tpair; intros i_1 i_2 j_1 j_2; intros; simpl.
    - destruct (H i_1 i_2) as [H1 _]; try assumption.
      now rewrite (H1 j_2 j_1).
    - destruct (H i_1 i_2) as [_ H2]; try assumption.
      now rewrite H2.
  Defined.

  Local Lemma gauss0
  {m n : nat} {A : Matrix F m n}
    {eq0 : 0 = n}
  : @gaussian_elimination_stmt _ _ _ A.
  Proof.
    exists (@identity_matrix F m).
    use tpair. {apply identity_matrix_invertible. }
    rewrite matlunax2.
    apply is_row_echelon_nil_matrix; now rewrite eq0.
  Defined.

  Theorem gaussian_elimination
    {m n : nat} {A : Matrix F m n}
    : @gaussian_elimination_stmt _ _ _ A.
  Proof.
    destruct (natchoice0 n) as [eq0 | gt]. { now refine gauss0. }
    exists (@gauss_clear_all_rows_as_left_matrix m n A gt).
    use tpair. {apply gauss_clear_all_rows_matrix_invertible. }
    rewrite gauss_clear_all_rows_as_matrix_eq; try assumption.
    now apply gauss_clear_all_rows_inv3.
  Defined.

End Gauss.
