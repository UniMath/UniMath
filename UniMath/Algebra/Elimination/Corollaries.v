Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Algebra.Matrix.

Require Import UniMath.PAdics.lemmas.

Require Import UniMath.Algebra.Domains_and_Fields.
Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.
Require Import UniMath.Algebra.Elimination.Matrices.
Require Import UniMath.Algebra.Elimination.Elimination.

(**
  In this module, we define a back-substitution procedure that works on
  nxn matrices that are upper triangular with all non-zero diagonal.

  We use this procedure to show that any nxn matrix either not invertible,
  or calculate its inverse.

  Author: Daniel @Skantz (September 2022)
*)

Definition matrix_inverse_or_non_invertible_stmt
  { n : nat } {F : fld}
  (A : Matrix F n n)
  := coprod (@matrix_inverse F n A)
            (@matrix_inverse F n A -> empty).

Definition back_sub_stmt
  { n : nat } {F : fld}
  (mat : Matrix F n n)
  (vec : Vector F n)
  (ut : @is_upper_triangular F _ _ mat)
  (df : @diagonal_all_nonzero F _ mat)
  := ∑ v : (Vector F n),
    (@matrix_mult F _ _ mat _ (col_vec v)) = (col_vec vec).

Section BackSub.

  Context (F : fld).

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 40, left associativity).
  Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).

  (** output: a solution [x] to [mat ** x = b] if one exists
     - given mat upper triangular, non-zero diagonal. *)
  Definition back_sub_step { n : nat } ( row : (⟦ n ⟧)%stn )
    (mat : Matrix F n n) (x : Vector F n) (b : Vector F n) : Vector F n.
  Proof.
    intros i.
    destruct (nat_eq_or_neq row i).
    - exact (((b i) * fldmultinv' (mat i i))
           - ((Σ (mat i *pw x) - (x  i)* (mat i i))
           * (fldmultinv' (mat i i))))%ring.
    - exact (x i).
  Defined.

  (** procedure gives [x_i] s.t. [(mat ** x)_i = b_i], given previous assumptions *)
  Lemma back_sub_step_inv0 { n : nat }
    (row : ⟦ n ⟧%stn) (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (p: @is_upper_triangular F n n mat)
    (p' : (mat row row != 0)%ring)
    : (mat ** (col_vec (back_sub_step row mat x b))) row = (col_vec b) row.
  Proof.
    unfold back_sub_step, col_vec.
    unfold fldmultinv'.
    rewrite matrix_mult_eq; unfold matrix_mult_unf, pointwise.
    set (m := n - (S row)).
    assert (split_eq : n = (S row) + m).
    { unfold m.
      rewrite natpluscomm, minusplusnmm.
      - apply idpath.
      - exact (pr2 row). }
    destruct (stn_inhabited_implies_succ row)
      as [s_row s_row_eq], (!s_row_eq).
    apply funextfun; intros ?.
    rewrite (@vecsum_dni _ (s_row) _ row)
    , nat_eq_or_neq_refl.
    destruct (fldchoice0 _) as [? | neq].
    {contradiction. }
    etrans.
    { apply maponpaths_2; apply maponpaths.
      apply funextfun; intros q.
      unfold funcomp.
      now rewrite (nat_eq_or_neq_right (dni_neq_i row q)). }
    rewrite (@vecsum_dni F (s_row) _ row).
    etrans.
    { apply maponpaths.
      etrans.
      { apply maponpaths.
        rewrite (@ringcomm2 F).
        apply maponpaths.
        now rewrite (@ringcomm2 F). }
      apply (@ringminusdistr F (mat row row)).
    }
    etrans.
    { apply maponpaths; apply map_on_two_paths.
      rewrite <- (@rigassoc2 F), (@fldmultinvrax F).
      { now rewrite (@riglunax2 F). }
      apply maponpaths.
      rewrite <- (@rigassoc2 F), (@fldmultinvrax F).
      apply (@riglunax2 F). }
    etrans.
    { do 3 apply maponpaths.
      now rewrite (@rigcomm2 F), (@ringplusminus F). }
    rewrite (@rigcomm1 F); rewrite (@rigassoc1 F).
    now rewrite (@ringlinvax1 F), (@rigrunax1 F).
  Defined.

  (** [back_sub_step] only modifies target element *)
  Lemma back_sub_step_inv1
    { n : nat } (row : ⟦ n ⟧%stn)
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    : ∏ i : ⟦ n ⟧%stn, i ≠ row ->
      (col_vec (back_sub_step row mat x b) i = (col_vec x) i).
  Proof.
    intros i ne.
    unfold back_sub_step, col_vec.
    apply funextfun. intros j; simpl.
    destruct (nat_eq_or_neq row i) as [eq | ?];
      try apply idpath.
    rewrite eq in ne.
    contradiction (isirrefl_natneq _ ne).
  Defined.

  Lemma back_sub_step_inv2
    { n : nat }
    (row : ⟦ n ⟧%stn)
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (is_ut: @is_upper_triangular F n n mat)
    : ∏ i : ⟦ n ⟧%stn, i ≥ row
    -> (mat i i != 0)%ring
    -> (mat ** (col_vec x)) i = (col_vec b) i
    -> (mat ** (col_vec (back_sub_step row mat x b))) i = (col_vec b) i.
  Proof.
    unfold transpose, flip.
    intros i le neq0 H.
    rewrite <- H.
    destruct (natlehchoice row i) as [lt | eq]. {apply le. }
    - rewrite matrix_mult_eq in *.
      apply pathsinv0.
      rewrite matrix_mult_eq.
      unfold matrix_mult_unf in *.
      apply funextfun; intros ?.
      apply maponpaths, funextfun; intros i'.
      destruct (stn_eq_or_neq i' (row)) as [eq | neq].
      2 : { now rewrite back_sub_step_inv1. }
      replace (mat i i') with (@ringunel1 F).
      2 : { rewrite is_ut; try reflexivity; now rewrite eq. }
      now do 2 rewrite (@rigmult0x F).
    - rewrite (stn_eq _ _ eq)
      , back_sub_step_inv0; try assumption.
      now rewrite H.
  Defined.

  (** Back-substituting repeatedly using step procedure defined earlier.
     Carries an additional [row] parameter for proof reasons. *)
  Definition back_sub_internal
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (sep : ⟦ S n ⟧%stn)
    (row : ⟦ S n ⟧%stn)
    : Vector F n.
  Proof.
    destruct sep as [sep p].
    induction sep as [| m IH]. {exact x. }
    destruct (natlthorgeh (dualelement (m,, p)) row).
    2: {exact x. }
    refine (back_sub_step (dualelement (m,, p)) mat (IH _) b).
    apply (istransnatlth _ _ _ (natgthsnn m) p).
  Defined.

  Lemma back_sub_internal_inv0
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (sep : ⟦ S n ⟧%stn)
    (row : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i >= row
    -> (col_vec (back_sub_internal mat x b sep row)) i = (col_vec x) i.
  Proof.
    destruct sep as [sep p].
    induction sep as [| sep IH].
    { intros i H; now destruct (natchoice0 (S n)) in H. }
    unfold back_sub_internal.
    intros i i_lt_row.
    rewrite nat_rect_step.
    destruct (natlthorgeh _ _) as [lt | geh].
    2: {reflexivity. }
    assert (p': sep < S n). { apply (istransnatlth _ _ _ (natgthsnn sep) p). }
    rewrite <- (IH p'); try assumption.
    unfold back_sub_internal.
    rewrite back_sub_step_inv1; try easy.
    {apply maponpaths_2, maponpaths, proofirrelevance, propproperty. }
    apply natgthtoneq.
    refine (natlthlehtrans _ _ _ lt i_lt_row).
  Defined.

  Lemma back_sub_internal_inv1
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (sep : ⟦ S n ⟧%stn)
    (row : ⟦ S n ⟧%stn)
    : ∏ i : stn n, i >= row
    -> (back_sub_internal mat x b sep row) i = x i.
  Proof.
    intros.
    rewrite (@col_vec_inj_pointwise F n
      (back_sub_internal mat x b sep row) x i).
    - apply idpath.
    - now apply (back_sub_internal_inv0).
  Defined.

  Lemma back_sub_internal_inv2
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (sep : ⟦ S n ⟧%stn)
    (row : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i ≥ (dualelement sep)
    -> (mat i i != 0)%ring
    -> i < row
    -> (mat ** (col_vec (back_sub_internal mat x b sep row))) i = (col_vec b) i.
  Proof.
    unfold transpose, flip.
    intros i i_le_sep neq0 lt.
    unfold back_sub_internal.
    destruct sep as [sep p].
    induction sep as [| sep IH].
    { apply fromempty, (dualelement_sn_stn_nge_0 _ _ i_le_sep). }
    rewrite nat_rect_step.
    destruct (natlehchoice (dualelement (sep,, p)) i) as [leh | eq].
    { refine (istransnatleh _ i_le_sep).
      now apply (@dualelement_sn_le). }
    - destruct (natlthorgeh _ _) as [? | contr_geh].
      2 : { contradiction (isirreflnatlth _
              (natlthlehtrans _ _ _ (istransnatlth _ _ _ leh lt) contr_geh)).
      }
      rewrite back_sub_step_inv2; try easy.
      { unfold dualelement. unfold dualelement in leh.
        destruct (natchoice0 _) as [contr_eq | ?].
        {apply fromstn0. now rewrite contr_eq. }
        now apply natgthtogeh. }
      rewrite IH; try reflexivity.
        now apply dualelement_lt_to_le_s.
    - destruct (natlthorgeh _ _) as [? | contr_geh].
      + rewrite (stn_eq _ _ eq).
        now rewrite back_sub_step_inv0.
      + rewrite <- (stn_eq _ _ eq) in lt.
        contradiction (isirreflnatlth _ (natlthlehtrans _ _ _ lt contr_geh)).
  Defined.

  Definition back_sub
    {n : nat}
    (mat : Matrix F n n)
    (vec : Vector F n)
  := back_sub_internal mat vec vec (n,, natgthsnn _) (n,, natgthsnn _).

  Lemma back_sub_inv0
    { n : nat }
    (mat : Matrix F n n) (b : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (df : @diagonal_all_nonzero F _ mat)
    : back_sub_stmt mat b ut df.
  Proof.
    exists (back_sub mat b).
    intros; unfold back_sub.
    destruct (natchoice0 n) as [eq0 | ?].
    { apply funextfun. intros i. apply fromstn0. now rewrite eq0. }
    apply funextfun; intros i.
    apply back_sub_internal_inv2;
      try assumption; unfold dualelement.
    destruct (natchoice0 _) as [eq0 | ?].
    { apply fromempty; now apply negpaths0sx in eq0. }
    simpl; now rewrite minus0r, minusnn0.
    apply df.
    exact (pr2 i).
  Defined.

End BackSub.

Section BackSubZero.

  (** Showing that right invertible matrix, upper triangular,
     must have fully non-zero diagonal. *)

  Context {F : fld}.

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 40, left associativity).
  Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).

  Local Notation "0" := (@ringunel1 F).

  (** Ax = 0 would have two solutions for x, but A invertible... *)
  Lemma back_sub_zero
    { n : nat }
    (mat : Matrix F n n)
    (ut : @is_upper_triangular F _ _ mat)
    (zero: ∑ i : stn n, (mat i i = 0)%ring
      × (forall j : stn n, j < i -> ((mat j j) != 0)%ring))
    (inv : @matrix_left_inverse F _ _ mat)
    : empty.
  Proof.
    unfold transpose, flip.
    destruct (natchoice0 (pr1 zero)) as [eq0_1 | gt].
    { apply (zero_row_to_non_right_invertibility (transpose mat) (pr1 zero));
        try assumption.
      apply funextfun; intros k.
      destruct (natchoice0 k) as [eq0_2 | ?].
      - rewrite <- (pr1 (pr2 zero)).
        unfold const_vec.
        rewrite eq0_1 in eq0_2.
        now rewrite (stn_eq _ _ eq0_2).
      - unfold transpose, flip.
        rewrite ut; try reflexivity.
        now rewrite <- eq0_1.
      - now apply matrix_left_inverse_to_transpose_right_inverse.
    }
    assert (contr_exists :  ∑ x : (Vector F n), (∑ i' : stn n,
      (x i' != 0) × (mat ** (col_vec x)) = (@col_vec F _ (const_vec 0)))).
    2: { assert (eqz : (mat ** (@col_vec F _ (const_vec 0)))
          = (@col_vec F _ (const_vec 0))).
        { rewrite matrix_mult_eq; unfold matrix_mult_unf.
          apply funextfun; intros k.
          unfold col_vec, const_vec.
          etrans.
          { rewrite vecsum_eq_zero.
            - apply idpath.
            - intros ?; apply rigmultx0. }
          reflexivity.
        }
        assert (contr_eq' : (@ringunel1 F) != (@ringunel1 F)).
        2: {contradiction. }
        rewrite <- eqz in contr_exists.
        destruct contr_exists as [x1 [x2 [x3 contr_exists]]].
        destruct inv as [inv isinv].
        rewrite <- contr_exists in eqz.
        assert (eq : @matrix_mult F _ _ inv _
          (@matrix_mult F _ _ mat _ (col_vec x1)) =
           @matrix_mult F _ _ inv _ (@col_vec F _ (const_vec 0))).
        {now rewrite eqz. }
        rewrite <- matrix_mult_assoc, isinv, matlunax2 in eq.
        pose (eq' := @matrix_mult_zero_vec_eq _ _ _ inv).
        change 0%ring with (@rigunel1 F) in * |-.
        unfold col_vec, const_vec in * |-.
        rewrite eq' in eq.
        destruct zero as [zero iszero].
        apply toforallpaths in eq.
        set (idx0 := (make_stn _ 0 (stn_implies_ngt0 zero))).
        assert (contr_eq' :
          (λ (_ : _) (_ : _), (@rigunel1 F)) idx0 =
          (λ (_ : _) (_ : (⟦ 1 ⟧)%stn), x1 x2) idx0
        ). { now rewrite eq. }
        apply toforallpaths in contr_eq'.
        change 0%rig with (@rigunel1 F) in * |-.
        rewrite contr_eq' in x3.
        2: { exact (make_stn _ _ (natgthsnn 0)). }
        contradiction.
    }
    destruct zero as [zero iszero].
    use tpair.
    { apply back_sub_internal.
      - exact mat.
      - intros j.
        destruct (natlthorgeh (pr1 zero) j).
        + exact 0.
        + destruct (natgehchoice (pr1 zero) j); try assumption.
          * exact 0.
          * exact (@rigunel2 F).
      - exact (const_vec 0).
      - exact (n,, natgthsnn _).
      - exact (pr1 zero,, (istransnatlth _ _ _ (pr2 zero) (natgthsnn _))).
    }
    exists zero.
    use tpair.
    - rewrite back_sub_internal_inv1; try assumption.
      2: {apply isreflnatleh. }
      destruct (natlthorgeh _ _) as [lt | ge].
      * contradiction (isirreflnatgth _ lt).
      * simpl; clear gt. destruct (natgehchoice _ _) as [gt | eq].
        {contradiction (isirreflnatlth _ gt). }
        apply (@nonzeroax F).
    - apply funextfun; intros j.
      destruct (natlthorgeh j zero) as [? | ge].
      + rewrite back_sub_internal_inv2; try easy.
        * unfold dualelement.
          destruct (natchoice0 (S n)).
          {simpl. now rewrite minus0r, minusxx. }
          rewrite coprod_rect_compute_2; simpl.
          now rewrite minus0r, minusxx.
        * now apply (pr2 iszero).
      + rewrite matrix_mult_eq; unfold matrix_mult_unf.
        unfold col_vec, const_vec.
        apply funextfun; intros ?.
        eapply (@vecsum_eq_zero F).
        intros k.
        destruct (natgthorleh j k) as [? | le].
        {rewrite ut; try assumption; apply rigmult0x. }
        destruct (stn_eq_or_neq (zero) k) as [eq | ?].
        * rewrite <- eq in *.
          rewrite <- (stn_eq _ _ (isantisymmnatgeh _ _ le ge)).
          rewrite (pr1 iszero); apply rigmult0x.
        * etrans. 2: {apply rigmultx0. }
          apply maponpaths.
          rewrite back_sub_internal_inv1; try assumption.
          2: {apply (istransnatleh ge le). }
          destruct (natlthorgeh _ _) as [? | ?]; try reflexivity.
          destruct (natgehchoice _ _) as [? | eq];
            try reflexivity.
          rewrite (stn_eq _ _ eq) in * |-.
          contradiction (isirrefl_natneq k).
  Defined.


End BackSubZero.

Section Locals.

  (** Helper functions *)

  Context {F: fld}.
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 40, left associativity).

  Local Definition flip_fld_bin
  (e : F) : F.
  Proof.
  destruct (fldchoice0 e).
  - exact 1%ring.
  - exact 0%ring.
  Defined.

  Local Definition flip_fld_bin_vec
  {n : nat} (v : Vector F n) := λ i : (stn n), flip_fld_bin (v i).

  Local Definition vector_all_nonzero_compute_internal
  {n : nat} (v : Vector F n)
  : coprod (∏ j : (stn n), (v j) != 0%ring)
          (∑ i : (stn n), ((v i) = 0%ring)
        × (forall j : stn n, (j < (pr1 i) -> (v j) != 0%ring))).
  Proof.
  pose (leading_entry := leading_entry_compute F (flip_fld_bin_vec v)).
  destruct (maybe_choice' leading_entry) as [some | none].
  - right; use tpair; simpl. {apply some. }
    pose (leading_entry_inv := @leading_entry_compute_inv2 F _
      (flip_fld_bin_vec v) (pr1 some) (pr2 some)).
    destruct leading_entry_inv as [some_neq_0 prev_eq_0].
    unfold is_leading_entry, flip_fld_bin_vec, flip_fld_bin in * |-.
    destruct (fldchoice0 (v _)); try contradiction.
    use tpair; try assumption.
    intros j lt.
    pose (eq := prev_eq_0 _ lt).
    generalize eq; clear eq prev_eq_0.
    now destruct (fldchoice0 (v j)).
  - left; intros j.
    pose (prev_eq_0 := @leading_entry_compute_inv1 _ _
      (flip_fld_bin_vec v) none j).
    rewrite <- prev_eq_0; try apply (pr2 (dualelement j)); clear prev_eq_0.
    destruct (fldchoice0 (v j)) as [eq | neq];
      unfold is_leading_entry, flip_fld_bin_vec, flip_fld_bin in *.
    + destruct (fldchoice0 _); try assumption.
      rewrite eq; intros contr_neq.
      contradiction (nonzeroax _ (pathsinv0 contr_neq)).
    + destruct (fldchoice0 (v j)) as [contr_eq | ?]; try assumption.
      now rewrite contr_eq in neq.
  Defined.

  Local Definition vector_all_nonzero_compute
  {n : nat} (v : Vector F n)
  : coprod (∏ j : (stn n), (v j) != 0%ring)
           (∑ i : (stn n), (v i)  = 0%ring).
  Proof.
  pose (H := @vector_all_nonzero_compute_internal n v).
  destruct H as [l | r].
  - left; assumption.
  - right; exists (pr1 r)
    ; exact (pr1 (pr2 r)).
  Defined.

End Locals.

Section Inverse.

  (** Some additional properties of matrix inverses,
      having now defined Gaussian elimination and
      back-substitution.

      Computes a matrix inverse or shows it is non-invertible. *)

  Context (F : fld).

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 40, left associativity).
  Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).

  (** Construct the inverse,
    if additionally mat is upper triangular with non-zero diagonal *)
  Definition upper_triangular_right_inverse_construction
    { n : nat }
    (mat : Matrix F n n)
    := transpose (λ i : (stn n), (back_sub _ mat (@identity_matrix F n i))).

  Lemma left_invertible_upper_triangular_to_diagonal_all_nonzero
    {n : nat }
    (A : Matrix F n n)
    (p : @is_upper_triangular F _ _ A)
    (p': @matrix_left_inverse F _ _ A)
    : (@diagonal_all_nonzero F _ A).
  Proof.
    destruct (@vector_all_nonzero_compute_internal _ _ (@diagonal_sq F _ A))
      as [l | r].
    { unfold diagonal_all_nonzero; intros; unfold diagonal_sq in l; apply l. }
    unfold diagonal_sq in r; apply fromempty; now apply (@back_sub_zero _ _ A p).
  Defined.

  Lemma right_inverse_construction_inv
    { n : nat } (mat : Matrix F n n)
    (ut : @is_upper_triangular F _ _ mat)
    (df: @diagonal_all_nonzero F _ mat)
    : (mat ** (upper_triangular_right_inverse_construction mat))
      = (@identity_matrix F n).
  Proof.
    apply funextfun; intros i.
    unfold matrix_mult, row, col, transpose, flip.
    apply funextfun; intros ?.
    unfold upper_triangular_right_inverse_construction.
    rewrite (@col_vec_mult_eq F _ _ mat
      (λ y : (⟦ n ⟧)%stn, upper_triangular_right_inverse_construction mat y x)
        (@identity_matrix F _ x)).
    - destruct (stn_eq_or_neq i x) as [eq | neq].
      { now rewrite eq. }
      rewrite id_mat_ij; try rewrite id_mat_ij; try easy.
      apply (issymm_natneq _ _ neq).
    - unfold upper_triangular_right_inverse_construction.
      pose (back_sub_inv := @back_sub_inv0).
      destruct (natchoice0 n) as [eq | ?].
      {apply fromstn0; now rewrite eq. }
      apply (back_sub_inv _ _ _ _ ut df).
  Defined.

  Lemma left_inverse_implies_right { n : nat } (A B: Matrix F n n)
    : (B ** A) = (@identity_matrix F n)
    -> (@matrix_right_inverse F n n A).
  Proof.
    intros ?.
    destruct (natchoice0 n) as [eq0 | gt].
    { unfold matrix_inverse. use tpair. {assumption. }
      simpl; apply funextfun; intros i; apply fromstn0; now rewrite eq0. }
    pose (C := gauss_clear_all_rows_as_left_matrix F A gt).
    pose (C' := gauss_clear_all_rows_as_matrix_eq F C).
    pose (CA := C ** A).
    pose (D := @upper_triangular_right_inverse_construction _ CA).
    exists (D ** C).
    assert (CA_ut : is_upper_triangular CA).
    { pose (CA_ut
      := @row_echelon_to_upper_triangular _ _ _ CA).
      unfold is_upper_triangular in CA_ut |- *.
      intros.
      apply CA_ut; try assumption.
      unfold is_row_echelon_partial.
      pose (re_1 := @gauss_clear_all_rows_inv1 _ _ _ A gt).
      pose (re_2 := @gauss_clear_all_rows_inv2 _ _ _ A gt).
      rewrite <- (gauss_clear_all_rows_as_matrix_eq F _ gt) in re_1, re_2.
      apply (@is_row_echelon_from_partial _ _ _ CA).
      exists re_1; apply re_2.
    }
    assert (re_1 : @diagonal_all_nonzero F _ CA).
    { apply left_invertible_upper_triangular_to_diagonal_all_nonzero;
      try assumption.
      pose (re_2 := @gauss_clear_all_rows_matrix_invertible
        F _ _ A gt).
      destruct re_2 as [M [linv rinv]].
      apply left_inv_matrix_prod_is_left_inv.
      - now exists M.
      - now exists B.
    }
    pose (invmat := @right_inverse_construction_inv _ _ CA_ut re_1).
    unfold CA in invmat.
    rewrite matrix_mult_assoc in invmat.
    pose (CM := @gauss_clear_all_rows_matrix_invertible
      _ _ _ A gt).
    assert (eq : (C ** A ** D) = (A ** D ** C)).
    { unfold CA in invmat. unfold D, CA.
      rewrite matrix_mult_assoc. rewrite invmat.
      pose (left_inv_eq_right := @matrix_left_inverse_equals_right_inverse).
      apply pathsinv0.
      pose (gauss_mat_invertible
        := @gauss_clear_all_rows_matrix_invertible _ _ _ A gt).
      apply (matrix_inverse_to_right_and_left_inverse) in gauss_mat_invertible.
      destruct gauss_mat_invertible as [gauss_mat gauss_mat_invertible].
      pose (left_inv_eq_right_app
        := @left_inv_eq_right F n _ n
        (gauss_clear_all_rows_as_left_matrix _ A gt)
        (gauss_mat) ((A ** D),, invmat)).
      replace (@matrix_mult F _ _ A _
        (upper_triangular_right_inverse_construction
        (@matrix_mult F _ _ C _ A)))
      with (pr1 gauss_mat); simpl.
      2: { now rewrite left_inv_eq_right_app. }
      now apply gauss_mat.
    }
    rewrite (@matrix_mult_assoc F _ _ A) in eq.
    rewrite <- matrix_mult_assoc in invmat.
    unfold D, CA in eq.
    rewrite invmat in eq.
    apply pathsinv0, eq.
  Defined.

  Lemma right_inverse_implies_left
    { n : nat } (A B: Matrix F n n)
    : @matrix_right_inverse F _ _ A -> (@matrix_left_inverse F _ _ A).
  Proof.
    intros [rinv isrinv].
    pose (linv := @make_matrix_left_inverse F _ _ n A rinv isrinv).
    pose (linv_to_rinv := @left_inverse_implies_right _ _ _ isrinv).
    exists rinv.
    pose (inv_eq :=
      @matrix_left_inverse_equals_right_inverse _ n _ n _ linv linv_to_rinv).
    simpl in inv_eq; rewrite inv_eq;
    apply linv_to_rinv.
  Defined.

  Theorem matrix_inverse_or_non_invertible { n : nat }
    (A : Matrix F n n)
    : @matrix_inverse_or_non_invertible_stmt _ _ A.
  Proof.
    unfold matrix_inverse_or_non_invertible_stmt.
    destruct (natchoice0 n) as [eq0 | gt].
    { left; destruct eq0; apply (@nil_matrix_invertible F 0 A). }
    set (B:= @gauss_clear_all_rows_as_left_matrix _ _ _ A gt).
    set (BA := B ** A).
    set (C := upper_triangular_right_inverse_construction BA).
    assert (ut : is_upper_triangular BA).
    { unfold BA.
      pose (is_echelon := @gauss_clear_all_rows_inv3 F _ _ A gt).
      rewrite <- (gauss_clear_all_rows_as_matrix_eq _ _ gt) in is_echelon.
      now apply row_echelon_to_upper_triangular. }
    destruct (vector_all_nonzero_compute (λ i : stn n, BA i i))
    as [nz | [idx isnotz]].
    2 : { right.
          intros [invM [isl isr]].
          pose (isinv := @make_matrix_left_inverse _ _ _ n _ _ isr).
          assert (isinvprod : (matrix_left_inverse BA)).
          { apply left_inv_matrix_prod_is_left_inv; try assumption.
            apply (@matrix_inverse_to_right_and_left_inverse F _ B),
              gauss_clear_all_rows_matrix_invertible. }
          pose (contr_eq
            := @left_invertible_upper_triangular_to_diagonal_all_nonzero
            _ _ ut isinvprod idx).
          now rewrite isnotz in contr_eq.
    }
    left.
    set (BAC_id := @right_inverse_construction_inv _ _ ut nz).
    assert (rinv_eq : (C ** BA) = identity_matrix).
    { pose (linv := @right_inverse_implies_left _ _ C (C,, BAC_id)).
      pose (eq := @matrix_left_inverse_equals_right_inverse
        _ n _ n _ linv (_,, BAC_id)).
      change (pr1 (C,, _)) with C in eq.
      apply linv. }
    exists (C ** B); simpl; use tpair.
    2: { simpl; rewrite matrix_mult_assoc; apply rinv_eq. }
    rewrite <- matrix_mult_assoc.
    unfold BA in BAC_id.
    assert (linv_eq : ((B ** A ** C) = (A ** C ** B))).
    { rewrite matrix_mult_assoc in BAC_id |- *.
      unfold C in *; clear C;
        set (C := (upper_triangular_right_inverse_construction BA)).
      pose (B_rinv := @make_matrix_right_inverse F _ _ n B (A ** C) BAC_id).
      pose (linv := @right_inverse_implies_left _ _ C B_rinv).
      pose (eq := @matrix_left_inverse_equals_right_inverse
        F n _ n B linv ((A ** C),, BAC_id)).
      replace (A ** C) with (pr1 B_rinv); try reflexivity.
      rewrite (pr2 B_rinv).
      replace (pr1 B_rinv) with (pr1 linv); try assumption.
      2: {now rewrite eq. }
      now rewrite (pr2 linv).
    }
    simpl in * |- ;
    now rewrite <- BAC_id, <- linv_eq.
  Defined.

End Inverse.
