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
Require Import UniMath.Algebra.Elimination.Elimination.
Require Import UniMath.Algebra.Elimination.EliminationAlts.

(** 
  In this module, we define a back-substitution procedure that works on
  nxn matrices that are upper triangular with all non-zero diagonal.

  We use this procedure to show that any nxn matrix either not invertible,
  or calculate its inverse.
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
  := ∑ f : (Matrix F n n -> Vector F n -> Vector F n),
    (@matrix_mult F _ _ mat _ (col_vec (f mat vec))) = (col_vec vec).

Section BackSub.

  Context (F : fld).

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* output: a solution [x] to [mat ** x = vec] (if one exists?) *)
  (* TODO: what conditions on [mat] are needed to ensure this is a solution? *)
  Definition back_sub_step { n : nat } ( iter : (⟦ n ⟧)%stn )
    (mat : Matrix F n n) (b : Vector F n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    destruct (nat_eq_or_neq iter i) as [? | ?].
    2 : {exact (b i). }
    destruct (natlehchoice (S iter) n) as [? | ?]. {apply iter. }
    - exact (((vec i) * fldmultinv' (mat i i))
           - ((Σ (mat i ^ b)  - (b  i)* (mat i i))
           * (fldmultinv' (mat i i))))%ring.
    - exact ((fldmultinv' (mat i i)) * (vec i))%ring.
  Defined.

  (* TODO moderately large cleanup needed - rename temp variables *)
  Lemma back_sub_step_inv0 { n : nat } (iter : ⟦ n ⟧%stn) (mat : Matrix F n n)
        (x : Vector F n) (b : Vector F n)
        (p: @is_upper_triangular F n n mat)
        (p' : @diagonal_all_nonzero F n mat):
    ((mat ** (col_vec (back_sub_step iter mat x b))) iter = (col_vec b) iter).
  Proof.
    intros.
    unfold back_sub_step, col_vec.
    unfold fldmultinv'.
    rewrite matrix_mult_eq; unfold matrix_mult_unf, pointwise.
    set (m := n - (S iter)).
    assert (split_eq : n = (S iter) + m).
    { unfold m.
      rewrite natpluscomm.
      rewrite minusplusnmm.
      - apply idpath.
      - simpl. exact (pr2 iter).
    }
    generalize iter mat b p' p x.
    clear x p p' b mat.
    destruct (stn_inhabited_implies_succ iter) as [s_iter s_iter_eq].
    rewrite s_iter_eq in *.
    intros iter' mat' vec' filled' is_upper_t' b'.
    apply funextfun; intros ?.
    rewrite (@rigsum_dni F (s_iter) _ iter').
    rewrite nat_eq_or_neq_refl.
    destruct (fldchoice0 _) as [contr0 | neq].
    { contradiction (filled' iter'). }
    destruct (natlehchoice (S (pr1 iter')) (S s_iter)) as [lt | eq].
    - etrans.
      { apply maponpaths_2; apply maponpaths.
        apply funextfun. intros q.
        unfold funcomp.
        rewrite (nat_eq_or_neq_right (dni_neq_i iter' q)).
        reflexivity.
      }
      rewrite (@rigsum_dni F (s_iter)  _ iter').
      set (f := λ q : (⟦ s_iter ⟧%stn), _).
      set (a := mat' iter' iter').
      set (b'' := b' iter').
      etrans.
      { apply maponpaths.
        etrans.
        { apply maponpaths.
          rewrite (@ringcomm2 F).
          apply maponpaths.
          rewrite (@ringcomm2 F).
          reflexivity.
        }
        apply (@ringminusdistr F a).
      }
      etrans.
      { apply maponpaths; apply map_on_two_paths.
        rewrite <- (@rigassoc2 F).
        rewrite (@fldmultinvrax F).
        { rewrite (@riglunax2 F); reflexivity. }
        apply maponpaths.
        rewrite <- (@rigassoc2 F), (@fldmultinvrax F).
        apply (@riglunax2 F).
      }
      etrans.
      { do 3 apply maponpaths.
        rewrite (@rigcomm2 F), (@fldplusminus F).
        reflexivity.
      }
      rewrite (@rigcomm1 F); rewrite (@rigassoc1 F).
      unfold f, funcomp.
      rewrite (@ringlinvax1 F), (@rigrunax1 F).
      apply idpath.
    - rewrite (@zero_function_sums_to_zero F).
      + rewrite (@riglunax1 F), <- (@rigassoc2 F).
        rewrite (@fldmultinvrax F), (@riglunax2 F).
        reflexivity.
      + simpl.
        apply funextfun; intros q.
        etrans.
        { apply maponpaths_2.
          rewrite is_upper_t'. {reflexivity. }
          unfold dni, di; simpl.
          destruct (natlthorgeh q iter') as [lt | geh].
          { apply lt. }
          apply invmaponpathsS in eq.
          apply fromempty.
          assert (q_ge_iter': q ≥ (pr1 iter')).
          { apply geh. }
          rewrite eq in q_ge_iter'.
          apply natgehtonegnatlth in q_ge_iter'.
          assert (q_le_iter_absurd : q < s_iter).
          { apply (pr2 q). }
          exact (q_ge_iter' q_le_iter_absurd).
        }
        rewrite (@rigmult0x F).
        reflexivity.
  Defined.

  Lemma back_sub_step_inv1
    { n : nat }
    (iter : ⟦ n ⟧%stn )
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (p: @is_upper_triangular F n n mat)
    (p' : @diagonal_all_nonzero F n mat)
    : ∏ i : ⟦ n ⟧%stn, i ≠ iter ->
      (col_vec (back_sub_step iter mat b vec) i  = ( (col_vec b)) i).
  Proof.
    intros i ne.
    unfold back_sub_step, col_vec.
    apply funextfun. intros j.
    simpl.
    destruct (nat_eq_or_neq iter i) as [eq | ?];
      try apply idpath.
    rewrite eq in ne.
    apply isirrefl_natneq in ne.
    contradiction.
  Defined.

  Lemma back_sub_step_inv2 
    { n : nat }
    (iter : ⟦ n ⟧%stn)
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (is_ut: @is_upper_triangular F n n mat)
    (nz : @diagonal_all_nonzero F n mat)
    : ∏ i : ⟦ n ⟧%stn, i ≥ iter ->
       (mat ** (col_vec b )) i = (col_vec vec) i
    -> (mat ** (col_vec (back_sub_step iter mat b vec))) i = ((col_vec vec) i).
  Proof.
    unfold transpose, flip.
    intros i le H.
    destruct iter as [iter p''].
    rewrite <- H.
    destruct (natlehchoice iter i) as [lt | eq]. {apply le. }
    - rewrite matrix_mult_eq in *.
      apply pathsinv0.
      rewrite matrix_mult_eq in *.
      unfold matrix_mult_unf in *.
      apply funextfun; intros ?.
      apply maponpaths, funextfun; intros i'.
      destruct (stn_eq_or_neq i' (iter,, p'')) as [eq | neq].
      2 : { rewrite back_sub_step_inv1; try assumption; reflexivity. }
      replace (mat i i') with (@ringunel1 F).
      2 : { rewrite is_ut; try reflexivity. rewrite eq; assumption. }
      do 2 rewrite (@rigmult0x F); reflexivity.
    - revert le. revert p''. rewrite eq.
      intros.
      replace (stntonat _ i,, p'') with i.
      { rewrite back_sub_step_inv0; try reflexivity; try assumption.
        apply pathsinv0. apply H. }
      unfold stntonat in *.
      change i with (pr1 i,, pr2 i); simpl.
      assert (eq' : (pr2 i) = p'').
      { apply proofirrelevance. apply propproperty. }
      rewrite eq'; reflexivity.
  Defined.

  Lemma back_sub_step_inv3
    { n : nat }
    ( iter : ⟦ n ⟧%stn )
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (is_ut : @is_upper_triangular F n n mat)
    (nz : @diagonal_all_nonzero F n mat):
    ∏ i : ⟦ n ⟧%stn, i > iter ->
      (mat ** (col_vec b )) i = (mat ** (col_vec (back_sub_step iter mat b vec))) i.
  Proof.
    intros i lt.
    unfold transpose, flip in *.
    destruct iter as [iter p''].
    destruct (natlehchoice iter i) as [it_i_lt | eq]. {apply natlthtoleh in lt. apply lt. }
    2: { rewrite <- eq in lt.
         apply isirreflnatgth in lt. contradiction. }
    rewrite matrix_mult_eq.
    apply pathsinv0.
    rewrite matrix_mult_eq.
    unfold matrix_mult_unf.
    apply funextfun; intros ?.
    apply maponpaths, funextfun; intros i'.
    destruct (stn_eq_or_neq i' (iter,, p'')) as [eq | neq].
    2: { rewrite back_sub_step_inv1; try assumption; reflexivity. }
    replace (mat i i') with (@ringunel1 F).
    { do 2 rewrite (@rigmult0x F); reflexivity. }
    rewrite is_ut; try reflexivity.
    unfold stntonat in lt.
    rewrite eq.
    apply it_i_lt.
  Defined.

  (* TODO fix signature - align b, vec with x, b as in other lemmata*)
  Definition back_sub_internal
    { n : nat }
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (iter : ⟦ S n ⟧%stn)
    : Vector F n.
  Proof.
    destruct iter as [iter p].
    induction iter as [ | m IHn] .
    - exact b.
    - refine (back_sub_step (dualelement (m,, p)) mat (IHn _) vec).
      apply (istransnatlth _ _ _ (natgthsnn m) p).
  Defined.

  Definition back_sub
    {n : nat}
    (mat : Matrix F n n)
    (vec : Vector F n)
    := back_sub_internal mat vec vec (n,, natgthsnn n).

  Lemma back_sub_internal_inv0
    { n : nat }
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (df : @diagonal_all_nonzero F n mat)
    (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < (dualelement iter)
    -> (((col_vec (back_sub_internal mat b vec iter)))) i = ((col_vec b) i).
  Proof.
    destruct iter as [iter p].
    induction iter.
    { intros i H.
      destruct (natchoice0 (S n)) as [contr_eq | gt] in H.
      { clear H. apply negpaths0sx in contr_eq. contradiction. }
      reflexivity. }
    unfold back_sub_internal.
    intros i i_lt_dual.
    rewrite nat_rect_step.
    assert (p': iter < S n). { apply (istransnatlth _ _ _ (natgthsnn iter) p).  }
    assert (lt : i < dualelement (iter,, p')).
    { unfold dualelement in *.
      destruct (natchoice0 (S n)) as [contr_eq | gt] in *.
      { pose (contr := (natneq0sx n)).
       rewrite contr_eq in contr.
       apply isirrefl_natneq in contr. contradiction. }
      simpl in *.
      refine (istransnatgth _ _ _ _ _).
      { set (n' := n - 0 - iter).
        apply natminus1lthn.
        rewrite minus0r.
        apply minusgth0.
        exact p. }
      replace (n - 0 - iter - 1) with (n - 0 - (S iter)); try apply i_lt_dual.
      rewrite minus0r, natminusminus.
      replace (S iter) with (iter + 1); try reflexivity.
      rewrite <- plus_n_Sm, natplusr0.
      reflexivity.
    }
    rewrite <- (IHiter p'); try assumption.
    rewrite back_sub_step_inv1; try reflexivity; try assumption.
    2 : { unfold dualelement in *.
          apply natlthtoneq.
          destruct (natchoice0 n) as [contr_eq | gt].
          { apply fromstn0. clear i_lt_dual. clear lt. rewrite <- contr_eq in i.
            assumption. }
          destruct (natchoice0 (S n)) as [contr_eq | sn_gt] in *.
          { simpl. pose (contr := natneqsx0 n). rewrite contr_eq in contr.
            apply isirrefl_natneq in contr. contradiction. }
          simpl in *.
          rewrite minus0r in i_lt_dual.
          replace (S iter) with (iter + 1) in i_lt_dual.
          2 : { rewrite <- plus_n_Sm, natplusr0. reflexivity. }
                rewrite natpluscomm, <- natminusminusassoc in i_lt_dual; assumption.
    }
    unfold back_sub_internal.
    apply maponpaths_2, maponpaths, proofirrelevance, propproperty.
  Defined.

  Lemma back_sub_internal_inv2
    { n : nat }
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (df : @diagonal_all_nonzero F n mat) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i ≥ (dualelement iter)
    -> (mat ** (col_vec (back_sub_internal mat b vec iter))) i = (col_vec vec) i.
  Proof.
    unfold transpose, flip.
    intros i i_le_iter.
    unfold back_sub_internal.
    destruct iter as [iter p].
    induction iter as [| iter IH].
    { apply fromempty.
      unfold dualelement in i_le_iter.
      destruct (natchoice0 (S n)) as [contreq0 | ?] in i_le_iter.
      {apply fromempty. clear i_le_iter. apply negpaths0sx in contreq0; contradiction. }
      unfold make_stn in i_le_iter.
      rewrite coprod_rect_compute_2 in i_le_iter.
      simpl in i_le_iter.
      do 2 rewrite minus0r in i_le_iter.
      pose (contr := pr2 i); simpl in contr.
      change (stntonat _ i) with (pr1 i) in i_le_iter.
      apply natgthtonegnatleh in contr.
      contradiction.
    }
    rewrite nat_rect_step.
    destruct (natlehchoice (dualelement (iter,, p)) (i)) as [leh | eq].
      { unfold dualelement in *.
        destruct (natchoice0 n) as [contr_eq | ?]. {apply fromstn0. rewrite contr_eq. assumption. }
        destruct (natchoice0 (S n)) as [contr_eq | ?] in *.
        { pose (contr := (natneq0sx n)). rewrite <- contr_eq in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2 in *.
        simpl in *.
        assert (eq' : ∏ n : nat, S n = (n + 1)%nat).
        { intros. rewrite <- plus_n_Sm, natplusr0. apply idpath.  }
        rewrite eq', minus0r, natpluscomm, <- natminusminus in i_le_iter.
        rewrite i_le_iter; reflexivity.
      }
    - rewrite back_sub_step_inv2; try reflexivity; try assumption.
      { unfold dualelement. unfold dualelement in leh.
        destruct (natchoice0 n) as [contr_eq | ?]. {apply fromstn0. rewrite contr_eq. assumption. }
        rewrite coprod_rect_compute_2 in *.
        apply natgthtogeh; assumption.
      }
      rewrite IH; try reflexivity.
      { unfold dualelement.
        destruct (natchoice0 (S n)) as [contr_eq | gt] in *.
        { pose (contr := (natneq0sx n)). rewrite <- contr_eq in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2.
        unfold dualelement in leh.
        destruct (natchoice0 n) as [eq | gt']. {apply fromstn0. rewrite eq. assumption. }
        rewrite coprod_rect_compute_2 in *.
        simpl; simpl in leh.
        rewrite minus0r.
        apply natgthtogehsn in leh.
        rewrite pathssminus in leh.
        2: { rewrite pathssminus.
             - rewrite minussn1; exact p.
             - simpl; apply gt'. }
        assert (e : n = S (n - 1)).
        { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
          apply pathsinv0. apply minusplusnmm. assumption. }
        rewrite <- e in leh.
        apply leh.
      }
    - replace (dualelement (iter,, p)) with i.
      { rewrite back_sub_step_inv0; try reflexivity; try assumption. }
      destruct (natchoice0 n) as [eq0 | gt]. {apply fromstn0. rewrite eq0. assumption. }
      unfold stntonat in eq.
      pose (subtype_eq := @subtypePath_prop _ _ _ _ eq).
      rewrite <- (@subtypePath_prop _ _ _ _ eq).
      reflexivity.
  Defined.

  Lemma back_sub_inv0
    { n : nat }
    (mat : Matrix F n n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (df : @diagonal_all_nonzero F _ mat)
    : back_sub_stmt mat vec ut df.
  Proof.
    unfold back_sub_stmt.
    use tpair. {exact back_sub. }
    intros; unfold back_sub.
    destruct (natchoice0 n) as [p | ?].
    { apply funextfun. intros i. apply fromstn0. rewrite p. simpl. assumption. }
    apply funextfun; intros i.
    apply back_sub_internal_inv2; try assumption; unfold dualelement.
    destruct (natchoice0 (S n)). { apply fromempty. apply negpaths0sx in p. assumption. }
    simpl; rewrite minus0r, minusnn0; reflexivity.
  Defined.

End BackSub.

Section Inverse.

  Context (F : fld).

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* Construct the inverse, if additionally mat is upper triangular with non-zero diagonal *)
  Definition upper_triangular_right_inverse_construction
    { n : nat }
    (mat : Matrix F n n)
    := transpose (λ i : (stn n), (back_sub F (mat) ((@identity_matrix F n) i))).

  (* actually only needs right invertibility ? *)
  Lemma invertible_upper_triangular_to_diagonal_all_nonzero
    {n : nat }
    (A : Matrix F n n)
    (p : @is_upper_triangular F n n A)
    (p': @matrix_inverse F n A)
    : (@diagonal_all_nonzero F n A).
  Proof.
    apply diagonal_nonzero_iff_transpose_nonzero.
    set (At := (λ y x : (⟦ n ⟧)%stn, A x y)).
    assert (@is_lower_triangular F n n At).
    { apply upper_triangular_transpose_is_lower_triangular. assumption. }
    unfold diagonal_all_nonzero.
    intros i.
    destruct (fldchoice0 (At i i)) as [contr | ne].
    2: { assumption. }
    apply fromempty.
    destruct (natchoice0 n) as [contr' | gt]. {apply fromstn0. rewrite contr'; exact i. }
    set (M :=  @clear_columns_up_to_no_switch_as_left_matrix F n (n,, natgthsnn n) A).
    assert (invertible : matrix_inverse (M ** A)).
    { apply inv_matrix_prod_is_inv; try assumption.
      apply clear_columns_up_to_matrix_no_switch_invertible.
    }
    pose (inv := @gauss_clear_columns_up_to_no_switch_inv5 F).
    pose (contr' := inv n At (n,, natgthsnn n) X i contr (pr2 i)).
    destruct contr' as [idx contr'].
    set ( At' := gauss_clear_columns_up_to_no_switch (n,, natgthsnn n) At).
    pose (noninv := @zero_row_to_non_invertibility F n At' idx contr').
    apply noninv.
    unfold At'.
    rewrite <- gauss_clear_columns_up_to_no_switch_as_matrix_eq.
    apply inv_matrix_prod_is_inv.
    2: {apply transpose_invertible_to_invertible; try assumption. }
    apply clear_columns_up_to_matrix_no_switch_invertible.
  Defined.

  Definition upper_triangular_right_inverse_is_inverse
    { n : nat } (mat : Matrix F n n)
    (ut : @is_upper_triangular F _ _ mat)
    (df: @diagonal_all_nonzero F n mat)
    : (mat ** ((upper_triangular_right_inverse_construction mat)))
      = (@identity_matrix F n).
  Proof.
    apply funextfun; intros i.
    unfold matrix_mult, row.
    unfold col, transpose, flip.
    apply funextfun; intros ?.
    unfold upper_triangular_right_inverse_construction.
    rewrite (@col_vec_mult_eq F n n mat
      (λ y : (⟦ n ⟧)%stn, upper_triangular_right_inverse_construction mat y x)
        (@identity_matrix F n x)).
    - destruct (stn_eq_or_neq i x) as [eq | neq].
      {rewrite eq; reflexivity. }
      rewrite id_mat_ij; try rewrite id_mat_ij; try reflexivity; try assumption.
      apply (issymm_natneq _ _ neq).
    - unfold upper_triangular_right_inverse_construction.
      pose (H2 := @back_sub_inv0).
      destruct (natchoice0 n) as [eq | ?].
      {apply fromstn0. rewrite eq. assumption. }
      apply (H2 _ _ _ _ ut df).
  Defined.

  Local Lemma row_vec_col_vec_mult_eq
  { n : nat }
  (A : Matrix F n n)
  : forall x, transpose ((row_vec x) ** (transpose A)) = (A ** (col_vec x)).
  Proof.
    intros.
    unfold transpose, flip, row_vec, col_vec, row, col.
    intros.
    do 2 (rewrite matrix_mult_eq; unfold matrix_mult_unf).
    assert (eq: forall x0 : (stn n), iterop_fun 0%ring op1
        (λ k : (⟦ n ⟧)%stn, (x k * A x0 k)%ring)
      = iterop_fun 0%ring op1 (λ k : (⟦ n ⟧)%stn, (A x0 k * x k )%ring)).
    { intros x0.
      assert (sum_pointwise_eq : forall (f g : (stn n) -> F),
      (forall i : (stn n), f i = g i) ->
        iterop_fun 0%ring op1 f =  iterop_fun 0%ring op1 g).
      { intros f g H. apply maponpaths. apply funextfun. intros j. apply H. }
      apply sum_pointwise_eq.
      intros; apply (@ringcomm2 F).
    }
    assert (f_eq : forall f g: (stn n) -> (stn 1) -> F,
      (forall i : (stn n), forall j : (stn 1), f i j = g i j) -> f = g).
    { intros f g. intros H. apply funextfun; intros i.
      apply funextfun; intros j. apply H. }
    apply f_eq; intros i j; apply eq.
  Defined.

  (* (BA)C = I -> D, s.t. BD = I*)
  Local Lemma matrix_product_right_inverse_to_left_term_right_inverse
    {R : rig} {n : nat} 
    (A : Matrix R n n) (B : Matrix R n n)
    (inv : (matrix_right_inverse (matrix_mult A B))) : matrix_right_inverse A.
  Proof.
    use tpair. { exact (matrix_mult B (pr1 inv)). }
    simpl; rewrite <- matrix_mult_assoc; apply inv.
  Defined.

  (* C(BA) -> D s.t. DA = I*)
  Local Lemma matrix_product_left_inverse_to_right_term_left_inverse
    {R : rig} {n : nat}
    (A : Matrix R n n) (B : Matrix R n n)
    (inv : (matrix_left_inverse (matrix_mult A B))) : matrix_left_inverse B.
  Proof.
    use tpair. { exact (matrix_mult (pr1 inv) A). }
    simpl; rewrite matrix_mult_assoc; apply inv.
  Defined.

  Local Lemma left_inverse_implies_right_internal
    {n : nat}
    (A B: Matrix F n n)
    (ut : @is_upper_triangular F _ _ A) (df: @diagonal_all_nonzero F n A)
    : (B ** A) = (@identity_matrix F n) -> (@matrix_inverse F n A).
  Proof.
    intros H0.
    assert (eq0: forall y, ((A ** (col_vec (back_sub F A y))) = (col_vec y))).
    { intros. apply (back_sub_inv0 _ _ _ ut df); assumption. }
    assert (eq1 : forall y,
      (B ** (A ** (col_vec (back_sub F A y)))) = (B ** (col_vec y))).
    { intros y. pose (H := eq0 y).
      rewrite H. reflexivity.  }
    assert (eq2 : forall y, (col_vec (back_sub F A y) = (B ** (col_vec y)))).
    { intros y.
      pose (H := eq1 y).
      rewrite <- matrix_mult_assoc, H0, matlunax2 in H.
      assumption. }
    assert (eq3 :forall y,
      ((A ** (col_vec (back_sub F A y))) = (A ** (B ** (col_vec y))))).
    { intros y.
      rewrite <- (eq2 y); reflexivity.
    }
    assert (eq4 : forall y, col_vec y = (A ** (B ** (col_vec y)))).
    { intros y.
      pose (H := eq3 y).
      pose (H1 := eq0 y).
      unfold col_vec in *.
      rewrite <- H1.
      apply maponpaths.
      rewrite <- matrix_mult_assoc, H0, matlunax2.
      apply idpath.
    }
    assert (eq5: (A ** B) = identity_matrix).
    { apply identity_matrix_unique_left.
      intros n' A'.
      apply funextfun; intros i.
      apply funextfun; intros j.
      pose (H := (eq4 (col A' j))).
      rewrite <- matrix_mult_assoc in H.
      symmetry in H.
      pose (eq5 := @col_vec_mult_eq F n n _ _ _ H).
      unfold col, transpose, flip in eq5.
      rewrite <- eq5.
      apply idpath. }
    use tpair. { exact B. }
    use tpair; try assumption.
  Defined.

  Lemma make_matrix_left_inverse
    {R : rig}
    {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix) : matrix_left_inverse B.
  Proof.
    unfold matrix_left_inverse.
    use tpair. {exact A. }
    exact eq.
  Defined.

  Lemma make_matrix_right_inverse
    {R : rig} {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix) : matrix_right_inverse A.
  Proof.
    unfold matrix_left_inverse.
    use tpair. {exact B. }
    exact eq.
  Defined.

  Lemma left_inverse_implies_right { n : nat } (A B: Matrix F n n)
    : (B ** A) = (@identity_matrix F n) -> (@matrix_right_inverse F n n A).
  Proof.
    intros H0.
    destruct (natchoice0 n) as [eq0 | gt].
    { unfold matrix_inverse. use tpair. {assumption. }
      simpl. apply funextfun; intros i; apply fromstn0; rewrite eq0; assumption. }
    pose (C := (clear_rows_up_to_as_left_matrix_internal F A (n,, natgthsnn n)) gt).
    pose (C' := gauss_clear_rows_up_to_as_matrix_eq F (n,, natgthsnn n) C).
    pose (CA := C ** A).
    pose (D := @upper_triangular_right_inverse_construction n CA).
    use tpair. {exact (D ** C). }
    assert (H1 : is_upper_triangular CA).
    { pose (H1 := @row_echelon_partial_to_upper_triangular_partial F n n CA gt (n,, natgthsnn n)).
      unfold is_upper_triangular.
      unfold is_upper_triangular_partial in H1.
      intros.
      apply H1; try assumption.
      2: {exact (pr2 i). }
      unfold is_row_echelon_partial.
      pose (H2 := @gauss_clear_rows_up_to_inv1 F n n A gt (n,, natgthsnn n)).
      pose (H3 := @gauss_clear_rows_up_to_inv2 F n n A gt (n,, natgthsnn n)).
      use tpair.
      - rewrite <- (gauss_clear_rows_up_to_as_matrix_eq F _ _ gt) in H2.
        apply H2.
      - rewrite <- (gauss_clear_rows_up_to_as_matrix_eq F _ _ gt) in H3.
        apply H3.
    }
    assert (H2 : @diagonal_all_nonzero F _ CA).
    { unfold diagonal_all_nonzero.
      intros i neq.
      apply (gauss_clear_columns_up_to_no_switch_inv7 n CA (n,, natgthsnn n) H1 i); try assumption.
      {exact (pr2 i). }
      apply left_inv_matrix_prod_is_left_inv.
      { apply matrix_inverse_to_right_and_left_inverse.
        apply gauss_clear_rows_up_to_matrix_invertible.
      }
      use tpair. {exact B. }
      simpl; assumption.
    }
    pose (H4 := @upper_triangular_right_inverse_is_inverse _ _ H1 H2).
    unfold CA in H4.
    rewrite matrix_mult_assoc in H4.
    pose (H5 := @matrix_product_left_inverse_to_right_term_left_inverse).
    pose (H6 := @matrix_product_right_inverse_to_left_term_right_inverse).
    pose (CM := @gauss_clear_rows_up_to_matrix_invertible F _ _ (n,, natgthsnn n) A gt).
    pose (H7 := left_inverse_implies_right_internal _ (B ** (pr1 CM) ) H1 H2).
    assert (eq : (C ** A ** D) = (A ** D ** C)).
    { unfold CA in H4. unfold D, CA.
      rewrite matrix_mult_assoc. rewrite H4.
      pose (H8 := @matrix_left_inverse_equals_right_inverse).
      apply pathsinv0.
      unfold matrix_left_inverse in H7.
      pose (H9 := @gauss_clear_rows_up_to_matrix_invertible F n n (n,, natgthsnn n) A gt).
      apply (matrix_inverse_to_right_and_left_inverse) in H9.
      destruct H9 as [H9 H10].
      unfold clear_rows_up_to_as_left_matrix in *.
      pose (H11 := @H8 F n _ n ((clear_rows_up_to_as_left_matrix_internal F A (n,, natgthsnn n) gt)) (H9) ((A ** D),, H4)).
      simpl in H11.
      unfold D, CA in H11.
      replace (@matrix_mult F _ _ A _
        (upper_triangular_right_inverse_construction (@matrix_mult F _ _ C _ A)))
          with (pr1 H9).
      2: { rewrite H11. reflexivity. }
      simpl.
      pose (H12 := @matrix_left_inverse_equals_right_inverse _ n _ n _ H9 H10).
      unfold matrix_left_inverse in H9.
      destruct H9 as [H9 H9'].
      simpl; unfold C.
      assumption.
    }
    rewrite (@matrix_mult_assoc F n n A n D n C) in eq.
    rewrite <- matrix_mult_assoc in H4.
    unfold D, CA in eq.
    rewrite H4 in eq.
    apply pathsinv0 in eq.
    apply eq.
  Defined.

  Lemma right_inverse_implies_left
    { n : nat }
    (A B: Matrix F n n)
    : @matrix_right_inverse F n n A
      -> (@matrix_left_inverse F n n A).
  Proof.
    intros A_right_inv.
    destruct A_right_inv as [rinv isrinv].
    pose (linv := @make_matrix_left_inverse F _ _ n A rinv isrinv).
    pose (linv_to_rinv := @left_inverse_implies_right n _ _ isrinv).
    use tpair. {exact rinv. }
    pose (inv_eq := @matrix_left_inverse_equals_right_inverse _ n _ n _ linv linv_to_rinv).
    simpl in inv_eq.
    rewrite inv_eq.
    apply linv_to_rinv.
  Defined.

  Lemma matrix_inverse_or_non_invertible { n : nat }
    (A : Matrix F n n)
    : @matrix_inverse_or_non_invertible_stmt _ _ A.
  Proof.
    unfold matrix_inverse_or_non_invertible_stmt.
    destruct (natchoice0 n) as [? | gt].
    { left. apply nil_matrix_is_inv; symmetry; assumption. }
    set (B:= @clear_rows_up_to_as_left_matrix F n n A (n,, natgthsnn n) gt).
    set (BA := B ** A).
    set (C := upper_triangular_right_inverse_construction (BA)).
    assert (ut : is_upper_triangular (BA)).
    { unfold BA.
      pose ( is_echelon := @gauss_clear_rows_up_to_inv3 F _ _ A gt (n,, natgthsnn n)).
      rewrite <- (gauss_clear_rows_up_to_as_matrix_eq F _ _ gt) in is_echelon.
      apply row_echelon_to_upper_triangular; try assumption.
    }
    destruct (diagonal_all_nonzero_compute F (λ i : (stn n), BA i i)) as [nz | hasz].
    2: { right.
      intros H.
      destruct H as [invM isinv].
      destruct isinv as [isl isr].
      pose (H1 := @gauss_clear_columns_up_to_no_switch_inv7).
      apply (gauss_clear_columns_up_to_no_switch_inv7 _ BA (n,, natgthsnn n) ut (pr1 hasz)); simpl; try assumption.
      - apply (pr2 hasz).
      - exact (pr2 (pr1 hasz)).
      - apply left_inv_matrix_prod_is_left_inv; try assumption.
        + apply matrix_inverse_to_right_and_left_inverse.
          unfold B. apply gauss_clear_rows_up_to_matrix_invertible.
        + use tpair. {exact invM. }
        simpl; try assumption.
    }
    left.
    set (BAC := BA ** C).
    set (BAC_id := @upper_triangular_right_inverse_is_inverse _ _ ut nz).
    assert (rinv_eq : (C ** BA) = identity_matrix).
    { pose (linv := @right_inverse_implies_left _ BA C (C,, BAC_id)).
      pose (eq := @matrix_left_inverse_equals_right_inverse F n _ n BA linv (C,, BAC_id)).
      change ( pr1 (C,, BAC_id)) with C in eq.
      apply linv.
    }
    use tpair. {exact (C ** B). }
    simpl; use tpair.
    2: { simpl. rewrite matrix_mult_assoc. apply rinv_eq. }
    rewrite <- matrix_mult_assoc.
    unfold BA in BAC_id.
    assert (linv_eq : ((B ** A ** C) = (A ** C ** B))).
    { rewrite matrix_mult_assoc.
      rewrite matrix_mult_assoc in BAC_id.
      unfold C in *; clear C; set (C := (upper_triangular_right_inverse_construction BA)).
      pose (B_rinv := @make_matrix_right_inverse F n n n B (A** C) (BAC_id)).
      pose (linv := @right_inverse_implies_left _ B C B_rinv).
      pose (eq := @matrix_left_inverse_equals_right_inverse F n _ n B linv ((A** C),, BAC_id)).
      replace  (A ** C) with (pr1 B_rinv).
      2: {simpl. reflexivity. }
      rewrite (pr2 B_rinv).
      replace (pr1 B_rinv) with (pr1 linv); try assumption.
      2: {rewrite eq. simpl; reflexivity. }
      rewrite (pr2 linv); reflexivity.
    }
    simpl in *.
    rewrite <- BAC_id, <- linv_eq.
    unfold C, BA.
    reflexivity.
  Defined.

End Inverse.