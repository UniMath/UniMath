(** * Matrices

Elementary row operations on matrices, for elimination procedures

Author: Daniel @Skantz (September 2022)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.

Require Import UniMath.Algebra.Elimination.Matrices.

Section GaussOps.

  Context { R : rig }.
  Context { CR : commring}.
  Context { F : fld }.
  Local Notation Σ := (iterop_fun 0%rig op1).
  Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).
  Local Notation "A ** B" := (@matrix_mult _ _ _ A _ B) (at level 80).
  Local Notation "A **' B" := (@matrix_mult CR _ _ A _ B) (at level 80).
  Local Notation "A **'' B" := (@matrix_mult F _ _ A _ B) (at level 80).

Section RowOps.

  (** Defining the three row operations on F;
      Addition of a multiple of a row to another row,
      the interchange of two rows,
      multiplication of a row by a nonzero scalar.

      Two versions of each operation: directly on input matrix,
      or as left multiplication by a matrix.

      Hopefully the material can be easily re-used for
      column operations too. *)

  Definition gauss_add_row
    { m n : nat } ( mat : Matrix CR m n )
    ( r1 r2 : ⟦ m ⟧%stn ) ( s : CR )
    : ( Matrix CR m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r2).
    - exact ((mat r2 j) + (s * (mat r1 j)))%rig.
    - exact (mat i j).
  Defined.

  Definition add_row_matrix
    { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : CR)
    : Matrix CR n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (@stdb_vector CR n i)
        (@scalar_lmult_vec CR s _ ((@stdb_vector CR) n r1))).
    - exact (@stdb_vector CR n i).
  Defined.

  Definition gauss_scalar_mult_row
    { m n : nat} (mat : Matrix F m n)
    (s : F) (r : ⟦ m ⟧%stn)
    : Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%ring.
    - exact (mat i j).
  Defined.

  Definition mult_row_matrix {n : nat}
    (s : F) (r : ⟦ n ⟧%stn)
    : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r).
    - exact (const_vec s *pw @stdb_vector F _ i).
    - exact (@stdb_vector F _ i).
  Defined.

  Definition gauss_switch_row
    {m n : nat} (mat : Matrix R m n)
    (r1 r2 : ⟦ m ⟧%stn)
    : Matrix R m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (mat r2 j).
    - induction (stn_eq_or_neq i r2).
      + exact (mat r1 j).
      + exact (mat i j).
  Defined.

  Definition switch_row_matrix
    {n : nat} (r1 r2 : ⟦ n ⟧ %stn)
    : Matrix R n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r1).
    - exact (@identity_matrix R n r2).
    - induction (stn_eq_or_neq i r2).
      + exact (@identity_matrix R n r1).
      + exact (@identity_matrix R n i).
  Defined.

  Lemma gauss_add_row_inv0
    {m n : nat}
    (mat : Matrix CR m n)
    (i : ⟦ m ⟧%stn) (j: ⟦ m ⟧%stn)
    (s : CR)
    : ∏ (k : ⟦ m ⟧%stn), j ≠ k -> gauss_add_row mat i j s k = mat k.
  Proof.
    intros k j_ne_k.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j]; try reflexivity.
    rewrite k_eq_j in j_ne_k.
    apply isirrefl_natneq in j_ne_k.
    apply fromempty; assumption.
  Defined.

  Lemma gauss_add_row_inv1
    {m n : nat}
    (mat : Matrix CR m n)
    (i : ⟦ m ⟧%stn)
    (j: ⟦ m ⟧%stn)
    (s : CR)
    : ∏ (k : ⟦ m ⟧%stn),
      (mat i = (const_vec 0%ring))
      -> gauss_add_row mat i j s = mat.
  Proof.
    intros k eq0.
    apply funextfun; intros i'; apply funextfun; intros j'.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j'];
      simpl; try reflexivity.
    rewrite <- i'_eq_j', eq0.
    unfold const_vec ; simpl.
    rewrite (@rigmultx0 CR).
    apply (@rigrunax1 CR).
  Defined.

  Definition gauss_add_row_comp
    { m n : nat }
    ( mat : Matrix CR m n )
    ( r1 r2 : ⟦ m ⟧%stn )
    (s : CR)
    (c : ⟦ n ⟧%stn)
  : (gauss_add_row mat r1 r2 s) r2 c = op1 (mat r2 c) (op2 s (mat r1 c)).
  Proof.
    unfold gauss_add_row
    ; now rewrite stn_eq_or_neq_refl.
  Defined.

  Lemma gauss_switch_row_inv0
    {m n : nat} (mat : Matrix R m n)
    (r1 : ⟦ m ⟧%stn) (r2 : ⟦ m ⟧%stn)
    : ∏ (i : ⟦ m ⟧%stn), i ≠ r1 -> i ≠ r2
    -> (gauss_switch_row mat r1 r2 ) i = mat i.
  Proof.
    intros i i_ne_r1 i_ne_r2.
    unfold gauss_switch_row.
    apply funextfun. intros i'.
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1]
    ; destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    - simpl. rewrite i_eq_r2; apply idpath.
    - simpl. rewrite i_eq_r1 in i_ne_r1.
        apply isirrefl_natneq in i_ne_r1. contradiction.
    - simpl. rewrite i_eq_r2 in i_ne_r2.
        apply isirrefl_natneq in i_ne_r2. contradiction.
    - simpl. apply idpath.
  Defined.

  Lemma gauss_switch_row_inv1
    {m n : nat} (mat : Matrix R m n)
    (r1 : ⟦ m ⟧%stn) (r2 : ⟦ m ⟧%stn)
    : (mat r1) = (mat r2) -> (gauss_switch_row mat r1 r2 ) = mat.
  Proof.
    intros m_eq.
    unfold gauss_switch_row.
    apply funextfun. intros i'.
    destruct (stn_eq_or_neq _ _) as [eq | neq];
      destruct (stn_eq_or_neq _ _) as [eq' | neq'];
      try rewrite eq; try rewrite eq';
      try rewrite m_eq; try reflexivity.
  Defined.

  Lemma gauss_switch_row_inv2
    {m n : nat} (mat : Matrix R m n)
    (r1 r2 : ⟦ m ⟧%stn) (j : (stn n))
    : (mat r1 j) = (mat r2 j) ->
      ∏ (r3 : ⟦ m ⟧%stn), (gauss_switch_row mat r1 r2 ) r3 j = mat r3 j.
  Proof.
    intros m_eq r3.
    unfold gauss_switch_row.
    destruct (stn_eq_or_neq _ _) as [eq | neq];
      destruct (stn_eq_or_neq _ _) as [eq' | neq'];
      try rewrite eq; try rewrite eq';
      try rewrite m_eq; reflexivity.
  Defined.

  Local Definition test_row_switch
    {m n : nat} (mat : Matrix R m n)
    (r1 r2 : ⟦ m ⟧%stn)
    : (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.
  Proof.
    use funextfun; intros i.
    use funextfun; intros j.
    unfold gauss_switch_row.
    destruct (stn_eq_or_neq i r1) as [ e_ir1 | ne_ir1 ].
    - destruct (stn_eq_or_neq r2 r1) as [ e_r1r2 | ne_r1r2 ].
      + destruct e_ir1, e_r1r2. apply idpath.
      + destruct (stn_eq_or_neq r2 r2) as [ ? | absurd ].
        * destruct e_ir1. apply idpath.
        * set (H := isirrefl_natneq _ absurd). destruct H.
    - destruct (stn_eq_or_neq i r2) as [ e_ir2 | ne_ir2 ].
      + destruct e_ir2.
        destruct (stn_eq_or_neq r1 r1) as [ ? | absurd ].
        * reflexivity.
        * destruct (stn_eq_or_neq r1 i) as [ e_ir1 | ne_ir1' ].
        -- rewrite e_ir1. apply idpath.
        -- set (H := isirrefl_natneq _ absurd). destruct H.
      + reflexivity.
  Defined.

End RowOps.

Section Elementary.

  (** The following three lemmata test the equivalence
     of multiplication by elementary matrices to swaps of indices. *)
  Lemma scalar_mult_mat_elementary
    {m n : nat} (mat : Matrix F m n) (s : F) (r : ⟦ m ⟧%stn)
    : ((mult_row_matrix s r) **'' mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros ?.
    unfold matrix_mult, mult_row_matrix, gauss_scalar_mult_row, row.
    destruct (stn_eq_or_neq i r) as [? | ?].
    - simpl coprod_rect.
      etrans.
      { apply maponpaths.
        etrans. { apply maponpaths_2, (@pointwise_comm2_vector F). }
        apply pointwise_assoc2_vector. }
      use sum_stdb_vector_pointwise_prod.
    - simpl coprod_rect.
      use sum_stdb_vector_pointwise_prod.
  Defined.

  Lemma switch_row_mat_elementary
    { m n : nat } (mat : Matrix R m n)
    (r1 r2 : ⟦ m ⟧%stn)
    : ((switch_row_matrix r1 r2) ** mat) = gauss_switch_row mat r1 r2.
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold switch_row_matrix, gauss_switch_row.
    apply funextfun. intros i.
    apply funextfun. intros ?.
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
    - simpl.
      rewrite (@pulse_function_sums_to_point R m
        (λ i : (⟦ m ⟧%stn), @identity_matrix R m r2 i * _)%ring r2).
      + unfold identity_matrix.
        rewrite stn_eq_or_neq_refl.
        simpl.
        apply (@riglunax2 R).
      + intros k r2_neq_k.
        rewrite (@id_mat_ij R m r2 k r2_neq_k).
        apply (@rigmult0x R).
    - simpl.
      pose (H' := @sum_id_pointwise_prod R).
      unfold pointwise in H'.
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
      + simpl.
        destruct (stn_eq_or_neq i r1) as [? | ?].
        * rewrite H'; apply idpath.
        * rewrite H'; apply idpath.
      + simpl; rewrite H'.
        apply idpath.
  Defined.

  Lemma add_row_mat_elementary
    { m n : nat } (mat : Matrix CR m n)
    (r1 r2 : ⟦ m ⟧%stn) (p : r1 ≠ r2) (s : CR)
    : ((add_row_matrix r1 r2 s) **' mat) = (gauss_add_row mat r1 r2 s).
  Proof.
    intros.
    apply funextfun. intros k.
    apply funextfun. intros l.
    unfold matrix_mult, add_row_matrix, gauss_add_row, row.
    destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
    - simpl coprod_rect.
      etrans. { apply maponpaths, (@pointwise_rdistr_vector CR). }
      etrans. { apply (@sum_pointwise_op1 CR). }
      apply map_on_two_paths.
      + etrans. 2: { apply maponpaths_2, k_eq_r2. }
        use sum_stdb_vector_pointwise_prod.
      + etrans.
        { apply maponpaths.
          etrans. { apply maponpaths_2, (@pointwise_comm2_vector CR). }
          apply pointwise_assoc2_vector. }
        use sum_stdb_vector_pointwise_prod.
    - use sum_stdb_vector_pointwise_prod.
  Defined.

  Lemma scalar_mult_matrix_product
    { n : nat }
    ( r : ⟦ n ⟧%stn ) ( s1 s2 : F )
    : ((mult_row_matrix s1 r ) **'' (mult_row_matrix s2 r ))
      = (mult_row_matrix (s1 * s2)%ring r ).
  Proof.
    rewrite scalar_mult_mat_elementary.
    unfold gauss_scalar_mult_row.
    unfold mult_row_matrix.
    apply funextfun; intros i.
    apply funextfun; intros j.
    destruct (stn_eq_or_neq i r);
      simpl coprod_rect.
    2: { reflexivity. }
    unfold pointwise.
    apply pathsinv0, rigassoc2.
  Defined.

  Lemma scalar_mult_matrix_one
    {n : nat} (r : ⟦ n ⟧%stn)
    : mult_row_matrix (@rigunel2 F) r = @identity_matrix F _.
  Proof.
    unfold mult_row_matrix.
    apply funextfun; intros i.
    destruct (stn_eq_or_neq i r); simpl coprod_rect.
    2: { reflexivity. }
    apply funextfun; intros j.
    apply (@riglunax2 F).
  Defined.

  Lemma scalar_mult_matrix_comm
    { n : nat } ( r : ⟦ n ⟧%stn ) ( s1 s2 : F )
    : ((mult_row_matrix s1 r) **'' (mult_row_matrix s2 r))
    = ((mult_row_matrix s2 r) **'' (mult_row_matrix s1 r)).
  Proof.
    do 2 rewrite scalar_mult_matrix_product.
    apply maponpaths_2, (rigcomm2 F).
  Defined.

  Lemma scalar_mult_matrix_invertible
    { n : nat }
    ( i : ⟦ n ⟧%stn ) ( s : F ) ( ne : s != (@rigunel1 F))
  : @matrix_inverse F _ (mult_row_matrix s i).
  Proof.
    exists (mult_row_matrix (fldmultinv s ne) i).
    split;
      refine (scalar_mult_matrix_product _ _ _ @ _);
      refine (_ @ scalar_mult_matrix_one i);
      apply maponpaths_2.
    - apply fldmultinvrax; assumption.
    - apply fldmultinvlax; assumption.
  Defined.

  Lemma add_row_matrix_plus_eq
    { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : CR ) (ne : r1 ≠ r2) :
    ((add_row_matrix r1 r2 s1 ) **' (add_row_matrix r1 r2 s2))
   = (add_row_matrix r1 r2 (s1 + s2)%ring).
  Proof.
    rewrite add_row_mat_elementary; try assumption.
    apply funextfun; intros i; apply funextfun; intros j.
    unfold gauss_add_row, add_row_matrix.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    2: {apply idpath. }
    destruct i_eq_r2.
    rewrite stn_eq_or_neq_refl, (stn_eq_or_neq_right ne); simpl.
    unfold scalar_lmult_vec, pointwise, const_vec.
    rewrite (@rigrdistr CR), rigcomm1, (@rigassoc1 CR).
    reflexivity.
  Defined.

  Lemma add_row_matrix_zero
      { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (ne : r1 ≠ r2)
    : add_row_matrix r1 r2 (@rigunel1 CR) = @identity_matrix CR _.
  Proof.
    apply funextfun; intros i.
    unfold add_row_matrix.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    2: { apply idpath. }
    destruct i_eq_r2. simpl.
    apply funextfun; intros j.
    unfold scalar_lmult_vec, pointwise.
    rewrite (@rigmult0x CR).
    apply (@rigrunax1 CR).
  Defined.

  Lemma add_row_matrix_commutes { n : nat }
        ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : CR ) (ne : r1 ≠ r2) :
       ((add_row_matrix r1 r2 s1 ) **' (add_row_matrix r1 r2 s2 ))
     = ((add_row_matrix r1 r2 s2 ) **' (add_row_matrix r1 r2 s1 )).
  Proof.
    do 2 (rewrite add_row_matrix_plus_eq; try assumption).
    apply maponpaths, (@rigcomm1 CR).
  Defined.

  Lemma add_row_matrix_invertible { n : nat } ( r1 r2 : ⟦ n ⟧%stn )
  (r1_neq_r2 : r1 ≠ r2) ( s : CR )
   : @matrix_inverse CR n (add_row_matrix r1 r2 s).
  Proof.
    exists (add_row_matrix r1 r2 (- s)%ring).
    split;
      refine (add_row_matrix_plus_eq _ _ _ _ r1_neq_r2 @ _);
      refine (_ @ add_row_matrix_zero _ _ r1_neq_r2);
      apply maponpaths.
    - apply (@ringrinvax1 CR).
    - apply (@ringlinvax1 CR).
  Defined.

  Lemma switch_row_matrix_involution
    { n : nat } ( r1 r2 : ⟦ n ⟧%stn )
    : ((switch_row_matrix r1 r2)
      ** (switch_row_matrix r1 r2))
      = @identity_matrix _ _.
  Proof.
    intros.
    rewrite switch_row_mat_elementary.
    unfold gauss_switch_row, switch_row_matrix.
    apply funextfun; intros i.
    destruct (stn_eq_or_neq i r1) as [eq | neq];
      destruct (stn_eq_or_neq r1 r2) as [eq' | neq'];
      rewrite stn_eq_or_neq_refl; simpl.
    - rewrite eq'; rewrite stn_eq_or_neq_refl; simpl.
      apply funextfun; intros j.
      rewrite <- eq', eq; apply idpath.
    - rewrite eq; simpl.
      rewrite (stn_eq_or_neq_right (issymm_stnneq neq')); simpl.
      reflexivity.
    - rewrite <- eq'; rewrite stn_eq_or_neq_refl; simpl.
      rewrite (stn_eq_or_neq_right neq); simpl.
      reflexivity.
    - rewrite stn_eq_or_neq_refl; simpl.
      destruct (stn_eq_or_neq _ _) as [eq | ?]; simpl.
      + now rewrite eq.
      + reflexivity.
  Defined.

  Lemma switch_row_matrix_invertible
    { n : nat } ( r1 r2 : ⟦ n ⟧%stn )
    : @matrix_inverse R n (switch_row_matrix r1 r2).
  Proof.
    exists (switch_row_matrix r1 r2).
    split; apply switch_row_matrix_involution.
  Defined.

End Elementary.

End GaussOps.
