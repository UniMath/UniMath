(** * Matrices

Elementary row operations on matrices, for elimination procedures

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.NumberSystems.RationalNumbers.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.

Require Import UniMath.Algebra.Elimination.Matrices.

Section GaussOps.
  (* TODO better (or any) comments for all these functions including assumptions*)
  (* TODO Carot operator is used similarly throughout the document, move out *)
  Local Notation Σ := (iterop_fun 0%hq op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).
  Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).

Section Auxiliary.

  (* TODO: generalize to rigs, upstream to Vectors *)
  Lemma pointwise_rdistr_vector { n : nat } (v1 v2 v3 : Vector hq n)
    : (pointwise n op1 v1 v2) ^ v3 = pointwise n op1 (v1 ^ v3) (v2 ^ v3).
  Proof.
    use (pointwise_rdistr (rigrdistr hq)).
  Defined.

  (* TODO: generalize to rigs, upstream to Vectors *)
  Lemma pointwise_assoc2_vector { n : nat } (v1 v2 v3 : Vector hq n)
    : (v1 ^ v2) ^ v3 = v1 ^ (v2 ^ v3).
  Proof.
    use (pointwise_assoc (rigassoc2 hq)).
  Defined.

  (* TODO: generalize to commrigs, upstream to Vectors *)
  Lemma pointwise_comm2_vector { n : nat } (v1 v2 : Vector hq n)
    : v1 ^ v2 = v2 ^ v1.
  Proof.
    use (pointwise_comm (rigcomm2 hq)).
  Defined.

End Auxiliary.

  (* Gaussian elimination over the field of rationals *)

  Definition gauss_add_row { m n : nat } ( mat : Matrix hq m n )
    ( r1 r2 : ⟦ m ⟧%stn )  ( s : hq ) : ( Matrix hq m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r2).
    - exact ( (mat r2 j) + ( s * (mat r1 j)))%rig.
    - exact (mat i j).
  Defined.

  (* TODO rename *)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : hq)
    : Matrix hq n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    (* TODO: here and elsewhere, probably better to use [scalar_lmult_vec] instead of this pointwise-product with [const_vec]; but will need lemmas about it abstracting away. *)
    - exact (pointwise n op1 (@stdb_vector hq n i) (const_vec s ^ ((@stdb_vector hq) n r1))).
    - exact (@stdb_vector hq n i).
  Defined.

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix hq m n)
    (s : hq) (r : ⟦ m ⟧%stn): Matrix hq m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
  Defined.

  Definition make_scalar_mult_row_matrix {n : nat}
    (s : hq) (r : ⟦ n ⟧%stn): Matrix hq n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r).
    - exact (const_vec s ^ @stdb_vector hq _ i).
    - exact (@stdb_vector hq _ i).
  Defined.

  Definition gauss_switch_row {m n : nat} (mat : Matrix hq m n)
             (r1 r2 : ⟦ m ⟧%stn) : Matrix hq m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (mat r2 j).
    - induction (stn_eq_or_neq i r2).
      + exact (mat r1 j).
      + exact (mat i j).
  Defined.

  Lemma gauss_switch_row_inv0 {m n : nat} (mat : Matrix hq m n)
        (r1 : ⟦ m ⟧%stn) (r2 : ⟦ m ⟧%stn) : ∏ (i : ⟦ m ⟧%stn), i ≠ r1 -> i ≠ r2
      -> (gauss_switch_row mat r1 r2 ) i = mat i.
  Proof.
    intros i i_ne_r1 i_ne_r2.
    unfold gauss_switch_row.
    apply funextfun. intros i'.
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1]
    ; destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    - simpl. rewrite i_eq_r2; apply idpath.
    - simpl. rewrite i_eq_r1 in i_ne_r1. apply isirrefl_natneq in i_ne_r1. contradiction.
    - simpl. rewrite i_eq_r2 in i_ne_r2. apply isirrefl_natneq in i_ne_r2. contradiction.
    - simpl. apply idpath.
  Defined.

  Lemma gauss_switch_row_inv1 {m n : nat} (mat : Matrix hq m n)
        (r1 : ⟦ m ⟧%stn) (r2 : ⟦ m ⟧%stn) : (mat r1) = (mat r2)
        -> (gauss_switch_row mat r1 r2 ) = mat.
  Proof.
    intros m_eq.
    unfold gauss_switch_row.
    apply funextfun. intros i'.
    destruct (stn_eq_or_neq _ _) as [eq | neq];
      destruct (stn_eq_or_neq _ _) as [eq' | neq'];
      try rewrite eq; try rewrite eq';
      try rewrite m_eq; try reflexivity.
  Defined.

  Lemma gauss_switch_row_inv2 {m n : nat} (mat : Matrix hq m n)
        (r1 r2 : ⟦ m ⟧%stn) (j : (stn n)): (mat r1 j) = (mat r2 j)
        -> ∏ (r3 : ⟦ m ⟧%stn), (gauss_switch_row mat r1 r2 ) r3 j = mat r3 j.
  Proof.
    intros m_eq r3.
    unfold gauss_switch_row.
    destruct (stn_eq_or_neq _ _) as [eq | neq];
      destruct (stn_eq_or_neq _ _) as [eq' | neq'];
      try rewrite eq; try rewrite eq';
      try rewrite m_eq; try reflexivity.
  Defined.

  Definition make_gauss_switch_row_matrix (n : nat)  (r1 r2 : ⟦ n ⟧ %stn) : Matrix hq n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r1).
    - exact (@identity_matrix hq n r2).
    - induction (stn_eq_or_neq i r2).
      + exact (@identity_matrix hq n r1).
      + exact (@identity_matrix hq n i).
  Defined.

  Definition test_row_switch {m n : nat} (mat : Matrix hq m n)
    (r1 r2 : ⟦ m ⟧%stn) : (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.
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

  (* The following three lemmata test the equivalence of multiplication by elementary matrices
     to swaps of indices. *)
  Lemma scalar_mult_mat_elementary
    {m n : nat} (mat : Matrix hq m n) (s : hq) (r : ⟦ m ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros ?.
    unfold matrix_mult, make_scalar_mult_row_matrix, gauss_scalar_mult_row, row.
    destruct (stn_eq_or_neq i r) as [? | ?].
    - simpl coprod_rect.
      etrans.
      { apply maponpaths.
        etrans. { apply maponpaths_2, pointwise_comm2_vector. }
        apply pointwise_assoc2_vector. }
      use sum_stdb_vector_pointwise_prod.
    - simpl coprod_rect.
      use sum_stdb_vector_pointwise_prod.
  Defined.

  (* TODO should certainly be over R *)
  Lemma switch_row_mat_elementary { m n : nat } (mat : Matrix hq m n)
    (r1 r2 : ⟦ m ⟧%stn) :
    ((make_gauss_switch_row_matrix m r1 r2) ** mat) = gauss_switch_row mat r1 r2.
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_gauss_switch_row_matrix, gauss_switch_row.
    apply funextfun. intros i.
    apply funextfun. intros ?.
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
    - simpl.
      rewrite (@pulse_function_sums_to_point hq m
        (λ i : (⟦ m ⟧%stn), @identity_matrix hq m r2 i * _)%ring r2).
      + unfold identity_matrix.
        rewrite stn_eq_or_neq_refl.
        simpl.
        apply (@riglunax2 hq).
      + intros k r2_neq_k.
        rewrite (@id_mat_ij hq m r2 k r2_neq_k).
        apply (@rigmult0x hq).
    - simpl.
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
      + simpl.
        destruct (stn_eq_or_neq i r1) as [? | ?].
        * rewrite (@sum_id_pointwise_prod_unf hq).
          apply idpath.
        * rewrite (@sum_id_pointwise_prod_unf hq).
          apply idpath.
      + simpl.
        rewrite (@sum_id_pointwise_prod_unf hq).
        apply idpath.
  Defined.

  (* TODO fix mixed up signatures on add_row  / make_add_row_matrix *)
  Lemma add_row_mat_elementary { m n : nat } (mat : Matrix hq m n)
  (r1 r2 : ⟦ m ⟧%stn) (p : r1 ≠ r2) (s : hq)
  : ((make_add_row_matrix  r1 r2 s) ** mat)  = (gauss_add_row mat r1 r2 s).
  Proof.
    intros.
    apply funextfun. intros k.
    apply funextfun. intros l.
    unfold matrix_mult, make_add_row_matrix, gauss_add_row, row.
    destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
    - simpl coprod_rect.
      etrans. { apply maponpaths, pointwise_rdistr_vector. }
      etrans. { apply (@sum_pointwise_op1 hq). }
      apply map_on_two_paths.
      + etrans. 2: { apply maponpaths_2, k_eq_r2. }
        use sum_stdb_vector_pointwise_prod.
      + etrans.
        { apply maponpaths.
          etrans. { apply maponpaths_2, pointwise_comm2_vector. }
          apply pointwise_assoc2_vector. }
        use sum_stdb_vector_pointwise_prod.
    - use sum_stdb_vector_pointwise_prod.
  Defined.

  Lemma scalar_mult_matrix_multiplicative { n : nat }
        ( r : ⟦ n ⟧%stn ) ( s1 s2 : hq ) :
    ((make_scalar_mult_row_matrix s1 r ) ** (make_scalar_mult_row_matrix s2 r ))
   = (make_scalar_mult_row_matrix (s1 * s2)%hq r ).
  Proof.
    rewrite scalar_mult_mat_elementary.
    unfold gauss_scalar_mult_row.
    unfold make_scalar_mult_row_matrix.
    apply funextfun; intros i.
    apply funextfun; intros j.
    destruct (stn_eq_or_neq i r);
      simpl coprod_rect.
    2: { reflexivity. }
    unfold pointwise.
    apply pathsinv0, rigassoc2.
  Defined.

  Lemma scalar_mult_matrix_one {n : nat} (r : ⟦ n ⟧%stn)
    : make_scalar_mult_row_matrix 1%hq r
    = @identity_matrix hq _.
  Proof.
    unfold make_scalar_mult_row_matrix.
    apply funextfun; intros i.
    destruct (stn_eq_or_neq i r); simpl coprod_rect.
    2: { reflexivity. }
    apply funextfun; intros j. apply (@riglunax2 hq).
  Defined.

  (* For hq at least *)
  Lemma scalar_mult_matrix_comm { n : nat } ( r : ⟦ n ⟧%stn ) ( s1 s2 : hq ) :
      ((make_scalar_mult_row_matrix s1 r ) ** (make_scalar_mult_row_matrix s2 r))
    = ((make_scalar_mult_row_matrix s2 r ) ** (make_scalar_mult_row_matrix s1 r)).
  Proof.
    do 2 rewrite scalar_mult_matrix_multiplicative.
    apply maponpaths_2, (rigcomm2 hq).
  Defined.

  (* TODO : hq should also be a general field, not short-hand for rationals specifically.
            This does not mandate any real change in any proofs ?*)
  Lemma scalar_mult_matrix_is_inv { n : nat } ( i : ⟦ n ⟧%stn ) ( s : hq ) ( ne : hqneq s 0%hq )
  : @matrix_inverse hq n (make_scalar_mult_row_matrix s i).
  Proof.
    exists (make_scalar_mult_row_matrix (hqmultinv s) i).
    split;
      refine (scalar_mult_matrix_multiplicative _ _ _ @ _);
      refine (_ @ scalar_mult_matrix_one i);
      apply maponpaths_2.
    - apply hqisrinvmultinv; assumption.
    - apply hqislinvmultinv; assumption.
  Defined.

  Lemma add_row_matrix_additive
    { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : hq ) (ne : r1 ≠ r2) :
    ((make_add_row_matrix r1 r2 s1 ) ** (make_add_row_matrix r1 r2 s2 ))
   = (make_add_row_matrix r1 r2 (s1 + s2)%hq ).
  Proof.
    rewrite add_row_mat_elementary; try assumption.
    apply funextfun; intros i; apply funextfun; intros j.
    unfold gauss_add_row, make_add_row_matrix.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    2: {apply idpath. }
    destruct i_eq_r2.
    simpl.
    rewrite stn_eq_or_neq_refl, (stn_eq_or_neq_right ne).
    simpl.
    unfold pointwise, const_vec.
    rewrite (@rigrdistr hq).
    rewrite rigcomm1.
    rewrite (@rigassoc1 hq).
    reflexivity.
  Time Defined.

  Lemma add_row_matrix_zero
      { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (ne : r1 ≠ r2)
    : make_add_row_matrix r1 r2 0%hq = @identity_matrix hq _.
  Proof.
    apply funextfun; intros i.
    unfold make_add_row_matrix.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    2: { apply idpath. }
    destruct i_eq_r2. simpl.
    apply funextfun; intros j.
    unfold pointwise.
    rewrite (@rigmult0x hq).
    apply (@rigrunax1 hq).
  Defined.

  Lemma add_row_matrix_commutes { n : nat }
        ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : hq ) (ne : r1 ≠ r2) :
     ((make_add_row_matrix r1 r2 s1 ) ** (make_add_row_matrix r1 r2 s2 ))
     = ((make_add_row_matrix r1 r2 s2 ) ** (make_add_row_matrix r1 r2 s1 )).
  Proof.
    rewrite add_row_matrix_additive; try assumption.
    rewrite add_row_matrix_additive; try assumption.
    apply maponpaths.
    apply (@rigcomm1 hq).
  Defined.

  Lemma add_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (r1_neq_r2 : r1 ≠ r2) ( s : hq )
   : @matrix_inverse hq n (make_add_row_matrix r1 r2 s).
  Proof.
    exists (make_add_row_matrix r1 r2 (- s)%hq).
    split;
      refine (add_row_matrix_additive _ _ _ _ r1_neq_r2 @ _);
      refine (_ @ add_row_matrix_zero _ _ r1_neq_r2);
      apply maponpaths.
    - apply (@ringrinvax1 hq).
    - apply (@ringlinvax1 hq).
  Defined.

  Lemma switch_row_matrix_self_inverse { n : nat }
    ( r1 r2 : ⟦ n ⟧%stn ) :
       ((make_gauss_switch_row_matrix n r1 r2)
     ** (make_gauss_switch_row_matrix n r1 r2))
      = @identity_matrix hq n.
  Proof.
    intros.
    rewrite switch_row_mat_elementary.
    unfold gauss_switch_row, make_gauss_switch_row_matrix.
    apply funextfun; intros i; apply funextfun; intros j.
    destruct (stn_eq_or_neq i j) as [eq | neq].
    - rewrite eq; simpl.
      destruct (stn_eq_or_neq r1 r2) as [r1_eq_r2 | r1_neq_r2].
      + simpl.
        rewrite stn_eq_or_neq_refl; simpl.
        rewrite r1_eq_r2 in *.
        destruct (stn_eq_or_neq j r2) as [j_eq_r2 | j_neq_r2].
        { simpl.
          rewrite j_eq_r2.
          rewrite stn_eq_or_neq_refl; simpl.
          reflexivity. }
        simpl.
        apply idpath.
      + simpl.
        rewrite stn_eq_or_neq_refl; simpl.
        rewrite stn_eq_or_neq_refl; simpl.
        destruct (stn_eq_or_neq j r1) as [j_eq_r1 | j_neq_r1].
        { simpl.
          rewrite j_eq_r1.
          apply issymm_natneq in r1_neq_r2.
          rewrite (stn_eq_or_neq_right r1_neq_r2).
          apply idpath. }
        simpl.
        destruct (stn_eq_or_neq j r2) as [j_eq_r2 | j_neq_r2].
        { simpl.
          rewrite j_eq_r2.
          apply idpath. }
        simpl.
        apply idpath.
    - rewrite stn_eq_or_neq_refl; simpl.
      destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
      { simpl.
        rewrite i_eq_r1.
        destruct (stn_eq_or_neq r2 r1) as [r2_eq_r1 | r2_neq_r1].
        - simpl.
          rewrite r2_eq_r1.
          reflexivity.
        - simpl.
          reflexivity.
      }
      simpl.
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
      { simpl.
        rewrite i_eq_r2.
        simpl.
        rewrite stn_eq_or_neq_refl; simpl.
        rewrite <- i_eq_r2.
        apply issymm_natneq in i_neq_r1.
        reflexivity.
      }
      simpl.
      apply idpath.
  Defined.

  Lemma switch_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ):
    @matrix_inverse hq n (make_gauss_switch_row_matrix n r1 r2).
  Proof.
    (* intros. *)
    use tpair.
    { exact (make_gauss_switch_row_matrix n r1 r2). }
    assert (proof : ((make_gauss_switch_row_matrix n r1 r2) **
                    (make_gauss_switch_row_matrix n r1 r2)) = identity_matrix).
    { apply switch_row_matrix_self_inverse. }
    - use tpair.
      + exact proof.
      + simpl.
        exact proof.
  Defined.

End GaussOps.
