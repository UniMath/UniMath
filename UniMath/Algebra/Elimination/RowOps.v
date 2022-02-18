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

  (* Gaussian elimination over the field of rationals *)

  Definition gauss_add_row { m n : nat } ( mat : Matrix hq m n )
    ( r1 r2 : ⟦ m ⟧%stn )  ( s : hq ) : ( Matrix hq m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r2).
    - exact ( op1 ( mat r2 j )  ( op2 s ( mat r1 j ))).
    - exact ( mat i j ).
  Defined.

  Definition gauss_add_row_comp1 { m n : nat } ( mat : Matrix hq m n )
    ( r1 r2 : ⟦ m ⟧%stn ) (s : hq) (c : ⟦ n ⟧%stn)
    : (gauss_add_row mat r1 r2 s) r2 c = op1 (mat r2 c) (op2 s (mat r1 c)).
  Proof.
    unfold gauss_add_row.
    rewrite stn_eq_or_neq_refl.
    simpl. reflexivity.
  Qed.

  Definition add_row_op { n : nat } (mat : Matrix hq n n) (r1 r2 : ⟦ n ⟧ %stn) (s : hq) : Matrix hq n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (mat r1) (mat r2)).
    - exact (mat i).
  Defined.

  (* TODO rename *)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : hq)  : Matrix hq n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (@identity_matrix hq n i) (const_vec s ^ ((@identity_matrix hq) n r1))).
    - exact (@identity_matrix hq n i).
  Defined.

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix hq m n)
    (s : hq) (r : ⟦ m ⟧%stn): Matrix hq m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
  Defined.

  (* TODO  generalize to m x n whereever possible*)
  Definition make_scalar_mult_row_matrix { n : nat}
    (s : hq) (r : ⟦ n ⟧%stn): Matrix hq n n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i j).
      - induction (stn_eq_or_neq i r).
        + exact s.
        + exact 1%hq.
      - exact 0%hq.
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

  Lemma gauss_switch_row_inv0 {m n : nat} (mat : Matrix hq n n)
        (r1 : ⟦ n ⟧%stn) (r2 : ⟦ n ⟧%stn) : ∏ (i : ⟦ n ⟧%stn), i ≠ r1 -> i ≠ r2
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

  Lemma gauss_switch_row_inv1 {m n : nat} (mat : Matrix hq n n)
        (r1 : ⟦ n ⟧%stn) (r2 : ⟦ n ⟧%stn) : (mat r1) = (mat r2)
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

  Lemma gauss_switch_row_inv2 {m n : nat} (mat : Matrix hq n n)
        (r1 r2 j : ⟦ n ⟧%stn) : (mat r1 j) = (mat r2 j)
        -> ∏ (r3 : ⟦ n ⟧%stn), (gauss_switch_row mat r1 r2 ) r3 j = mat r3 j.
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
  Lemma scalar_mult_mat_elementary {n : nat} (mat : Matrix hq n n) (s : hq) (r : ⟦ n ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros ?.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_scalar_mult_row_matrix. unfold gauss_scalar_mult_row.
    assert (p : n > 0). { apply (stn_implies_ngt0 r). }
    destruct (stn_eq_or_neq i r) as [? | ?].
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' hq n _ p i ).
      + rewrite stn_eq_or_neq_refl.
        simpl.
        apply idpath.
      + intros k i_neq_k.
        rewrite (stn_eq_or_neq_right i_neq_k).
        simpl.
        apply (@rigmult0x hq).
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' hq n _ p i ).
      + rewrite stn_eq_or_neq_refl.
        simpl.
        rewrite (@riglunax2 hq).
        reflexivity.
      + intros k i_neq_k.
        rewrite (stn_eq_or_neq_right i_neq_k).
        simpl.
        apply (@rigmult0x hq).
  Defined.

  (* TODO should certainly be over R *)
  Lemma switch_row_mat_elementary { n : nat } (mat : Matrix hq n n) (r1 r2 : ⟦ n ⟧%stn) :
    ((make_gauss_switch_row_matrix n r1 r2) ** mat)  = gauss_switch_row mat r1 r2.
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_gauss_switch_row_matrix, gauss_switch_row.
    apply funextfun. intros i.
    apply funextfun. intros ?.
    assert (p: n > 0).  { apply ( stn_implies_ngt0 r1).  }
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' hq n (λ i : (⟦ n ⟧%stn), @identity_matrix hq n r2 i * _)%ring p r2).
      + unfold identity_matrix.
        rewrite stn_eq_or_neq_refl.
        simpl.
        apply (@riglunax2 hq).
      + intros k r2_neq_k.
        rewrite (@id_mat_ij hq n r2 k r2_neq_k).
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
  Lemma add_row_mat_elementary { n : nat } (mat : Matrix hq n n)
  (r1 r2 : ⟦ n ⟧%stn) (p : r1 ≠ r2) (s : hq)
  : ((make_add_row_matrix  r1 r2 s) ** mat)  = (gauss_add_row mat r1 r2 s).
  Proof.
    intros.
    unfold make_add_row_matrix, gauss_add_row.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold pointwise.
    apply funextfun. intros k.
    apply funextfun. intros l.
    assert (p': n > 0). { apply (stn_implies_ngt0 r1). }
    destruct (stn_eq_or_neq k r1) as [k_eq_r1 | k_neq_r1].
    - simpl.
      destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
      + simpl.
        rewrite k_eq_r1 in k_eq_r2.
        rewrite k_eq_r2 in p.
        apply isirrefl_natneq in p.
        contradiction.
      + simpl.
        rewrite (@pulse_function_sums_to_point_rig'' hq n
          (λ i : (⟦ n ⟧%stn), @identity_matrix hq n k i * _)%ring p' k).
        * rewrite k_eq_r1 in *.
          rewrite id_mat_ii.
          rewrite (@riglunax2 hq).
          apply idpath.
        * intros j k_neq_j.
          rewrite (id_mat_ij k j k_neq_j).
          apply (@rigmult0x hq).
    - destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
      + simpl.
        rewrite (@two_pulse_function_sums_to_point_rig hq n
          (λ i : ( ⟦ n ⟧%stn), ((@identity_matrix hq n  _ _ + _ * _) * _ ))%rig p' k r1).
        * unfold const_vec, identity_matrix.
          rewrite stn_eq_or_neq_refl. simpl.
          apply issymm_natneq in k_neq_r1.
          rewrite (stn_eq_or_neq_right k_neq_r1). simpl.
          rewrite stn_eq_or_neq_refl. simpl.
          apply issymm_natneq in k_neq_r1.
          rewrite (stn_eq_or_neq_right k_neq_r1). simpl.
          rewrite (@rigmultx0 hq).
          rewrite (@rigrunax1 hq).
          rewrite (@riglunax1 hq (s * _))%hq.
          rewrite (@rigrunax2 hq).
          rewrite (@riglunax2 hq).
          rewrite k_eq_r2.
          apply idpath.
        * exact k_neq_r1.
        * intros q q_neq_k q_neq_k'.
          unfold identity_matrix.
          apply issymm_natneq in q_neq_k.
          rewrite (stn_eq_or_neq_right q_neq_k).
          simpl.
          rewrite (@riglunax1 hq).
          unfold const_vec.
          apply issymm_natneq in q_neq_k'.
          rewrite (stn_eq_or_neq_right q_neq_k').
          simpl.
          rewrite (@rigmultx0 hq).
          rewrite (@rigmult0x hq).
          apply idpath.
      + simpl.
        rewrite (@sum_id_pointwise_prod_unf hq).
        apply idpath.
  Defined.

  (* For hq at least *)
  Lemma scalar_mult_matrix_comm { n : nat } ( r : ⟦ n ⟧%stn ) ( s1 s2 : hq ) :
      ((make_scalar_mult_row_matrix s1 r ) ** (make_scalar_mult_row_matrix s2 r))
    = ((make_scalar_mult_row_matrix s2 r ) ** (make_scalar_mult_row_matrix s1 r)).
  Proof.
    do 2 rewrite scalar_mult_mat_elementary.
    unfold gauss_scalar_mult_row.
    unfold make_scalar_mult_row_matrix.
    apply funextfun; intros i.
    apply funextfun; intros j.
    destruct (stn_eq_or_neq _ _).
    2: { simpl; reflexivity. }
    simpl.
    destruct (stn_eq_or_neq _ _).
    - simpl.
      rewrite (hqmultcomm); reflexivity. (* This works for fields with commutative multiplication *)
    - simpl.
      do 2 rewrite (@rigmultx0 hq).
      reflexivity.
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
    destruct (stn_eq_or_neq i j).
    2: { simpl.
         destruct (stn_eq_or_neq i r).
         - simpl. rewrite (@rigmultx0 hq).
           reflexivity.
         - simpl.
           reflexivity.
    }
    simpl.
    destruct (stn_eq_or_neq i r).
    2: {simpl; reflexivity. }
    simpl.
    reflexivity.
  Defined.


  (* TODO : hq should also be a general field, not short-hand for rationals specifically.
            This does not mandate any real change in any proofs ?*)
  Lemma scalar_mult_matrix_is_inv { n : nat } ( i : ⟦ n ⟧%stn ) ( s : hq ) ( ne : hqneq s 0%hq ) :
    @matrix_inverse hq n (make_scalar_mult_row_matrix s i ).
  Proof.
    set (B :=  (make_scalar_mult_row_matrix (hqmultinv s ) i)).
    use tpair.
    { exact B. }
    assert (left : ((make_scalar_mult_row_matrix s i) ** B) = identity_matrix).
    { unfold B.
      rewrite scalar_mult_matrix_comm.
      rewrite scalar_mult_mat_elementary.
      apply funextfun. intros k.
      apply funextfun. intros l.
      unfold gauss_scalar_mult_row.
      unfold  make_scalar_mult_row_matrix.
      destruct (stn_eq_or_neq k l) as [T' | F'].
      + (*rewrite T.*)
        destruct (stn_eq_or_neq l i).
        * destruct (stn_eq_or_neq l l).
          2 : { apply isirrefl_natneq in h.
                apply fromempty. assumption. }
          -- rewrite T'. rewrite p.
             destruct (stn_eq_or_neq i i).
             ++ do 2 rewrite coprod_rect_compute_1.
                simpl.
                rewrite hqislinvmultinv; try assumption.
                rewrite id_mat_ii. reflexivity.
             ++ remember h as h'. clear Heqh'.
                apply isirrefl_natneq in h.
                apply fromempty. assumption.
        * rewrite <- T' in h.
          simpl.
          destruct (stn_eq_or_neq k i) as [k_eq_i | k_neq_i].
          { rewrite k_eq_i in h.
            apply isirrefl_natneq in h. (* TODO fix h *)
            contradiction.
          }
          simpl.
          rewrite T'.
          rewrite id_mat_ii; reflexivity.
      + destruct (stn_eq_or_neq k l) as [cntr | dup ].
        { apply fromempty.
          rewrite cntr in F'. (* really should have a one_liner *)
          apply isirrefl_natneq in F'.
          apply fromempty. assumption.
        }
        simpl.
        destruct (stn_eq_or_neq k i).
        { simpl.
          rewrite (@rigmultx0 hq).
          rewrite id_mat_ij; try reflexivity; assumption. }
        simpl.
        rewrite id_mat_ij; try reflexivity; assumption.
    }
    use tpair.
    - apply left.
    - simpl.
      unfold B. rewrite <- scalar_mult_matrix_comm.
      apply left.
  Defined.

  Lemma add_row_matrix_additive { n : nat }
        ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : hq ) (ne : r1 ≠ r2) :
    ((make_add_row_matrix r1 r2 s1 ) ** (make_add_row_matrix r1 r2 s2 ))
   = (make_add_row_matrix r1 r2 (s1 + s2)%hq ).
  Proof.
    rewrite add_row_mat_elementary; try assumption.
    unfold gauss_add_row, make_add_row_matrix.
    apply funextfun; intros i; apply funextfun; intros j.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    2: {apply idpath. }
    simpl.
    rewrite stn_eq_or_neq_refl.
    rewrite (stn_eq_or_neq_right ne).
    simpl.
    unfold pointwise.
    rewrite i_eq_r2.
    unfold const_vec.
    rewrite (@rigrdistr hq).
    rewrite rigcomm1.
    rewrite (@rigassoc1 hq).
    reflexivity.
  Defined.

  Lemma add_row_matrix_commutes { n : nat }
        ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : hq ) (ne : r1 ≠ r2) :
     ((make_add_row_matrix r1 r2 s1 ) ** (make_add_row_matrix r1 r2 s2 ))
     = ((make_add_row_matrix r1 r2 s2 ) ** (make_add_row_matrix r1 r2 s1 )).
  Proof.
    rewrite add_row_matrix_additive; try assumption.
    rewrite add_row_matrix_additive; try assumption.
    unfold make_add_row_matrix, pointwise, const_vec.
    apply funextfun; intros i; apply funextfun; intros j.
    destruct (stn_eq_or_neq _ _) as [i_eq_r2 | i_neq_r2].
    2: {apply idpath. }
    simpl.
    apply maponpaths.
    rewrite (@rigcomm1 hq).
    reflexivity.
  Defined.

  Lemma add_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (r1_neq_r2 : r1 ≠ r2) ( s : hq )
    (p' : n > 0):
    @matrix_inverse hq n (make_add_row_matrix r1 r2 s).
  Proof.
    use tpair.
    {
      induction (stn_eq_or_neq r1 r2) as [? | ?].
      - exact (make_add_row_matrix r1 r2 (hqmultinv s)). (* Contradiction also works *)
      - exact (make_add_row_matrix r1 r2 (- s)%hq).
    }
    assert (proof :
     ((make_add_row_matrix r1 r2 s)  ** (make_add_row_matrix r1 r2 (- s)%hq))
      = @identity_matrix hq n).
    { unfold make_add_row_matrix, identity_matrix, pointwise.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    (*use tpair.*) (*TODO was there a quicker alternative ? *)
    - apply funextfun. intros k.
      apply funextfun. intros l.
      destruct (stn_eq_or_neq r1 r2) as [r1_eq_r2 | r1_neq_r2'].
      + rewrite r1_eq_r2 in r1_neq_r2.
        apply isirrefl_natneq in r1_neq_r2.
        contradiction.
      + simpl.
        destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2]
        ; destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l]; simpl.
        * rewrite (@two_pulse_function_sums_to_point_rig hq n _ p' k r1).
          -- do 2 rewrite stn_eq_or_neq_refl. simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2).
             rewrite k_eq_l in *.
             rewrite k_eq_r2 in *.
             rewrite (stn_eq_or_neq_right r1_neq_r2'). simpl.
             rewrite (@rigmultx0 hq); rewrite (@rigrunax1 hq); rewrite (@riglunax2 hq).
             rewrite stn_eq_or_neq_refl; simpl.
             rewrite stn_eq_or_neq_refl; simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2').
             rewrite (@rigmultx0 hq); simpl; rewrite (@rigmultx0 hq).
             do 2 rewrite (@rigrunax1 hq).
             apply idpath.
          -- rewrite k_eq_r2.
             apply issymm_natneq in r1_neq_r2'.
             assumption.
          -- intros q q_neq_k q_neq_r1.
             rewrite k_eq_r2, k_eq_l in *.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             apply issymm_natneq in q_neq_k. (* TODO this is repeated quite often... *)
             rewrite (stn_eq_or_neq_right q_neq_k).
             apply issymm_natneq in q_neq_r1.
             rewrite (stn_eq_or_neq_right q_neq_r1).
             rewrite (@rigmultx0 hq).
             apply idpath.
        *  rewrite (@two_pulse_function_sums_to_point_rig hq n _ p' k r1).
           -- rewrite (stn_eq_or_neq_right r1_neq_r2); simpl.
              rewrite stn_eq_or_neq_refl. simpl.
              rewrite k_eq_r2 in *.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              rewrite stn_eq_or_neq_refl.
              simpl.
              rewrite (stn_eq_or_neq_right k_neq_l).
              rewrite (@rigmultx0 hq); rewrite (@rigrunax1 hq); rewrite (@riglunax2 hq); rewrite (@riglunax1 hq).
              unfold const_vec.
              rewrite stn_eq_or_neq_refl.
              apply issymm_natneq in r1_neq_r2'.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              destruct (stn_eq_or_neq r1 l) as [r1_eq_l | r1_neq_l].
              ++ simpl.
                 do 3 rewrite (@rigrunax2 hq).
                 rewrite (hqpluscomm _ s) . (* Only place we mention hq ? TODO don't? *)
                 rewrite hqplusr0.
                 rewrite hqlminus.
                 apply idpath.
              ++ repeat rewrite (@rigmultx0 hq).
                 rewrite (@rigrunax1 hq).
                 apply idpath.
           -- rewrite k_eq_r2.
              apply issymm_natneq.
              assumption.
           -- intros q q_neq_k q_neq_r1.
              rewrite k_eq_r2 in *.
              apply issymm_natneq in q_neq_k.
              rewrite (stn_eq_or_neq_right q_neq_k).
              unfold const_vec.
              apply issymm_natneq in q_neq_r1.
              rewrite (stn_eq_or_neq_right q_neq_r1).
              rewrite (@riglunax1 hq).
              rewrite (@rigmultx0 hq).
              rewrite (@rigmult0x hq).
              apply idpath.
        * rewrite k_eq_l in *.
          set (cl := setquot _ ).
          rewrite (@pulse_function_sums_to_point_rig''  hq n _  p' l).
          -- rewrite (stn_eq_or_neq_refl); simpl.
             rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
             rewrite (@riglunax2 hq).
             rewrite (stn_eq_or_neq_refl); simpl.
             apply idpath.
          -- intros q l_neq_q; simpl.
             rewrite (stn_eq_or_neq_right l_neq_q); simpl.
             apply (@rigmult0x hq).
        *  rewrite (@pulse_function_sums_to_point_rig''  hq n _  p' l).
           { rewrite (stn_eq_or_neq_right k_neq_l); simpl. apply (@rigmult0x hq). }
           intros q q_neq_j.
           destruct (stn_eq_or_neq k q) as [k_eq_q | k_neq_q]; simpl.
           -- rewrite k_eq_q in *.
              rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
              rewrite (stn_eq_or_neq_right k_neq_l); simpl.
              apply (@rigmultx0 hq).
           -- apply (@rigmult0x hq).
    }
    destruct (stn_eq_or_neq r1 r2) as [absurd | ?].
    { rewrite absurd in r1_neq_r2. apply isirrefl_natneq in r1_neq_r2.
      contradiction. }
    simpl.
    use tpair.
    { apply proof. }
    simpl.
    rewrite add_row_matrix_commutes; try assumption; apply proof.
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
