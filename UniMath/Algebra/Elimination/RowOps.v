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
  Context { F : fld }.
  Local Notation Σ := (iterop_fun 0%ring op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).

  (* Gaussian elimination over the field of rationals *)

  Definition gauss_add_row { m n : nat } ( mat : Matrix F m n )
    ( r1 r2 : ⟦ m ⟧%stn )  ( s : F ) : ( Matrix F m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r2).
    - exact ( op1 ( mat r2 j )  ( op2 s ( mat r1 j ))).
    - exact ( mat i j ).
  Defined.

  (* TODO rename *)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : F)  : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (@identity_matrix F n i) (const_vec s ^ ((@identity_matrix F) n r1))).
    - exact (@identity_matrix F n i).
  Defined.

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix F m n)
    (s : F) (r : ⟦ m ⟧%stn): Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
  Defined.

  (* TODO  generalize to m x n whereever possible*)
  Definition make_scalar_mult_row_matrix {n : nat}
    (s : F) (r : ⟦ n ⟧%stn): Matrix F n n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i j).
      - induction (stn_eq_or_neq i r).
        + exact s.
        + exact 1%ring.
      - exact 0%ring.
  Defined.

  Definition gauss_switch_row {m n : nat} (mat : Matrix F m n)
             (r1 r2 : ⟦ m ⟧%stn) : Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (mat r2 j).
    - induction (stn_eq_or_neq i r2).
      + exact (mat r1 j).
      + exact (mat i j).
  Defined.

  Lemma gauss_switch_row_inv0 {m n : nat} (mat : Matrix F m n)
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

  Lemma gauss_switch_row_inv1 {m n : nat} (mat : Matrix F m n)
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

  Lemma gauss_switch_row_inv2 {m n : nat} (mat : Matrix F m n)
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

  Definition make_gauss_switch_row_matrix (n : nat)  (r1 r2 : ⟦ n ⟧ %stn) : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r1).
    - exact (@identity_matrix F n r2).
    - induction (stn_eq_or_neq i r2).
      + exact (@identity_matrix F n r1).
      + exact (@identity_matrix F n i).
  Defined.

  Definition test_row_switch {m n : nat} (mat : Matrix F m n)
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
    {m n : nat} (mat : Matrix F m n) (s : F) (r : ⟦ m ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros ?.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_scalar_mult_row_matrix. unfold gauss_scalar_mult_row.
    assert (p : m > 0). { apply (stn_implies_ngt0 r). }
    destruct (stn_eq_or_neq i r) as [? | ?].
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F m _ p i ).
      + rewrite stn_eq_or_neq_refl.
        simpl.
        apply idpath.
      + intros k i_neq_k.
        rewrite (stn_eq_or_neq_right i_neq_k).
        simpl.
        apply (@rigmult0x F).
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F m _ p i ).
      + rewrite stn_eq_or_neq_refl.
        simpl.
        rewrite (@riglunax2 F).
        reflexivity.
      + intros k i_neq_k.
        rewrite (stn_eq_or_neq_right i_neq_k).
        simpl.
        apply (@rigmult0x F).
  Defined.

  (* TODO should certainly be over R *)
  Lemma switch_row_mat_elementary { m n : nat } (mat : Matrix F m n)
    (r1 r2 : ⟦ m ⟧%stn) :
    ((make_gauss_switch_row_matrix m r1 r2) ** mat) = gauss_switch_row mat r1 r2.
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_gauss_switch_row_matrix, gauss_switch_row.
    apply funextfun. intros i.
    apply funextfun. intros ?.
    assert (p: m > 0).  { apply ( stn_implies_ngt0 r1).  }
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F m
        (λ i : (⟦ m ⟧%stn), @identity_matrix F m r2 i * _)%ring p r2).
      + unfold identity_matrix.
        rewrite stn_eq_or_neq_refl.
        simpl.
        apply (@riglunax2 F).
      + intros k r2_neq_k.
        rewrite (@id_mat_ij F m r2 k r2_neq_k).
        apply (@rigmult0x F).
    - simpl.
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
      + simpl.
        destruct (stn_eq_or_neq i r1) as [? | ?].
        * rewrite (@sum_id_pointwise_prod_unf F).
          apply idpath.
        * rewrite (@sum_id_pointwise_prod_unf F).
          apply idpath.
      + simpl.
        rewrite (@sum_id_pointwise_prod_unf F).
        apply idpath.
  Defined.

  (* TODO fix mixed up signatures on add_row  / make_add_row_matrix *)
  Lemma add_row_mat_elementary { m n : nat } (mat : Matrix F m n)
  (r1 r2 : ⟦ m ⟧%stn) (p : r1 ≠ r2) (s : F)
  : ((make_add_row_matrix  r1 r2 s) ** mat)  = (gauss_add_row mat r1 r2 s).
  Proof.
    intros.
    unfold make_add_row_matrix, gauss_add_row.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold pointwise.
    apply funextfun. intros k.
    apply funextfun. intros l.
    assert (p': m > 0). { apply (stn_implies_ngt0 r1). }
    destruct (stn_eq_or_neq k r1) as [k_eq_r1 | k_neq_r1].
    - simpl.
      destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
      + simpl.
        rewrite k_eq_r1 in k_eq_r2.
        rewrite k_eq_r2 in p.
        apply isirrefl_natneq in p.
        contradiction.
      + simpl.
        rewrite (@pulse_function_sums_to_point_rig'' F m
          (λ i : (⟦ m ⟧%stn), @identity_matrix F m k i * _)%ring p' k).
        * rewrite k_eq_r1 in *.
          rewrite id_mat_ii.
          rewrite (@riglunax2 F).
          apply idpath.
        * intros j k_neq_j.
          rewrite (id_mat_ij k j k_neq_j).
          apply (@rigmult0x F).
    - destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
      + simpl.
        rewrite (@two_pulse_function_sums_to_point_rig F m
          (λ i : ( ⟦ m ⟧%stn), ((@identity_matrix F m _ _ + _ * _) * _ ))%rig p' k r1).
        * unfold const_vec, identity_matrix.
          rewrite stn_eq_or_neq_refl. simpl.
          apply issymm_natneq in k_neq_r1.
          rewrite (stn_eq_or_neq_right k_neq_r1). simpl.
          rewrite stn_eq_or_neq_refl. simpl.
          apply issymm_natneq in k_neq_r1.
          rewrite (stn_eq_or_neq_right k_neq_r1). simpl.
          rewrite (@rigmultx0 F).
          rewrite (@rigrunax1 F).
          rewrite (@riglunax1 F (s * _)%ring).
          rewrite (@rigrunax2 F).
          rewrite (@riglunax2 F).
          rewrite k_eq_r2.
          apply idpath.
        * exact k_neq_r1.
        * intros q q_neq_k q_neq_k'.
          unfold identity_matrix.
          apply issymm_natneq in q_neq_k.
          rewrite (stn_eq_or_neq_right q_neq_k).
          simpl.
          rewrite (@riglunax1 F).
          unfold const_vec.
          apply issymm_natneq in q_neq_k'.
          rewrite (stn_eq_or_neq_right q_neq_k').
          simpl.
          rewrite (@rigmultx0 F).
          apply (@rigmult0x F).
      + simpl.
        rewrite (@sum_id_pointwise_prod_unf F).
        apply idpath.
  Defined.

  (* For F at least *)
  Lemma scalar_mult_matrix_comm { n : nat } ( r : ⟦ n ⟧%stn ) ( s1 s2 : F ) :
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
      apply ringcomm2; reflexivity.
    - simpl.
      do 2 rewrite (@rigmultx0 F).
      reflexivity.
  Defined.

  Lemma scalar_mult_matrix_multiplicative { n : nat }
        ( r : ⟦ n ⟧%stn ) ( s1 s2 : F ) :
    ((make_scalar_mult_row_matrix s1 r ) ** (make_scalar_mult_row_matrix s2 r ))
   = (make_scalar_mult_row_matrix (s1 * s2)%ring r ).
  Proof.
    rewrite scalar_mult_mat_elementary.
    unfold gauss_scalar_mult_row.
    unfold make_scalar_mult_row_matrix.
    apply funextfun; intros i.
    apply funextfun; intros j.
    destruct (stn_eq_or_neq i j).
    2: { simpl.
         destruct (stn_eq_or_neq i r).
         - simpl. rewrite (@rigmultx0 F).
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

  Lemma fldmultinvlax {X: fld} (e : X) (ne : e != 0%ring) :
    (fldmultinv e ne * e)%ring = 1%ring.
  Proof.
    unfold fldmultinv.
    unfold fldmultinvpair.
    destruct (fldchoice _) as [? | contr_eq].
    2: { apply fromempty.
         rewrite contr_eq in ne.
         contradiction. }
    unfold multinvpair in m.
    unfold invpair in m.
    destruct m as [m1 m2].
    simpl.
    destruct m2 as [m2 m3].
    change (m1 * e)%ring with (m1 * e)%multmonoid.
    rewrite m2.
    reflexivity.
  Defined.

  Lemma fldmultinvrax {X: fld} (e : X) (ne : e != 0%ring) :
    (e * fldmultinv e ne)%ring = 1%ring.
  Proof.
    rewrite ringcomm2; apply fldmultinvlax.
  Defined.

  (* TODO : F should also be a general field, not short-hand for rationals specifically.
            This does not mandate any real change in any proofs ?*)
  Lemma scalar_mult_matrix_is_inv { n : nat } ( i : ⟦ n ⟧%stn ) ( s : F ) ( ne : s != 0%ring )
  : @matrix_inverse F n (make_scalar_mult_row_matrix s i).
  Proof.
    set (B :=  (make_scalar_mult_row_matrix (fldmultinv s ne) i)).
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
                rewrite id_mat_ii. simpl.
                apply (@fldmultinvlax F s ne).
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
          rewrite (@rigmultx0 F).
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

  Lemma add_row_matrix_additive
    { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : F ) (ne : r1 ≠ r2) :
    ((make_add_row_matrix r1 r2 s1 ) ** (make_add_row_matrix r1 r2 s2 ))
   = (make_add_row_matrix r1 r2 (s1 + s2)%ring).
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
    rewrite (@rigrdistr F).
    rewrite rigcomm1.
    rewrite (@rigassoc1 F).
    reflexivity.
  Defined.

  Lemma add_row_matrix_commutes { n : nat }
        ( r1 r2 : ⟦ n ⟧%stn ) ( s1 s2 : F ) (ne : r1 ≠ r2) :
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
    rewrite (@rigcomm1 F).
    reflexivity.
  Defined.

  Lemma add_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (r1_neq_r2 : r1 ≠ r2) ( s : F )
    (p' : n > 0):
    @matrix_inverse F n (make_add_row_matrix r1 r2 s).
  Proof.
    use tpair.
    {
      induction (stn_eq_or_neq r1 r2) as [contr_eq| ?].
      - rewrite contr_eq in r1_neq_r2. (contradiction (isirrefl_natneq _ r1_neq_r2)).
      - exact (make_add_row_matrix r1 r2 (- s)%ring).
    }
    assert (proof :
     ((make_add_row_matrix r1 r2 s)  ** (make_add_row_matrix r1 r2 (- s)%ring))
      = @identity_matrix F n).
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
        * rewrite (@two_pulse_function_sums_to_point_rig F n _ p' k r1).
          -- do 2 rewrite stn_eq_or_neq_refl. simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2).
             rewrite k_eq_l in *.
             rewrite k_eq_r2 in *.
             rewrite (stn_eq_or_neq_right r1_neq_r2'). simpl.
             rewrite (@rigmultx0 F); rewrite (@rigrunax1 F); rewrite (@riglunax2 F).
             rewrite stn_eq_or_neq_refl; simpl.
             rewrite stn_eq_or_neq_refl; simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2').
             rewrite (@rigmultx0 F); simpl; rewrite (@rigmultx0 F).
             do 2 rewrite (@rigrunax1 F).
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
             rewrite (@rigmultx0 F).
             apply idpath.
        *  rewrite (@two_pulse_function_sums_to_point_rig F n _ p' k r1).
           -- rewrite (stn_eq_or_neq_right r1_neq_r2); simpl.
              rewrite stn_eq_or_neq_refl. simpl.
              rewrite k_eq_r2 in *.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              rewrite stn_eq_or_neq_refl.
              simpl.
              rewrite (stn_eq_or_neq_right k_neq_l).
              rewrite (@rigmultx0 F); rewrite (@rigrunax1 F); rewrite (@riglunax2 F); rewrite (@riglunax1 F).
              unfold const_vec.
              rewrite stn_eq_or_neq_refl.
              apply issymm_natneq in r1_neq_r2'.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              destruct (stn_eq_or_neq r1 l) as [r1_eq_l | r1_neq_l].
              ++ simpl.
                 do 3 rewrite (@rigrunax2 F).
                 rewrite (@ringcomm1 F (- s)%ring) . (* Only place we mention F ? TODO don't? *)
                 rewrite (@riglunax1 F).
                 rewrite ringrinvax1.
                 apply idpath.
              ++ repeat rewrite (@rigmultx0 F).
                 rewrite (@rigrunax1 F).
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
              rewrite (@riglunax1 F).
              rewrite (@rigmultx0 F).
              rewrite (@rigmult0x F).
              apply idpath.
        * rewrite k_eq_l in *.
          rewrite (@pulse_function_sums_to_point_rig''  F n _  p' l).
          -- rewrite (stn_eq_or_neq_refl); simpl.
             rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
             rewrite (@riglunax2 F).
             rewrite (stn_eq_or_neq_refl); simpl.
             apply idpath.
          -- intros q l_neq_q; simpl.
             rewrite (stn_eq_or_neq_right l_neq_q); simpl.
             apply (@rigmult0x F).
        *  rewrite (@pulse_function_sums_to_point_rig''  F n _  p' l).
           { rewrite (stn_eq_or_neq_right k_neq_l); simpl. apply (@rigmult0x F). }
           intros q q_neq_j.
           destruct (stn_eq_or_neq k q) as [k_eq_q | k_neq_q]; simpl.
           -- rewrite k_eq_q in *.
              rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
              rewrite (stn_eq_or_neq_right k_neq_l); simpl.
              apply (@rigmultx0 F).
           -- apply (@rigmult0x F).
    }
    destruct (stn_eq_or_neq r1 r2) as [absurd | ?].
    { apply fromempty; rewrite absurd in r1_neq_r2.
      apply isirrefl_natneq in r1_neq_r2; contradiction. }
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
      = @identity_matrix F n.
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
    @matrix_inverse F n (make_gauss_switch_row_matrix n r1 r2).
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
