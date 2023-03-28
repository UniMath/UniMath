(** * Matrices

Elementary row operations on matrices, for elimination procedures

Primary Author: Daniel @Skantz (November 2022)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.Algebra.GaussianElimination.Auxiliary.
Require Import UniMath.Algebra.GaussianElimination.Vectors.

Require Import UniMath.Algebra.GaussianElimination.Matrices.


(** This file defines the traditional elementary row operations on matrices over a ring, as used in Gaussian elimination and related procedures:
  - addition of a multiple of a row to another row;
  - interchange of two rows;
  - multiplication of a row by a nonzero scalar.

  For each operation, we describe its action on matrices directly,
  and also equivalently as left multiplication by an elementary matrix.

  We further show that these elementary matrices are invertible (with inverses just the elementary matrices corresponding to inverse row operations).

  Hopefully the material can be easily re-used for column operations too. *)


Local Notation Σ := (iterop_fun 0%rig op1).
Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).
Local Notation "R1 +pw R2" := ((pointwise _ op1) R1 R2) (at level 50, left associativity).
Local Notation "A ** B" := (@matrix_mult _ _ _ A _ B) (at level 40, left associativity).
Local Notation "A **' B" := (@matrix_mult (_:ring) _ _ A _ B) (at level 40, left associativity).
(* second notation is needed since [pr1ring] being a coercion means the inferred coercions to [setwithbinop] from [ring] and further structures factor syntactically through [ring] but NOT always [rig] *)

Section Add_Row.

  Context { R : ring }.

  Definition add_row_mult
    { m n } (r1 r2 : ⟦ m ⟧%stn) (s : R) (mat : Matrix R m n)
    : ( Matrix R m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r2).
    - exact ((mat r2 j) + (s * (mat r1 j)))%rig.
    - exact (mat i j).
  Defined.
(* Note: There’s a tradeoff here (and similarly in other row-operations) between doing the case-split before or after introducing [j].  Putting the case-split first allows defining the rows as linear combinations of vectors, providing useful abstractions in some calculations later, but means the function isn’t in canonical form, which obstructs pointwise calculations. *)

  (** Basic properties of [add_row_mult] *)
  Lemma add_row_mult_nontarget_row
      {m n} (r1 r2 : ⟦ m ⟧%stn) (s : R) (mat : Matrix R m n)
    : ∏ (i : ⟦ m ⟧%stn), r2 ≠ i -> add_row_mult r1 r2 s mat i = mat i.
  Proof.
    intros i r2_ne_i.
    unfold add_row_mult.
    now rewrite (stn_eq_or_neq_right (issymm_stnneq r2_ne_i)).
  Defined.

  Definition add_row_mult_target_row
      {m n} (r1 r2 : ⟦ m ⟧%stn) (s : R) (mat : Matrix R m n)
      (c : ⟦ n ⟧%stn)
    : (add_row_mult r1 r2 s mat) r2 c = (mat r2 c + s * mat r1 c)%rig.
  Proof.
    unfold add_row_mult.
    now rewrite stn_eq_or_neq_refl.
  Defined.

  (** The add-a-row-multiple operation as a matrix *)

  Definition add_row_mult_matrix
    { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : R)
    : Matrix R n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - refine ((@stdb_vector R _ i) +pw
        (@scalar_lmult_vec R s _ (@stdb_vector R _ r1))).
    - refine (@stdb_vector R _ i).
  Defined.

  Lemma add_row_mult_as_matrix
    { m n } (r1 r2 : ⟦ m ⟧%stn) (ne : r1 ≠ r2) (s : R) (mat : Matrix R m n)
    : (add_row_mult_matrix r1 r2 s) **' mat = add_row_mult r1 r2 s mat.
  Proof.
    intros.
    apply funextfun; intros i; apply funextfun; intros j.
    unfold matrix_mult, add_row_mult_matrix, add_row_mult, col, row.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2]; simpl coprod_rect.
    - etrans. { apply maponpaths, (@pointwise_rdistr_vector R). }
      etrans. { apply vecsum_add. }
      apply map_on_two_paths.
      + etrans. 2: { apply maponpaths_2, i_eq_r2. }
        use sum_stdb_vector_pointwise_prod.
      + etrans. { apply vecsum_scalar_lmult. }
        apply maponpaths, @sum_stdb_vector_pointwise_prod.
    - use sum_stdb_vector_pointwise_prod.
  Defined.

  Lemma add_row_mult_matrix_sum
    { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (ne : r1 ≠ r2) ( s1 s2 : R ) :
    ((add_row_mult_matrix r1 r2 s1 ) **' (add_row_mult_matrix r1 r2 s2))
   = (add_row_mult_matrix r1 r2 (s1 + s2)%ring).
  Proof.
    rewrite add_row_mult_as_matrix; try assumption.
    apply funextfun; intros i; apply funextfun; intros j.
    unfold add_row_mult, add_row_mult_matrix.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    2: {apply idpath. }
    destruct i_eq_r2.
    rewrite stn_eq_or_neq_refl, (stn_eq_or_neq_right ne); simpl.
    unfold scalar_lmult_vec, pointwise, vector_fmap.
    rewrite (@rigrdistr R), rigcomm1, (@rigassoc1 R).
    reflexivity.
  Defined.

  Lemma add_row_mult_matrix_zero
      { n } ( r1 r2 : ⟦ n ⟧%stn ) (ne : r1 ≠ r2)
    : add_row_mult_matrix r1 r2 (@rigunel1 R) = @identity_matrix R _.
  Proof.
    apply funextfun; intros i.
    unfold add_row_mult_matrix.
    destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    2: { apply idpath. }
    destruct i_eq_r2. simpl.
    apply funextfun; intros j.
    unfold scalar_lmult_vec, pointwise, vector_fmap.
    rewrite (@rigmult0x R).
    apply (@rigrunax1 R).
  Defined.

  Lemma add_row_mult_matrix_commutes
      {n} ( r1 r2 : ⟦ n ⟧%stn) (ne : r1 ≠ r2) ( s1 s2 : R )
    : ((add_row_mult_matrix r1 r2 s1 ) **' (add_row_mult_matrix r1 r2 s2 ))
    = ((add_row_mult_matrix r1 r2 s2 ) **' (add_row_mult_matrix r1 r2 s1 )).
  Proof.
    do 2 (rewrite add_row_mult_matrix_sum; try assumption).
    apply maponpaths, (@rigcomm1 R).
  Defined.

  Lemma add_row_mult_matrix_invertible
    { n } (r1 r2 : ⟦ n ⟧%stn) (ne : r1 ≠ r2) (s : R)
   : @matrix_inverse R n (add_row_mult_matrix r1 r2 s).
  Proof.
    exists (add_row_mult_matrix r1 r2 (- s)%ring).
    split;
      refine (add_row_mult_matrix_sum _ _ ne _ _ @ _);
      refine (_ @ add_row_mult_matrix_zero _ _ ne);
      apply maponpaths.
    - apply (@ringrinvax1 R).
    - apply (@ringlinvax1 R).
  Defined.

  (** Miscellaneous properties of [add_row_mult], used in [Algebra.GaussianElimination.Elimination] *)

  Lemma add_row_mult_source_row_zero
    {m n} (r1 r2 : ⟦ m ⟧%stn) (s : R) (mat : Matrix R m n)
    : mat r1 = const_vec 0%ring
      -> add_row_mult r1 r2 s mat = mat.
  Proof.
    intros eq0.
    apply funextfun; intros i'; apply funextfun; intros j'.
    unfold add_row_mult.
    destruct (stn_eq_or_neq _ _ ) as [i'_eq_j' | i'_neq_j'];
      simpl; try reflexivity.
    rewrite <- i'_eq_j', eq0.
    unfold const_vec ; simpl.
    rewrite (@rigmultx0 R).
    apply (@rigrunax1 R).
  Defined.

End Add_Row.

Section Mult_Row.

  Context { F : fld }.

  Definition scalar_mult_row
    { m n : nat} (r : ⟦ m ⟧%stn) (s : F) (mat : Matrix F m n)
    : Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%ring.
    - exact (mat i j).
  Defined.

  (** The multiply-row operation as a matrix *)
  Definition scalar_mult_row_matrix {n : nat}
      (r : ⟦ n ⟧%stn) (s : F)
    : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r).
    - exact (const_vec s *pw @stdb_vector F _ i).
    - exact (@stdb_vector F _ i).
  Defined.

  Lemma scalar_mult_as_matrix
    {m n : nat} (r : ⟦ m ⟧%stn) (s : F) (mat : Matrix F m n)
    : ((scalar_mult_row_matrix r s) **' mat) = scalar_mult_row r s mat.
  Proof.
    use funextfun; intros i; use funextfun; intros ?.
    unfold matrix_mult, scalar_mult_row_matrix, scalar_mult_row, row.
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

  Lemma scalar_mult_matrix_product
    { n } ( r : ⟦ n ⟧%stn ) ( s1 s2 : F )
    : ((scalar_mult_row_matrix r s1 ) **' (scalar_mult_row_matrix r s2 ))
      = (scalar_mult_row_matrix r (s1 * s2)%ring ).
  Proof.
    rewrite scalar_mult_as_matrix.
    unfold scalar_mult_row.
    unfold scalar_mult_row_matrix.
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
    : scalar_mult_row_matrix r (@rigunel2 F) = @identity_matrix F _.
  Proof.
    unfold scalar_mult_row_matrix.
    apply funextfun; intros i.
    destruct (stn_eq_or_neq i r); simpl coprod_rect.
    2: { reflexivity. }
    apply funextfun; intros j.
    apply (@riglunax2 F).
  Defined.

  Lemma scalar_mult_matrix_comm
    { n : nat } ( r : ⟦ n ⟧%stn ) ( s1 s2 : F )
    : ((scalar_mult_row_matrix r s1) **' (scalar_mult_row_matrix r s2))
    = ((scalar_mult_row_matrix r s2) **' (scalar_mult_row_matrix r s1)).
  Proof.
    do 2 rewrite scalar_mult_matrix_product.
    apply maponpaths, (rigcomm2 F).
  Defined.

  Lemma scalar_mult_matrix_invertible
    { n } ( i : ⟦ n ⟧%stn ) ( s : F ) ( ne : s != (@rigunel1 F))
  : @matrix_inverse F _ (scalar_mult_row_matrix i s).
  Proof.
    exists (scalar_mult_row_matrix i (fldmultinv s ne)).
    split;
      refine (scalar_mult_matrix_product _ _ _ @ _);
      refine (_ @ scalar_mult_matrix_one i);
      apply maponpaths.
    - apply fldmultinvrax; assumption.
    - apply fldmultinvlax; assumption.
  Defined.

End Mult_Row.

Section Switch_Row.

  Context { R : rig }.

  Definition switch_row
    {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
    : Matrix R m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact (mat r2 j).
    - induction (stn_eq_or_neq i r2).
      + exact (mat r1 j).
      + exact (mat i j).
  Defined.

  (** Basic properties of [switch_row] *)
  Lemma switch_row_former_row
      {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n) (j : ⟦n⟧%stn)
    : switch_row r1 r2 mat r1 j = mat r2 j.
  Proof.
    unfold switch_row. rewrite stn_eq_or_neq_refl; simpl.
    reflexivity.
  Defined.

  Lemma switch_row_latter_row
      {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n) (j : ⟦n⟧%stn)
    : switch_row r1 r2 mat r2 j = mat r1 j.
  Proof.
    unfold switch_row.
    rewrite stn_eq_or_neq_refl; simpl.
    destruct (stn_eq_or_neq r2 r1) as [ e | ? ];
      simpl; try destruct e; reflexivity.
  Defined.

  Lemma switch_row_other_row
      {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
      (i : ⟦ m ⟧%stn) (ne1 : i ≠ r1) (ne2 : i ≠ r2) (j : ⟦n⟧%stn)
    : switch_row r1 r2 mat i j = mat i j.
  Proof.
    unfold switch_row.
    rewrite (stn_eq_or_neq_right ne1), (stn_eq_or_neq_right ne2).
    simpl; reflexivity.
  Defined.

  Lemma switch_row_former_row'
      {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
      (i : ⟦m⟧%stn) (e : i = r1) (j : ⟦n⟧%stn)
    : switch_row r1 r2 mat i j = mat r2 j.
  Proof.
    destruct e; apply switch_row_former_row.
  Defined.

  Lemma switch_row_latter_row'
      {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
      (i : ⟦m⟧%stn) (e : i = r2) (j : ⟦n⟧%stn)
    : switch_row r1 r2 mat i j = mat r1 j.
  Proof.
    destruct e; apply switch_row_latter_row.
  Defined.

  Lemma switch_row_other_row'
    {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
    : ∏ (i : ⟦ m ⟧%stn), i ≠ r1 -> i ≠ r2
    -> (switch_row r1 r2 mat) i = mat i.
  Proof.
    intros i i_ne_r1 i_ne_r2.
    apply funextfun; intros j.
    apply switch_row_other_row; assumption.
  Defined.

  (** The switch-row operation as a matrix *)
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

  Lemma switch_row_as_matrix
    {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
    : ((switch_row_matrix r1 r2) ** mat) = switch_row r1 r2 mat.
  Proof.
    apply funextfun; intros i; apply funextfun; intros j.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold switch_row_matrix, switch_row.
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1];
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2];
      simpl;
      use sum_stdb_vector_pointwise_prod.
  Defined.

  Definition switch_row_involution
    {m n : nat} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
    : switch_row r1 r2 (switch_row r1 r2 mat) = mat.
  Proof.
    apply funextfun; intros i; apply funextfun; intros j.
    destruct (stn_eq_or_neq i r1) as [ e_i_r1 | ne_i_r1 ];
      [ | destruct (stn_eq_or_neq i r2) as [ e_i_r2 | ne_i_r2 ]].
    - destruct e_i_r1.
      etrans. { apply switch_row_former_row. }
      apply switch_row_latter_row.
    - destruct e_i_r2.
      etrans. { apply switch_row_latter_row. }
      apply switch_row_former_row.
    - etrans; apply switch_row_other_row; assumption.
  Defined.

  Lemma switch_row_matrix_involution
    { n : nat } ( r1 r2 : ⟦ n ⟧%stn )
    : ((switch_row_matrix r1 r2)
      ** (switch_row_matrix r1 r2))
      = @identity_matrix _ _.
  Proof.
    intros.
    rewrite switch_row_as_matrix.
    unfold switch_row, switch_row_matrix.
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

  (** Miscellaneous properties of [switch_row], used in [Algebra.GaussianElimination.Elimination] *)
  Lemma switch_row_equal_rows
    {m n} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
    : (mat r1) = (mat r2) -> (switch_row r1 r2 mat) = mat.
  Proof.
    intros m_eq.
    unfold switch_row.
    apply funextfun. intros i'.
    destruct (stn_eq_or_neq _ _) as [eq | neq].
    - destruct (stn_eq_or_neq _ _) as [eq' | neq'].
      + now apply maponpaths.
      + etrans. apply m_eq.
        now apply maponpaths.
    - destruct (stn_eq_or_neq _ _) as [eq | cec].
      + cbn. etrans. apply(!m_eq).
        apply maponpaths, (!eq).
      + apply idpath.
  Qed.

  Lemma switch_row_equal_entries
    {m n : nat} (r1 r2 : ⟦ m ⟧%stn) (mat : Matrix R m n)
    : ∏ (j : ⟦ n ⟧%stn), (mat r1 j) = (mat r2 j) ->
      ∏ (r3 : ⟦ m ⟧%stn), (switch_row r1 r2 mat) r3 j = mat r3 j.
  Proof.
    intros j m_eq r3.
    unfold switch_row.
    destruct (stn_eq_or_neq _ _) as [eq | neq].
    - destruct (stn_eq_or_neq _ _) as [eq' | neq']; cbn.
      + now apply maponpaths_2.
      + etrans. apply m_eq.
        now apply maponpaths_2.
    - destruct (stn_eq_or_neq _ _) as [eq | cec]; cbn.
      + etrans. apply(!m_eq).
        now apply maponpaths_2.
      + apply idpath.
  Qed.

End Switch_Row.
