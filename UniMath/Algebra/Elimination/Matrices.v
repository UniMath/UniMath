 (** * Matrices

Some matrix background material for [Algebra.Elimination]

Author: Daniel @Skantz (September 2022)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.


Local Notation Σ := (iterop_fun rigunel1 op1).
Local Notation "A ** B" := (matrix_mult A B) (at level 80).
Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).

(** * Arbitrary types *)
(** Purely structural facts about matrices over arbitary types *)
Section Arbitrary_Types.

  Lemma weq_rowvec
    : ∏ X : UU, ∏ n : nat, Vector X n ≃ Matrix X 1 n.
  Proof.
    intros; apply weq_vector_1.
  Defined.

  Lemma row_vec_inj { X : rig } { n : nat } (v1 v2 : Vector X n)
    : row_vec v1 = row_vec v2 -> v1 = v2.
  Proof.
    intros H; apply (invmaponpathsweq (@weq_rowvec X n)  _ _ H).
  Defined.

  Lemma weq_colvec
    : ∏ X : UU, ∏ n : nat, weq (Vector X n) (Matrix X n 1).
  Proof.
    intros; apply weqffun, weq_vector_1.
  Defined.

  Lemma col_vec_inj { X : rig } { n : nat } (v1 v2 : Vector X n)
    : col_vec v1 = col_vec v2 -> v1 = v2.
  Proof.
    intros H; apply (invmaponpathsweq (@weq_colvec X n)  _ _ H).
  Defined.

  Lemma col_vec_inj_pointwise { X : rig } { n : nat } (v1 v2 : Vector X n)
    : forall i : (stn n), (col_vec v1 i) = (col_vec v2 i) -> (v1 i) = (v2 i).
  Proof.
    intros i eq; apply (invmaponpathsweq (@weq_vector_1 X)  _ _ eq).
  Defined.

  Lemma col_vec_eq {X : UU} {n : nat} (v : Vector X n)
  : ∏ i : (stn 1), v = col (col_vec v) i.
  Proof.
    easy.
  Defined.

End Arbitrary_Types.

(* Matrix algebra facts that hold over an arbitrary rig,
   not yet assumed commutative. *)

Section General_Rigs.

Context {R : rig}.

Section General.

  Definition matrix_mult_unf  {m n : nat} (mat1 : Matrix R m n)
    {p : nat} (mat2 : Matrix R n p) : (Matrix R m p) :=
    λ i j, Σ (λ k, (mat1 i k * mat2 k j))%rig.

  Lemma matrix_mult_eq {m n : nat} (mat1 : Matrix R m n)
    {p : nat} (mat2 : Matrix R n p) :
    matrix_mult mat1 mat2 = matrix_mult_unf mat1 mat2.
  Proof.
    reflexivity.
  Defined.

  Definition matrix_add
  {m n : nat}
  (mat1 : Matrix R m n)
  (mat2 : Matrix R m n)
  : (Matrix R m n) :=
    entrywise _ _ op1 mat1 mat2.

  Lemma matrix_add_comm:
  ∏ {m n : nat} (mat1 : Matrix R m n)
                (mat2 : Matrix R m n),
  matrix_add mat1 mat2 = matrix_add mat2 mat1.
  Proof.
    intros.   apply funextfun.
    intros i. apply funextfun.
    intros j. apply rigcomm1.
  Defined.

  Lemma matrix_add_assoc:
  ∏ {m n : nat} (mat1 : Matrix R m n)
  (mat2 : Matrix R m n) (mat3 : Matrix R m n),
    matrix_add (matrix_add mat1 mat2) mat3
  = matrix_add mat1 (matrix_add mat2 mat3).
  Proof.
    intros.   apply funextfun.
    intros i. apply funextfun.
    intros j. apply rigassoc1.
  Defined.

  Lemma matrix_mult_assoc :
    ∏ {m n : nat} (mat1 : Matrix R m n)
      {p : nat} (mat2 : Matrix R n p)
      {q : nat} (mat3 : Matrix R p q),
    ((mat1 ** mat2) ** mat3) = (mat1 ** (mat2 ** mat3)).
  Proof.
    intros; unfold matrix_mult.
    apply funextfun; intro i; apply funextfun; intro j.
    etrans.
    2: { symmetry.
         apply maponpaths, funextfun. intros k.
         apply vecsum_ldistr. }
    etrans.
      { apply maponpaths. apply funextfun. intros k.
        apply vecsum_rdistr. }
    rewrite vecsum_interchange.
    apply maponpaths, funextfun; intros k.
    apply maponpaths, funextfun; intros l.
    apply rigassoc2.
  Defined.

  Local Notation "A ++' B" := (matrix_add A B) (at level 80).

  Lemma matrix_mult_ldistr :
    ∏ (m n : nat) (mat1 : Matrix R m n)
      (p : nat) (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R n p),
    ((mat1 ** (mat2 ++' mat3))) = ((mat1 ** mat2) ++' (mat1 ** mat3)).
  Proof.
    intros.
    rewrite matrix_mult_eq.
    unfold matrix_mult_unf, matrix_add
    , entrywise, pointwise.
    apply funextfun. intros i.
    apply funextfun. intros j.
    etrans. {
      apply maponpaths, funextfun; intros k.
      rewrite rigldistr; apply idpath.
    }
    apply vecsum_add.
  Defined.

  Lemma matrix_mult_rdistr :
    ∏ (m n p: nat) (mat1 : Matrix R n p)
      (mat2 : Matrix R n p)
      (q : nat) (mat3 : Matrix R p q),
    ((mat1 ++' mat2) ** mat3) = ((mat1 ** mat3) ++' (mat2 ** mat3)).
  Proof.
    intros.
    rewrite matrix_mult_eq.
    unfold matrix_mult_unf, matrix_add.
    unfold entrywise, pointwise.
    apply funextfun. intros i.
    apply funextfun. intros j.
    etrans. {
      apply maponpaths, funextfun; intros k.
      rewrite rigrdistr.
      exact (idpath _).
    }
    apply vecsum_add.
  Defined.


  Lemma matrix_mult_zero_vec_eq {m n : nat} {mat : Matrix R m n}
  : (@matrix_mult R _ _ mat _
    (col_vec (const_vec (@rigunel1 R))))
      = (col_vec (const_vec (@rigunel1 R))).
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    apply funextfun; intros i.
    unfold col_vec.
    apply funextfun; intros _.
    apply vecsum_eq_zero.
    intros k.
    apply rigmultx0.
  Defined.

End General.

Section Transposition.

  Definition transpose_transpose {X : UU} {m n : nat} (mat : Matrix X m n)
    : transpose (transpose mat) = mat.
  Proof. easy. Defined.

  Lemma transpose_inj {X : UU} {m n : nat} (mat1 mat2 : Matrix X m n):
    transpose mat1 = transpose mat2 -> mat1 = mat2.
  Proof.
    intros H; exact (invmaponpathsweq (make_weq _ (isweq_flipsec)) _ _ H).
  Defined.

  Lemma col_inj {X : UU} (m n : nat) (mat1 mat2 : Matrix X m n)
    : (∏ i : (stn n), col mat1 i = col mat2 i) -> mat1 = mat2.
  Proof.
    intro H. apply funextfun; intro i; apply funextfun; intro j.
    specialize (H j). apply toforallpaths in H. apply H.
  Defined.

  (* Note: probably switch direction, for consistency *)
  Definition is_symmetric_mat {X : UU} {n : nat} (mat : Matrix X n n)
    := mat = transpose mat.

  Lemma symmetric_mat_row_eq_col {X : UU} {n : nat} (mat : Matrix X n n)
        (i : ⟦ n ⟧%stn)
    : is_symmetric_mat mat -> row mat i = col mat i.
  Proof.
    intros issymm_mat. unfold col.
    rewrite <- issymm_mat. apply idpath.
  Defined.

  Lemma identity_matrix_symmetric  {n : nat}
    : is_symmetric_mat (@identity_matrix R n).
  Proof.
    unfold is_symmetric_mat.
    apply funextfun. intros i.
    apply funextfun. intros j.
    unfold identity_matrix, transpose, flip.
    apply stn_eq_or_neq_symm_nondep.
  Defined.

End Transposition.

Section Identity_Matrix.

  Definition id_row_stdb_vector {n} (i : ⟦n⟧%stn)
    : row (@identity_matrix R n) i = stdb_vector i.
  Proof. easy. Defined.

  Definition id_col_stdb_vector {n} (i : ⟦n⟧%stn)
    : col (@identity_matrix R n) i = stdb_vector i.
  Proof.
    apply funextfun; intros j.
    apply stn_eq_or_neq_symm_nondep.
  Defined.

  Lemma id_mat_row_is_pf { n : nat } (r : ⟦ n ⟧%stn)
    : is_pulse_function r (row (@identity_matrix R n) r).
  Proof.
    apply is_pulse_function_stdb_vector.
  Defined.

  Lemma id_pointwise_prod { n : nat } (v : Vector R n) (i : ⟦ n ⟧%stn)
    : (@identity_matrix R n i) *pw v
      = (@scalar_lmult_vec R (v i) n (identity_matrix i)).
  Proof.
    unfold identity_matrix, scalar_lmult_vec, pointwise, vector_fmap.
    apply funextfun. intros k.
    destruct (stn_eq_or_neq i k) as [eq | neq].
    - now rewrite riglunax2, rigrunax2, eq.
    - now rewrite rigmultx0, rigmult0x.
  Defined.

  Lemma sum_id_pointwise_prod { n : nat } (v : Vector R n) (i : ⟦ n ⟧%stn) :
    Σ ((identity_matrix i) *pw v) = (v i).
  Proof.
    apply sum_stdb_vector_pointwise_prod.
  Defined.

  Definition matlunel2 (n : nat) := @identity_matrix R n.
  Definition matrunel2 (n : nat) := @identity_matrix R n.

  Lemma matlunax2 : ∏ (m n: nat) (mat : Matrix R n m),
    (identity_matrix ** mat) = mat.
  Proof.
    intros.
    apply funextfun. intros i.
    apply funextfun. intros j.
    unfold matrix_mult, row.
    use sum_id_pointwise_prod.
  Defined.

  Lemma col_vec_mult_eq
    { m n : nat } (mat : Matrix R m n) (v1 : Vector R n) (v2 : Vector R m)
    (e : (mat ** (col_vec v1)) = col_vec v2)
    : ∏ i : (stn m),
    Σ ((mat i) *pw v1) = v2 i.
  Proof.
    now apply toforallpaths; use col_vec_inj.
  Defined.

  Lemma idmat_i_to_idvec {n : nat} (i : ⟦ n ⟧%stn)
    : (@identity_matrix R) i = (@stdb_vector R i).
  Proof.
    apply funextfun. intros j.
    apply funextfun. intros k.
    now destruct (stn_eq_or_neq j k).
  Defined.

  Lemma id_mat_ii {n : nat} (i : ⟦ n ⟧%stn)
     : (@identity_matrix R n) i i = rigunel2.
  Proof.
    unfold identity_matrix;
    now rewrite (stn_eq_or_neq_refl).
  Defined.

  Lemma id_mat_ij {n : nat} (i j : ⟦ n ⟧%stn)
    : i ≠ j -> (@identity_matrix R n) i j = rigunel1.
  Proof.
    intros i_neq_j.
    unfold identity_matrix.
    now rewrite (stn_eq_or_neq_right i_neq_j).
  Defined.

  Lemma matrunax2 : ∏ (m n : nat) (mat : Matrix R m n),
    (mat ** identity_matrix) = mat.
  Proof.
    intros m n mat.
    apply funextfun. intros i.
    apply funextfun. intros j.
    unfold matrix_mult.
    rewrite (pulse_function_sums_to_point _ j);
    rewrite <- (symmetric_mat_row_eq_col _ _ identity_matrix_symmetric);
    unfold pointwise, row.
    - now rewrite id_mat_ii, rigrunax2.
    - intros k j_neq_k;
      now rewrite (id_mat_ij _ _ j_neq_k), rigmultx0.
  Defined.

  Lemma identity_matrix_unique_left {m : nat}
    (Z : Matrix R m m)
    : (∏ n : nat, ∏ A : (Matrix R m n),
      (Z ** A) = A)
    -> Z = identity_matrix.
  Proof.
    intros impl.
    etrans. { apply pathsinv0, matrunax2. }
    apply impl.
  Defined.

  Lemma identity_matrix_unique_right {n : nat}
    (Z : Matrix R n n)
    : (∏ m : nat, ∏ A : (Matrix R m n),
      (A ** Z) = A)
    -> Z = identity_matrix.
  Proof.
    intros impl.
    etrans. { apply pathsinv0, matlunax2. }
    apply impl.
  Defined.

  Lemma idrow_sums_to_1 { n : nat } (i : ⟦ n ⟧%stn) :
    Σ ((@identity_matrix R n ) i) = 1%rig.
  Proof.
    apply stdb_vector_sums_to_1.
  Defined.

End Identity_Matrix.

Section Inverses.

  Definition matrix_right_inverse {m n : nat} (A : Matrix R m n) :=
    ∑ (B : Matrix R n m), ((A ** B) = identity_matrix).

  Definition matrix_left_inverse {m n : nat} (A : Matrix R m n) :=
    ∑ (B : Matrix R n m), ((B ** A) = identity_matrix).

  Definition matrix_inverse {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n),
      ((A ** B) = identity_matrix)
    × ((B ** A) = identity_matrix).

  Lemma matrix_inverse_to_right_and_left_inverse
    {n : nat} (A : Matrix R n n)
    : (matrix_inverse A)
      -> matrix_left_inverse A × matrix_right_inverse A.
  Proof.
    intros inv.
    destruct inv as [inv isinv].
    split; exists inv.
    - exact (pr2 isinv).
    - exact (pr1 isinv).
  Defined.

  Lemma make_matrix_left_inverse
    {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix)
    : matrix_left_inverse B.
  Proof.
    now exists A.
  Defined.

  Lemma make_matrix_right_inverse
    {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix)
    : matrix_right_inverse A.
  Proof.
    now exists B.
  Defined.

  Lemma matrix_left_inverse_equals_right_inverse
  {m n k: nat} (A : Matrix R n n)
  (lft : matrix_left_inverse A) (rght : matrix_right_inverse A)
  : pr1 lft = pr1 rght.
  Proof.
    destruct lft as [? islft].
    destruct rght as [rght isrght]; simpl.
    pose (H0 := matlunax2 n n rght).
    now rewrite <- islft, matrix_mult_assoc, isrght, matrunax2 in H0.
  Defined.

  Lemma matrix_right_left_inverse_to_inverse
    {n : nat} (A : Matrix R n n)
    : matrix_left_inverse A -> matrix_right_inverse A -> (matrix_inverse A).
  Proof.
    intros lft rght.
    use tpair; simpl. {apply lft. }
    split. 2: {apply lft. }
    pose (H0 := @matrix_left_inverse_equals_right_inverse n _ n _ lft rght).
    rewrite H0; apply rght.
  Defined.

  Lemma matrix_inverse_unique {n : nat} (A : Matrix R n n)
    (B C : matrix_inverse A) : pr1 B = pr1 C.
  Proof.
    assert (eq : pr1 B = ((pr1 B) ** (A ** (pr1 C)))).
    { rewrite (pr1 (pr2 C)).
      now rewrite matrunax2. }
    rewrite eq, <- matrix_mult_assoc, (pr2 (pr2 B)).
    now rewrite matlunax2.
  Defined.

  Lemma left_inv_matrix_prod_is_left_inv {m n : nat} (A : Matrix R m n)
    (A' : Matrix R n n) (pa : matrix_left_inverse A) (pb : matrix_left_inverse A') :
    (matrix_left_inverse (A ** A')).
  Proof.
    intros.
    exists ((pr1 pb) ** (pr1 pa)); simpl.
    rewrite matrix_mult_assoc, <- (matrix_mult_assoc _ A _).
    now rewrite (pr2 pa), matlunax2, (pr2 pb).
  Defined.

  Lemma right_inv_matrix_prod_is_right_inv {m n : nat} (A : Matrix R m n)
    (A' : Matrix R n n) (pa : matrix_right_inverse A) (pb : matrix_right_inverse A') :
    (matrix_right_inverse (A ** A')).
  Proof.
    intros.
    use tpair; simpl. { exact ((pr1 pb) ** (pr1 pa)). }
    rewrite matrix_mult_assoc,
    <- (matrix_mult_assoc _ (pr1 pb) _).
    now rewrite (pr2 pb), matlunax2, (pr2 pa).
  Defined.

  Lemma inv_matrix_prod_invertible {n : nat} (A : Matrix R n n)
    (A' : Matrix R n n) (pa : matrix_inverse A) (pb : matrix_inverse A') :
    (matrix_inverse (A ** A')).
  Proof.
    use tpair; simpl. { exact ((pr1 pb) ** (pr1 pa)). }
    use tpair.
    - rewrite matrix_mult_assoc.
      rewrite <- (matrix_mult_assoc _ (pr1 pb) _).
      rewrite (pr1 (pr2 pb)), matlunax2.
      now rewrite (pr1 (pr2 pa)).
    - simpl; rewrite matrix_mult_assoc.
      now rewrite <- (matrix_mult_assoc _ A _),
      (pr2 (pr2 pa)), matlunax2, (pr2 (pr2 pb)).
  Defined.

  Lemma identity_matrix_invertible { n : nat } : matrix_inverse (@identity_matrix _ n).
  Proof.
    exists identity_matrix.
    use tpair; apply matrunax2.
  Defined.

End Inverses.

Section Nil_Matrices.

  Lemma iscontr_nil_row_matrix {X : UU} {n : nat} : iscontr (Matrix X 0 n).
  Proof.
    apply iscontr_nil_vector.
  Defined.

  Lemma iscontr_nil_col_matrix {X : UU} {m : nat} : iscontr (Matrix X m 0).
  Proof.
    apply impred_iscontr; intro; apply iscontr_nil_vector.
  Defined.

  Lemma nil_matrix_invertible {n : nat} (A : Matrix R 0 0): matrix_inverse A.
  Proof.
    exists identity_matrix.
    use tpair;
      rewrite matrunax2; apply funextfun; intros i;
      apply (@iscontr_nil_row_matrix _ 0); assumption.
  Defined.

End Nil_Matrices.

Section Diagonal.

  Definition diagonal_sq { n : nat } (mat : Matrix R n n) :=
    λ i : (stn n), mat i i.

  Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn), (stntonat _ i ≠ (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition diagonal_all_nonzero { n : nat } (mat : Matrix R n n) :=
    ∏ i : ⟦ n ⟧%stn, mat i i != 0%rig.

End Diagonal.

Section Triangular.

  Definition is_upper_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i > (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_lower_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ), (stntonat _ i < (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_upper_triangular_partial { m n k : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i > (stntonat _ j)) -> i < k -> (mat i j) = 0%rig.

  Lemma upper_triangular_iff_transpose_lower_triangular
  { m n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix R m n)
  : is_upper_triangular mat
  <-> is_lower_triangular (transpose mat).
  Proof.
    unfold  is_upper_triangular, is_lower_triangular, transpose, flip.
    split.
    - intros inv i j i_lt_j.
      rewrite inv; try assumption; reflexivity.
    - intros inv i j i_gt_j.
      rewrite inv; try assumption; reflexivity.
  Defined.

End Triangular.

Section Misc.

  Definition ij_minor {X : rig} {n : nat} ( i j : ⟦ S n ⟧%stn )
    (mat : Matrix X (S n) (S n)) : Matrix X n n.
  Proof.
    intros i' j'.
    exact (mat (dni i i') (dni j j')).
  Defined.

  Lemma zero_row_product { m n p : nat }
      (A : Matrix R m n) (B : Matrix R n p)
      (i : ⟦m⟧%stn) (Ai_zero : row A i = const_vec 0%rig)
    : row (A ** B) i = const_vec 0%rig.
  Proof.
    apply toforallpaths in Ai_zero.
    apply funextfun; intro k.
    apply vecsum_eq_zero.
    intro j; unfold pointwise.
    etrans. { apply maponpaths_2, Ai_zero. }
    apply rigmult0x.
  Defined.

End Misc.

End General_Rigs.

Section MatricesCommrig.

  Lemma row_vec_col_vec_mult_eq
  { n : nat } {CR: commrig}
  (A : Matrix CR n n)
  : ∏ x, transpose (matrix_mult (row_vec x) (transpose A))
  = (matrix_mult A (col_vec x)).
  Proof.
    intros; unfold transpose, flip, row_vec, col_vec, row, col; intros.
    do 2 (rewrite (matrix_mult_eq); unfold matrix_mult_unf).
    assert (eq: ∏ x0 : (stn n),
             Σ (λ k : (⟦ n ⟧)%stn, (x k * A x0 k)%rig)
             = Σ (λ k : (⟦ n ⟧)%stn, (A x0 k * x k )%rig)).
    { intro. apply vecsum_eq.
      intro. apply rigcomm2. }
    assert (f_eq : ∏ f g: (stn n) -> (stn 1) -> CR,
      (∏ i : (stn n), ∏ j : (stn 1), f i j = g i j) -> f = g).
    { intros f g. intros H. apply funextfun; intros i.
      apply funextfun; intros j. apply H. }
    apply f_eq; intros i j; apply eq.
  Defined.

End MatricesCommrig.

  (* Note: Some material can be moved to semirings section above *)
Section MatricesFld.

  Context {F : fld}.
  Local Notation Σ := (iterop_fun 0%ring op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2).

  Lemma matrix_product_transpose
  { m n k : nat } (A : Matrix F m n) (B : Matrix F n k)
  : (transpose (A ** B)) = ((transpose B) ** (transpose A)).
  Proof.
    intros.
    unfold transpose, flip.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    symmetry; rewrite matrix_mult_eq; unfold matrix_mult_unf.
    apply funextfun. intros i.
    apply funextfun. intros j.
    etrans. {apply maponpaths. apply funextfun.
      intros ?. rewrite ringcomm2. reflexivity. }
    reflexivity.
  Defined.

  Lemma invertible_to_transpose_invertible
    { n : nat } (mat : Matrix F n n)
    : (@matrix_inverse F n mat)
    -> (@matrix_inverse F n (transpose mat)).
  Proof.
    intros [mat_inv [e_mi e_im]].
    exists (transpose mat_inv).
    split;
      refine (!(identity_matrix_symmetric
                  @ maponpaths _ (!_)
                  @ matrix_product_transpose _ _));
      assumption.
  Defined.

  Lemma transpose_invertible_to_invertible { n : nat } (mat : Matrix F n n)
    : (@matrix_inverse F n (transpose mat))
  -> (@matrix_inverse F n mat).
  Proof.
    intros; rewrite <- transpose_transpose.
    now apply invertible_to_transpose_invertible.
  Defined.

  Lemma matrix_left_inverse_to_transpose_right_inverse
    {m n : nat} (A : Matrix F m n)
    (inv: @matrix_left_inverse F m n A)
    : (@matrix_right_inverse F n m (@transpose F n m A)).
  Proof.
    destruct inv as [inv isinv].
    exists (transpose inv).
    etrans. { apply pathsinv0, matrix_product_transpose. }
    etrans. { apply maponpaths, isinv. }
    apply pathsinv0, identity_matrix_symmetric.
  Defined.

  Lemma zero_row_to_non_right_invertibility { m n : nat } (A : Matrix F m n)
      (i : ⟦ m ⟧%stn) (zero_row : A i = (const_vec 0%ring))
    : (@matrix_right_inverse F m n A) -> empty.
  Proof.
    intros [inv isrightinv].
    contradiction (@nonzeroax F).
    etrans. { apply pathsinv0, (@id_mat_ii F). }
    do 2 (apply toforallpaths in isrightinv; specialize (isrightinv i)).
    etrans. { apply pathsinv0, isrightinv. }
    refine (toforallpaths _ _ _ _ i).
    apply (@zero_row_product F).
    apply zero_row.
  Defined.

  Lemma zero_row_to_non_invertibility { n : nat } (A : Matrix F n n)
    (i : ⟦ n ⟧%stn) (zero_row : A i = (const_vec 0%ring)) :
    (@matrix_inverse F n A) -> empty.
  Proof.
    intros invA.
    apply matrix_inverse_to_right_and_left_inverse in invA.
    destruct invA as [? rinvA].
    apply (zero_row_to_non_right_invertibility A i); assumption.
  Defined.

  Lemma diagonal_nonzero_iff_transpose_nonzero
    { n : nat } (A : Matrix F n n)
    : @diagonal_all_nonzero F n A
    <-> (@diagonal_all_nonzero F n (transpose A)).
  Proof.
    split ; intros H; unfold diagonal_all_nonzero, transpose, flip; apply H.
  Defined.

  Lemma upper_triangular_transpose_is_lower_triangular
    { m n : nat } (A : Matrix F m n)
    (H: @is_upper_triangular F m n A)
    : (@is_lower_triangular F n m (transpose A)).
  Proof.
    intros i j lt; unfold is_upper_triangular; now apply H.
  Defined.

End MatricesFld.

Section Transpositions.

  Context { R : rig }.

  Definition transposition_fun {n : nat} (i j : ⟦ n ⟧%stn)
    : ⟦ n ⟧%stn -> ⟦ n ⟧%stn.
  Proof.
    intros k.
    destruct (stn_eq_or_neq i k).
    - exact j.
    - destruct (stn_eq_or_neq j k).
      + exact i.
      + exact k.
  Defined.

  Definition transposition_self_inverse {n} (i j : ⟦ n ⟧%stn)
    : transposition_fun i j ∘ transposition_fun i j = idfun _.
  Proof.
    apply funextsec; intros k; simpl; unfold transposition_fun.
    destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k];
      destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
    - now destruct i_eq_j.
    - now rewrite stn_eq_or_neq_refl.
    - destruct i_eq_j.
      do 2 rewrite (stn_eq_or_neq_right i_neq_k).
      reflexivity.
    - destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
      + now rewrite stn_eq_or_neq_refl.
      + rewrite (stn_eq_or_neq_right i_neq_k).
        rewrite (stn_eq_or_neq_right j_neq_k).
        reflexivity.
  Defined.

  Definition transposition_perm {n : nat} (i j : ⟦ n ⟧%stn)
    : ⟦ n ⟧%stn ≃ ⟦ n ⟧%stn.
  Proof.
    exists (transposition_fun i j).
    use isweq_iso.
    - exact (transposition_fun i j).
    - apply toforallpaths, transposition_self_inverse.
    - apply toforallpaths, transposition_self_inverse.
  Defined.

  (* Note: can be generalize to functions on rows? *)
  Definition transposition_mat_rows {X : UU} {m n : nat} (i j : ⟦ m ⟧%stn)
    : (Matrix X m n) -> Matrix X m n.
  Proof.
    intros mat k.
    destruct (stn_eq_or_neq i k).
    - apply (mat j).
    - destruct (stn_eq_or_neq j k).
      + exact (mat i).
      + exact (mat k).
  Defined.

  Definition tranposition_mat_rows_perm_stmt {X : UU} {m n : nat} (i j : ⟦ m ⟧%stn)
    := (Matrix X m n) ≃ Matrix X m n.
  (* Proof. (* This is just the switch_rows proof *)   Abort.*)

  Definition is_permutation_fun {n : nat} (p : ⟦ n ⟧%stn -> ⟦ n ⟧%stn) :=
    ∏ i j: ⟦ n ⟧%stn, (p i = p j) -> i = j.

  Definition id_permutation_fun (n : nat) : ⟦ n ⟧%stn -> ⟦ n ⟧%stn :=
    λ i : ⟦ n ⟧%stn, i.

  Lemma idp_is_permutation_fun {n : nat} : is_permutation_fun (id_permutation_fun n).
  Proof.
    unfold is_permutation_fun, id_permutation_fun.
    intros; assumption.
  Defined.

End Transpositions.
