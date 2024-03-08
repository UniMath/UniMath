 (** * Matrices

Some matrix background material for [Algebra.GaussianElimination]

Primary Author: Daniel @Skantz (November 2022)
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.Algebra.GaussianElimination.Auxiliary.
Require Import UniMath.Algebra.GaussianElimination.Vectors.


Local Notation Σ := (iterop_fun rigunel1 op1).
Local Notation "A ** B" := (matrix_mult A B) (at level 40, left associativity).
Local Notation "R1 *pw R2" := ((pointwise _ op2) R1 R2) (at level 40, left associativity).

(** * Arbitrary types *)
(** Purely structural facts about matrices over arbitary types *)
Section Arbitrary_Types.

Section Misc.
  Lemma col_inj {X : UU} (m n : nat) (mat1 mat2 : Matrix X m n)
    : (∏ i : (stn n), col mat1 i = col mat2 i) -> mat1 = mat2.
  Proof.
    intro H. apply funextfun; intro i; apply funextfun; intro j.
    specialize (H j). apply toforallpaths in H. apply H.
  Defined.
End Misc.

Section Vectors_as_Matrices.
  (** Vectors as column and row vectors *)
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

End Vectors_as_Matrices.

Section Transposition.

  Definition transpose_transpose {X : UU} {m n : nat} (mat : Matrix X m n)
    : transpose (transpose mat) = mat.
  Proof. easy. Defined.

  Lemma transpose_inj {X : UU} {m n : nat} (mat1 mat2 : Matrix X m n)
    : transpose mat1 = transpose mat2 -> mat1 = mat2.
  Proof.
    apply (maponpaths transpose).
  Defined.

  Definition is_symmetric_mat {X : UU} {n : nat} (mat : Matrix X n n)
    := transpose mat = mat.

  Lemma symmetric_mat_row_eq_col {X : UU} {n : nat} (mat : Matrix X n n)
        (i : ⟦ n ⟧%stn)
    : is_symmetric_mat mat -> row mat i = col mat i.
  Proof.
    intros H. unfold col, row.
    exact (toforallpaths _ _ _ (!H) i).
  Defined.

End Transposition.

End Arbitrary_Types.

(** * Arbitary rigs
  Matrix algebra facts that hold over an arbitrary rig, not yet assumed commutative. *)

Section General_Rigs.

Context {R : rig}.

Section General.

  Definition matrix_mult_unf {m n p} (mat1 : Matrix R m n) (mat2 : Matrix R n p)
    : Matrix R m p
  := λ i j, Σ (λ k, (mat1 i k * mat2 k j))%rig.

  Lemma matrix_mult_eq {m n p} (mat1 : Matrix R m n) (mat2 : Matrix R n p)
    : mat1 ** mat2 = matrix_mult_unf mat1 mat2.
  Proof.
    reflexivity.
  Defined.

  Definition matrix_add {m n} (mat1 : Matrix R m n) (mat2 : Matrix R m n)
    : Matrix R m n
  := entrywise _ _ op1 mat1 mat2.

  Local Notation "A ++' B" := (matrix_add A B) (at level 50, left associativity).

  Lemma matrix_add_comm {m n} (mat1 : Matrix R m n) (mat2 : Matrix R m n)
    : matrix_add mat1 mat2 = matrix_add mat2 mat1.
  Proof.
    apply entrywise_comm, rigcomm1.
  Defined.

  Lemma matrix_add_assoc {m n : nat}
      (mat1 : Matrix R m n) (mat2 : Matrix R m n) (mat3 : Matrix R m n)
    : matrix_add (matrix_add mat1 mat2) mat3
      = matrix_add mat1 (matrix_add mat2 mat3).
  Proof.
    apply entrywise_assoc, rigassoc1.
  Defined.

  Lemma matrix_mult_assoc {m n p q}
      (mat1 : Matrix R m n) (mat2 : Matrix R n p) (mat3 : Matrix R p q)
    : (mat1 ** mat2) ** mat3 = mat1 ** (mat2 ** mat3).
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

  Lemma matrix_mult_ldistr {m n p}
        (mat1 : Matrix R m n) (mat2 : Matrix R n p) (mat3 : Matrix R n p)
    : mat1 ** (mat2 ++' mat3) = (mat1 ** mat2) ++' (mat1 ** mat3).
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

  Lemma matrix_mult_rdistr {m n p}
        (mat1 : Matrix R m n) (mat2 : Matrix R m n) (mat3 : Matrix R n p)
    : (mat1 ++' mat2) ** mat3 = (mat1 ** mat3) ++' (mat2 ** mat3).
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
    : mat ** col_vec (const_vec 0%rig)
      = col_vec (const_vec 0%rig).
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

Section Identity_Matrix.

  Lemma identity_matrix_symmetric  {n : nat}
    : is_symmetric_mat (@identity_matrix R n).
  Proof.
    unfold is_symmetric_mat.
    apply funextfun. intros i.
    apply funextfun. intros j.
    unfold identity_matrix, transpose, flip.
    apply stn_eq_or_neq_symm_nondep.
  Defined.

  Definition id_row_stdb_vector {n} (i : ⟦n⟧%stn)
    : row (@identity_matrix R n) i = stdb_vector i.
  Proof. easy. Defined.

  Definition id_col_stdb_vector {n} (i : ⟦n⟧%stn)
    : col (@identity_matrix R n) i = stdb_vector i.
  Proof.
    apply funextfun; intros j.
    apply stn_eq_or_neq_symm_nondep.
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

  Definition matrix_left_inverse {m n : nat} (A : Matrix R m n) :=
    ∑ (B : Matrix R n m), ((B ** A) = identity_matrix).

  Definition matrix_right_inverse {m n : nat} (A : Matrix R m n) :=
    ∑ (B : Matrix R n m), ((A ** B) = identity_matrix).

  Definition matrix_inverse {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n),
      ((A ** B) = identity_matrix)
    × ((B ** A) = identity_matrix).

  #[reversible=no] Coercion matrix_left_inverse_of_inverse {n : nat}
    (A : Matrix R n n)
    : @matrix_inverse n A -> @matrix_left_inverse n n A.
  Proof.
    intros [y [xy yx]]. esplit; eauto.
  Defined.

  #[reversible=no] Coercion matrix_right_inverse_of_inverse {n : nat}
    (A : Matrix R n n)
    : @matrix_inverse n A -> @matrix_right_inverse n n A.
  Proof.
    intros [y [xy yx]]. esplit; eauto.
  Defined.

  Lemma matrix_inverse_to_right_and_left_inverse
    {n : nat} (A : Matrix R n n)
    : (matrix_inverse A)
      -> matrix_left_inverse A × matrix_right_inverse A.
  Proof.
    intros inv; split.
    - apply matrix_left_inverse_of_inverse; exact inv.
    - apply matrix_right_inverse_of_inverse; exact inv.
  Defined.

  Lemma make_matrix_left_inverse
    {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix)
    : matrix_left_inverse B.
  Proof. now exists A. Defined.

  Lemma make_matrix_right_inverse
    {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix)
    : matrix_right_inverse A.
  Proof. now exists B. Defined.

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
    rewrite (@matrix_left_inverse_equals_right_inverse n _ n _ lft rght).
    apply rght.
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
    use tpair.
    - etrans. apply matrunax2.
      apply funextfun; intro i.
      now apply(@iscontr_nil_row_matrix _ 0).
    - etrans. apply matlunax2.
      apply funextfun; intro.
      now apply (@iscontr_nil_row_matrix _ 0).
  Defined.

End Nil_Matrices.

Section Diagonal.

  Definition diagonal_sq { n : nat } (mat : Matrix R n n) :=
    λ i : (stn n), mat i i.

  Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn), (stntonat _ i ≠ (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition diagonal_all_nonzero { n : nat } (mat : Matrix R n n) :=
    ∏ i : ⟦ n ⟧%stn, mat i i != 0%rig.

  Lemma diagonal_nonzero_iff_transpose_nonzero
    { n : nat } (A : Matrix R n n)
    : diagonal_all_nonzero A
    <-> diagonal_all_nonzero (transpose A).
  Proof.
    split ; intros H; unfold diagonal_all_nonzero, transpose, flip; apply H.
  Defined.

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
  : is_upper_triangular mat <-> is_lower_triangular (transpose mat).
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

(** * Commutative rigs *)
Section MatricesCommrig.

  Context {CR : commrig }.

  Lemma matrix_product_transpose
      { m n p : nat } (A : Matrix CR m n) (B : Matrix CR n p)
    : (transpose (A ** B)) = ((transpose B) ** (transpose A)).
  Proof.
    intros.
    apply funextfun. intros i.
    apply funextfun. intros k.
    apply vecsum_eq. intros j.
    unfold col, row, pointwise, transpose, flip; cbn.
    apply rigcomm2.
  Defined.

  Lemma row_vec_col_vec_mult_eq {m n} (A : Matrix CR m n) (x : Vector CR n)
  : transpose ((row_vec x) ** (transpose A)) = A ** (col_vec x).
  Proof.
    etrans. { apply matrix_product_transpose. }
    apply idpath.
  Defined.

  Lemma invertible_to_transpose_invertible { n } (mat : Matrix CR n n)
    : (@matrix_inverse CR n mat)
    -> (@matrix_inverse CR n (transpose mat)).
  Proof.
    intros [mat_inv [e_mi e_im]].
    exists (transpose mat_inv).
    split;
      refine (!matrix_product_transpose _ _
               @ maponpaths _ _
               @ identity_matrix_symmetric);
      assumption.
  Defined.

  Lemma transpose_invertible_to_invertible { n } (mat : Matrix CR n n)
    : (@matrix_inverse CR n (transpose mat))
    -> (@matrix_inverse CR n mat).
  Proof.
    apply invertible_to_transpose_invertible.
  Defined.

  Lemma matrix_left_inverse_to_transpose_right_inverse
    {m n} (A : Matrix CR m n)
    (inv: @matrix_left_inverse CR m n A)
    : (@matrix_right_inverse CR n m (@transpose CR n m A)).
  Proof.
    destruct inv as [inv isinv].
    exists (transpose inv).
    etrans. { apply pathsinv0, matrix_product_transpose. }
    etrans. { apply maponpaths, isinv. }
    apply identity_matrix_symmetric.
  Defined.

End MatricesCommrig.

Section MatricesIntDom.

  Context {R : intdom}.

  (** Note: these results don’t really require that R is an integral domain, just that R is non-trivial. *)
  Lemma zero_row_to_non_right_invertibility { m n : nat } (A : Matrix R m n)
      (i : ⟦ m ⟧%stn) (zero_row : A i = (const_vec 0%ring))
    : (@matrix_right_inverse R m n A) -> empty.
  Proof.
    intros [inv isrightinv].
    contradiction (@nonzeroax R).
    etrans. { apply pathsinv0, (@id_mat_ii R). }
    do 2 (apply toforallpaths in isrightinv; specialize (isrightinv i)).
    etrans. { apply pathsinv0, isrightinv. }
    refine (toforallpaths _ _ _ _ i).
    apply (@zero_row_product R).
    apply zero_row.
  Defined.

  Lemma zero_row_to_non_invertibility { n : nat } (A : Matrix R n n)
    (i : ⟦ n ⟧%stn) (zero_row : A i = (const_vec 0%ring)) :
    (@matrix_inverse R n A) -> empty.
  Proof.
    intros invA.
    apply matrix_inverse_to_right_and_left_inverse in invA.
    destruct invA as [? rinvA].
    apply (zero_row_to_non_right_invertibility A i); assumption.
  Defined.

End MatricesIntDom.

(** * Matrices representing permutations *)
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
