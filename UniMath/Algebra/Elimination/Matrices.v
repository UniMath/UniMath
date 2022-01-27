 (** * Matrices

Some matrix background material for [Algebra.Elimination]

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

Require Import UniMath.RealNumbers.Prelim.

Section Matrices.

  Context {R : rig}.
  Local Notation Σ := (iterop_fun rigunel1 op1).
  Local Notation "A ** B" := (matrix_mult A B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Definition matlunel2 (n : nat) := @identity_matrix R n.
  Definition matrunel2 (n : nat) := @identity_matrix R n.


  Lemma matlunax2 : ∏ (n : nat) (mat : Matrix R n n),
    (identity_matrix ** mat) = mat.
  Proof.
    intros.
    apply funextfun. intros i.
    apply funextfun. intros j.
    - unfold matrix_mult, row, pointwise.
      assert (X: is_pulse_function i (λ i0 : (⟦ n ⟧)%stn, op2 (identity_matrix i i0) (col mat j i0))).
      { unfold is_pulse_function.

        intros k i_neq_k.
        unfold identity_matrix.
        destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k'].
        - rewrite i_eq_k in i_neq_k.
          apply isirrefl_natneq in i_neq_k.
          apply fromempty. assumption.
        - rewrite coprod_rect_compute_2.
          apply rigmult0x.
      }
      set (f :=  (λ i0 : (⟦ n ⟧)%stn, op2 (identity_matrix i i0) (col mat j i0)) ).
      unfold f.
      rewrite (pulse_function_sums_to_point_rig'' _ (stn_implies_ngt0 i) i X).
      unfold identity_matrix.
      destruct (stn_eq_or_neq i i).
      + rewrite coprod_rect_compute_1.
        apply riglunax2.
      + (*apply isirrefl_natneq in h. *)
        rewrite coprod_rect_compute_2.
        apply isirrefl_natneq in h.
        apply fromempty. assumption.
  Defined.

  Lemma col_vec_mult_eq
    { n : nat } (mat : Matrix R n n) (v1 v2 : Vector R n)
    : 
    (mat ** (col_vec v1)) = (col_vec v2)
    -> forall i : (stn n),
    @iterop_fun R (@rigunel1 R) op1 n ((mat i) ^ v1) = v2 i.
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold pointwise.
    intros eq.
    intros i.
    unfold col_vec in eq.
    pose (H := @col_vec_inj).
    unfold col_vec in H.
    pose (H' := H R _ _ _ eq).
    rewrite <- H'.
    reflexivity.
  Defined.


  Definition is_symmetric_mat {X : UU} {n : nat} (mat : Matrix X n n) := mat = transpose mat.

  Lemma symmetric_mat_row_eq_col {X : UU} {n : nat} (mat : Matrix X n n) (i : ⟦ n ⟧%stn) :
    is_symmetric_mat mat -> row mat i = col mat i.
  Proof.
    intros issymm_mat. unfold col.
    rewrite <- issymm_mat. apply idpath.
  Defined.

  Lemma identity_matrix_symmetric  {n : nat} : @is_symmetric_mat R n (identity_matrix ).
  Proof.
    unfold is_symmetric_mat.
    apply funextfun. intros i.
    apply funextfun. intros j.
    unfold identity_matrix, transpose, flip.
    destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
    - simpl.
      rewrite i_eq_j.
      rewrite stn_eq_or_neq_refl.
      simpl.
      apply idpath.
    - rewrite coprod_rect_compute_2.
      destruct (stn_eq_or_neq j i) as [cnt | ?].
      + rewrite cnt in i_neq_j. (* TODO have a lemma for (i = j) (i ≠ j) too - pattern is used often*)
        apply issymm_natneq in i_neq_j.
        apply isirrefl_natneq in i_neq_j.
        contradiction.
      + simpl.
        apply idpath.
  Defined.

  Lemma pointwise_prod_idvec {n : nat} (v : Vector R n) (i : ⟦ n ⟧%stn) :
    v ^ (stdb_vector i) = scalar_lmult_vec (v i) (stdb_vector i).
  Proof.
    unfold  scalar_lmult_vec.
    unfold const_vec, pointwise.
    apply funextfun. intros j.
    destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
    - rewrite i_eq_j; apply idpath.
    - unfold stdb_vector.
      rewrite (stn_eq_or_neq_right i_neq_j).
      do 2 rewrite rigmultx0.
      apply idpath.
  Defined.

  Lemma idmat_i_to_idvec {n : nat} (i : ⟦ n ⟧%stn) : (@identity_matrix R) i = (@stdb_vector R i).
  Proof.
    apply funextfun. intros j.
    apply funextfun. intros k.
    destruct (stn_eq_or_neq j k); simpl; apply idpath.
  Defined.

  Lemma id_mat_ii {n : nat} (i : ⟦ n ⟧%stn) : (@identity_matrix R n) i i = rigunel2.
  Proof.
    unfold identity_matrix.
    rewrite (stn_eq_or_neq_refl); simpl; apply idpath.
  Defined.

  Lemma id_mat_ij {n : nat} (i j : ⟦ n ⟧%stn) : i ≠ j -> (@identity_matrix R n) i j = rigunel1.
  Proof.
    intros i_neq_j.
    unfold identity_matrix.
    rewrite (stn_eq_or_neq_right i_neq_j); simpl; apply idpath. (* TODO Should we try to use ; all the time ?*)
  Defined.

  Lemma matrunax2 : ∏ (n : nat) (mat : Matrix R n n),
    (mat ** identity_matrix) = mat.
  Proof.
    intros n mat.
    apply funextfun. intros i.
    apply funextfun. intros j.
    unfold matrix_mult.
    rewrite (pulse_function_sums_to_point_rig'' _ (stn_implies_ngt0 i) j);
    rewrite <- (symmetric_mat_row_eq_col _ _ identity_matrix_symmetric); (* Non-descript name ?*)
    unfold pointwise, row.
    - rewrite id_mat_ii, rigrunax2.
      apply idpath.
    - intros k j_neq_k.
      rewrite (id_mat_ij _ _ j_neq_k), rigmultx0.
      apply idpath.
  Defined.

  Lemma idrow_sums_to_1 { n : nat } (i : ⟦ n ⟧%stn) :
    Σ ((@identity_matrix R n ) i) = 1%rig.
  Proof.
    rewrite (pulse_function_sums_to_point_rig'' _ (stn_implies_ngt0 i) i).
    - unfold identity_matrix.
      rewrite stn_eq_or_neq_refl, coprod_rect_compute_1.
      apply idpath.
    - unfold identity_matrix.
      intros ? i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      apply idpath.
  Defined.

  (* Should be renamed isinvertible_matrix or something close to that *)
  Definition matrix_inverse {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix) × ((B ** A) = identity_matrix).

  (* TODO: name as e.g. [matrix_right_inverse] since gives choice of inverse? and similar vice versa below. *)
  Definition matrix_right_inverse {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix).

  Definition matrix_left_inverse {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((B ** A) = identity_matrix).

  Lemma matrix_inverse_unique {n : nat} (A : Matrix R n n)
    (B C : matrix_inverse A) : pr1 B = pr1 C.
  Proof.
    revert B C.
    unfold matrix_inverse.
    intros.
    apply funextfun; intros i.
    apply funextfun; intros j.
  Abort.

  (* The product of two invertible matrices being invertible *)
  Lemma inv_matrix_prod_is_inv {n : nat} (A : Matrix R n n)
    (A' : Matrix R n n) (pa : matrix_inverse A) (pb : matrix_inverse A') :
    (matrix_inverse (A ** A')).
  Proof.
    intros.
    use tpair. { exact ((pr1 pb) ** (pr1 pa)). }
    use tpair.
    - rewrite matrix_mult_assoc.
      rewrite <- (matrix_mult_assoc A' _ _).
      replace (A' ** pr1 pb) with (@identity_matrix R n).
      + rewrite matlunax2.
        replace (A ** pr1 pa) with (@identity_matrix R n).
        2 : { symmetry.
              set (p := (pr1 (pr2 pa))). rewrite p.
              reflexivity.
        }
        reflexivity.
      + rewrite <- matrunax2.
        replace (A' ** pr1 pb) with (@identity_matrix R n).
        { rewrite matrunax2.
          reflexivity. }
        set (p := pr1 (pr2 pb)). rewrite p.
        reflexivity.
    - simpl.
      rewrite <- matrix_mult_assoc.
      rewrite  (matrix_mult_assoc (pr1 pb) _ _).
      replace (pr1 pa ** A) with (@identity_matrix R n).
      2 : { symmetry. rewrite (pr2 (pr2 pa)). reflexivity. }
      replace (pr1 pb ** identity_matrix) with (pr1 pb).
      2 : { rewrite matrunax2. reflexivity. }
      rewrite (pr2 (pr2 pb)).
      reflexivity.
  Defined.

  Lemma identity_matrix_is_inv { n : nat } : matrix_inverse (@identity_matrix _ n).
  Proof.
    use tpair. { exact identity_matrix. }
    use tpair; apply matrunax2.
  Defined.

  Lemma nil_matrix_is_inv {n : nat} (A : Matrix R n n) (eq : n = 0): matrix_inverse A.
  Proof.
    simpl.
    unfold matrix_inverse.
    use tpair; try assumption; simpl.
    use tpair; simpl.
    - apply funextfun; intros i. apply fromstn0. rewrite eq in i. assumption.
    - apply funextfun; intros i. apply fromstn0. rewrite eq in i. assumption.
  Defined.

  Lemma square_inverse_left_right_eq 
    {n : nat} (A B : Matrix R n n)
    (e1 : (A ** B) = identity_matrix) (e2 : (B ** A) = identity_matrix)
    : A = B.
  Proof.
  Abort.

  Lemma nil_matrix_eq1 {X : UU} {m n : nat} (A B: Matrix X m n) (eq0 : m = 0)
    : A = B.
  Proof.
    apply funextfun; intros i; apply fromstn0. rewrite eq0 in i. assumption.
  Defined.

  Lemma nil_matrix_eq2 {X : UU} {m n : nat} (A B: Matrix X m n) (eq0 : n = 0)
    : A = B.
  Proof.
    apply funextfun; intros ?; apply funextfun; intros j.
    apply fromstn0. rewrite eq0 in j. assumption.
  Defined.

  Lemma transpose_inj {X : UU} (m n : nat) (mat1 mat2 : Matrix X n n):
    transpose mat1 = transpose mat2 -> mat1 = mat2.
  Proof.
    intros H; exact (invmaponpathsweq (make_weq _ (isweq_flipsec)) _ _ H).
  Defined.

  Definition diagonal_sq { n : nat } (mat : Matrix R n n) :=
    λ i : (stn n), mat i i.

  Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn), (stntonat _ i ≠ (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_upper_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i > (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_lower_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ), (stntonat _ i < (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_upper_triangular_partial { m n k : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i > (stntonat _ j)) -> i < k -> (mat i j) = 0%rig.

  Definition diagonal_all_nonzero { n : nat } (mat : Matrix hq n n) :=
    ∏ i : ⟦ n ⟧%stn, mat i i != 0%hq.

  Definition ij_minor {X : rig} {n : nat} ( i j : ⟦ S n ⟧%stn ) (mat : Matrix X (S n) (S n)) : Matrix X n n.
  Proof.
    intros i' j'.
    exact (mat (dni i i') (dni j j')).
  Defined.

  Definition determinant_cofactor { n : nat } (mat : Matrix hq (n) (n)) : hq.
  Proof.
    induction n. {  exact (@rigunel2 hq). }
    destruct (nat_eq_or_neq n 1 ). { exact (firstValue (firstValue mat)). }
    destruct (nat_eq_or_neq n 2 ).
    { exact (firstValue (firstValue mat) * (lastValue (lastValue (mat)))
             - (lastValue (firstValue mat))  * (firstValue(lastValue (mat))))%hq. }
    set (mp := λ i : ⟦ S n ⟧%stn, iterop_fun 0%hq op2 (λ j : ⟦ (S n) + i ⟧%stn, (- 1%hq)%hq)).
    set (q := (λ i : ⟦ S n ⟧%stn, (IHn ((@ij_minor hq _ i (0,, natgthsn0 n) mat))))).
    exact ( (iterop_fun 0%hq op1 (λ i : ⟦ S n ⟧%stn, (mp i) * q i)))%hq.
  Defined.

End Matrices.


  (* Things that are not really specific to hq but used in later in hq
     - TODO either generalize elimination procedures or state below
       in terms of commrings and prove hq is one. *)
Section MatricesHq.

  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Lemma upper_triangular_iff_transpose_lower_triangular
  { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
  : (@is_upper_triangular hq n n mat)
  <-> (@is_lower_triangular hq n n (transpose mat)).
  Proof.
    unfold  is_upper_triangular,  is_lower_triangular, transpose, flip.
    split.
    - intros inv i j i_lt_j.
      rewrite inv; try assumption; reflexivity.
    - intros inv i j i_gt_j.
      rewrite inv; try assumption; reflexivity.
  Defined.

  Lemma matrix_product_transpose
  { n : nat } (A B : Matrix hq n n)
  : (transpose (A ** B)) = ((transpose B) ** (transpose A)).
  Proof.
    intros.
    unfold transpose, flip.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    symmetry; rewrite matrix_mult_eq; unfold matrix_mult_unf.
    apply funextfun. intros i.
    apply funextfun. intros j.
    etrans. {apply maponpaths. apply funextfun. intros ?. rewrite hqmultcomm. reflexivity. }
    reflexivity.
  Defined.

  Lemma invertible_to_transpose_invertible
  { n : nat } (mat : Matrix hq n n)
  :
  (@matrix_inverse hq n mat)
  ->
  (@matrix_inverse hq n (transpose mat)).
  Proof.
    assert (eq : transpose (@identity_matrix hq n) = @identity_matrix hq n).
    { unfold transpose. unfold flip.
      apply funextfun; intros ?. apply funextfun; intros ?.
      unfold identity_matrix.
      destruct (stn_eq_or_neq _) as [eq' | neq]; try simpl.
      - symmetry in eq'.
        rewrite (stn_eq_or_neq_left eq'); simpl.
        reflexivity.
      - destruct (stn_eq_or_neq _ _) as [contr | ?].
        2: {simpl. reflexivity. }
        simpl.
        rewrite contr in neq.
        apply isirrefl_natneq in neq.
        contradiction.
    }
    try split.
    - intros inv1.
      destruct inv1 as [inv1 isinv1].
      destruct isinv1 as [isrightinv1 isleftinv1].
      use tpair.
      {exact (transpose inv1). }
      split.
      + rewrite <- matrix_product_transpose in *.
        rewrite isleftinv1.
        assumption.
      + rewrite <- matrix_product_transpose in *.
        rewrite isrightinv1.
        assumption.
  Defined.

  Lemma transpose_invertible_to_invertible
  { n : nat } (mat : Matrix hq n n)
  :
  (@matrix_inverse hq n (transpose mat)) 
  -> (@matrix_inverse hq n mat).
  Proof.
    intros.
    assert (eq : mat = (transpose (transpose mat))). {reflexivity. }
    rewrite eq.
    apply invertible_to_transpose_invertible; assumption.
  Defined.

  Lemma zero_row_to_non_invertibility { n : nat } (A : Matrix hq n n)
      (i : ⟦ n ⟧%stn) (zero_row : A i = (const_vec 0%hq)) :
  (@matrix_inverse hq n A) -> empty.
  Proof.
    intros invA.
    destruct invA as [inv isinv].
    destruct isinv as [isrightinv isleftinv]. (* TODO fix order *)
    assert (∏ i j : ⟦ n ⟧%stn, (A ** inv) i j = identity_matrix i j).
    { intros.  rewrite isrightinv. reflexivity. }
    destruct (natchoice0 n) as [eq | gt].
    { apply fromstn0. clear zero_row. rewrite <- eq in i. assumption. }
    assert (contr : (A ** inv) i i = 0%hq).
    { rewrite matrix_mult_eq. unfold matrix_mult_unf.
      rewrite zero_function_sums_to_zero. {reflexivity. }
      apply funextfun. intros k.
      replace (A i k) with 0%hq.
      { apply (@rigmult0x hq). }
      rewrite zero_row. reflexivity.
    }
    pose (id_ii := (@id_mat_ii hq n)).
    rewrite isrightinv in contr.
    rewrite id_ii in contr.
    change 1%rig with 1%hq in contr.
    pose (t1 := intpart 1%hq).
    pose (t2 := intpart 0%hq).
    assert (contr' : t1 != t2).
    {apply hzone_neg_hzzero. }
    unfold t1, t2 in contr'.
    rewrite contr in contr'.
    contradiction.
  Defined.

  Lemma diagonal_nonzero_iff_transpose_nonzero
    { n : nat } (A : Matrix hq n n)
    : diagonal_all_nonzero A
    <-> (diagonal_all_nonzero (transpose A)).
  Proof.
    split ; intros H; unfold diagonal_all_nonzero, transpose, flip; apply H.
  Defined.

  Lemma upper_triangular_transpose_is_lower_triangular
    { n : nat } (A : Matrix hq n n)
    (H: @is_upper_triangular hq n n A)
    : (@is_lower_triangular hq n n (transpose A)).
  Proof.
    intros i j lt; unfold is_upper_triangular; apply H; assumption. 
  Defined.


End MatricesHq.


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

  (* This proof should probably be redone with all 3 destructs at top *)
  Definition transposition_perm {n : nat} (i j : ⟦ n ⟧%stn)
    : ⟦ n ⟧%stn ≃ ⟦ n ⟧%stn.
  Proof.
    exists (transposition_fun i j).
    use isweq_iso.
    - exact (transposition_fun i j).
    - intros k.
      unfold transposition_fun.
      destruct (stn_eq_or_neq i) as [i_eq| i_neq].
      + destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k].
        * rewrite i_eq_k in i_eq.
          symmetry; assumption.
        * destruct (stn_eq_or_neq j k).
          -- assumption.
          -- rewrite <- i_eq in *.
             apply isirrefl_natneq in i_neq_k.
             contradiction. (*  This is repeated too many times *)
      + destruct (stn_eq_or_neq j) as [j_eq | j_neq].
        * destruct (stn_eq_or_neq j) as [j_eq' | j_neq'].
          -- destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k].
             ++ assumption.
             ++ rewrite j_eq' in *.
                assumption.
          -- destruct (stn_eq_or_neq i k).
             ++ assumption.
             ++ apply isirrefl_natneq in i_neq.
                contradiction.
        * destruct (stn_eq_or_neq i k).
          -- rewrite stn_eq_or_neq_refl.
             assumption.
          -- rewrite (stn_eq_or_neq_right j_neq).
             apply idpath.
    - intros k.
      unfold transposition_fun.
      destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k];
      destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
      + rewrite  i_eq_k in *.
        symmetry; assumption.
      + rewrite stn_eq_or_neq_refl.
        assumption.
      + assert (j_neq_k : j ≠ k).
        { rewrite i_eq_j in i_neq_k.
          assumption.
        }
        rewrite (stn_eq_or_neq_right j_neq_k).
        rewrite (stn_eq_or_neq_right i_neq_k).
        rewrite (stn_eq_or_neq_right j_neq_k).
        apply idpath.
      + destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
        * rewrite stn_eq_or_neq_refl.
          assumption.
        * rewrite (stn_eq_or_neq_right i_neq_k).
          rewrite (stn_eq_or_neq_right j_neq_k).
          apply idpath.
  Defined.

  Definition transposition_mat_rows {X : UU} {m n  : nat} (i j : ⟦ m ⟧%stn)
    : (Matrix X m n) -> Matrix X m n.
  Proof.
    intros mat.
    unfold Matrix in mat.
    unfold Vector in mat at 1.
    intros k.
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

  Definition transpose_permutation_fun {n : nat} (p :  ⟦ n ⟧%stn -> ⟦ n ⟧%stn ) (i j : ⟦ n ⟧%stn) :  ⟦ n ⟧%stn -> ⟦ n ⟧%stn.
  Proof.
    intros k.
    destruct (stn_eq_or_neq i k).
    - exact (p j).
    - destruct (stn_eq_or_neq j k).
      + exact (p i).
      + exact (p k).
  Defined.

  (* TODO clean up - and this should follow from  transposition_perm  ?  *)
  Definition permutation_fun_closed_under_tranpose {n : nat} (p : ⟦ n ⟧%stn -> ⟦ n ⟧%stn) (isp : is_permutation_fun p) :
    ∏ i j : ⟦ n ⟧%stn, is_permutation_fun (transpose_permutation_fun p i j).
  Proof.
    intros i j.
    unfold is_permutation_fun, transpose_permutation_fun.
    intros i' j'.
    unfold is_permutation_fun in isp.
    destruct (stn_eq_or_neq i i') as [i_eq_i' | F].
    - destruct (stn_eq_or_neq i j') as [i_eq_j' | F'].
      + intros ?. rewrite <- i_eq_i', i_eq_j'.
        reflexivity.
      + destruct (stn_eq_or_neq j j') as [j_eq_j' | ?].
        * intros j_eq_i.
          apply isp in j_eq_i.
          rewrite <- j_eq_j',  j_eq_i.
          rewrite i_eq_i'.
          apply idpath.
        * intros j_eq_j'.
          apply isp in j_eq_j'.
          rewrite j_eq_j' in *.
          apply isirrefl_natneq in h. (* TODO h ? *)
          contradiction.
    - destruct (stn_eq_or_neq j i') as [j_eq_i' | j_neq_i'] ;
        destruct (stn_eq_or_neq i j') as [i_eq_j' | i_neq_j'].
      +
        intros i_eq_j.
        rewrite <- i_eq_j'.
        apply isp in i_eq_j.
        rewrite i_eq_j.
        rewrite j_eq_i'.
        reflexivity.
      + destruct (stn_eq_or_neq j j').
        * intros i_eq_i.
          rewrite <- p0.
          rewrite j_eq_i'.
          reflexivity.
        * intros i_eq_j'.
          apply isp in i_eq_j'.
          rewrite i_eq_j' in i_neq_j'.
          apply isirrefl_natneq in i_neq_j'.
          contradiction.
      + intros i'_eq_j.
        apply isp in i'_eq_j.
        rewrite i'_eq_j in j_neq_i'.
        apply isirrefl_natneq in j_neq_i'.
        contradiction.
      + destruct (stn_eq_or_neq j j') as [j_eq_j' | j_neq_j'].
        * intros i'_eq_i.
          apply isp in i'_eq_i.
          rewrite i'_eq_i in F.
          apply isirrefl_natneq in F.
          contradiction.
        * intros i'_eq_j'.
          apply isp in i'_eq_j'.
          assumption.
  Defined.

End Transpositions.