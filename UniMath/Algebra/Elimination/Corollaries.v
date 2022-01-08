
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


Local Notation Σ := (iterop_fun hqzero op1).
Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* output: a solution [x] to [mat ** x = vec] (if one exists?) *)
  (* TODO: what conditions on [mat] are needed to ensure this is a solution? *)
  Definition back_sub_step { n : nat } ( iter : (⟦ n ⟧)%stn ) 
  (mat : Matrix hq n n) (b : Vector hq n) (vec : Vector hq n) : Vector hq n.
  Proof.
    intros i.
    destruct (nat_eq_or_neq iter i).
    2 : {exact (b i). }
    destruct (natlehchoice (S (pr1 iter)) n) as [? | ?]. {apply iter. }
    - exact (((vec i) * hqmultinv (mat i i))
           - ((Σ (mat i ^ b)  - (b  i)* (mat i i))
           * (hqmultinv (mat i i))))%hq.
    - exact ((hqmultinv (mat i i)) * (vec i))%hq.
  Defined.

  (* TODO moderately large cleanup needed - rename temp variables *)
  Lemma back_sub_step_inv0 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (x : Vector hq n) (b : Vector hq n)
        (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_all_nonzero mat):
    ((mat ** (col_vec (back_sub_step iter mat x b))) iter  = (col_vec b) iter).
  Proof.
    intros.
    unfold back_sub_step, col_vec.
    rewrite matrix_mult_eq; unfold matrix_mult_unf, pointwise.
    set (m := n - (S iter)).
    assert (spliteq : n = (S iter) + m ).  (* Could do away with this if iter is ⟦ S n ⟧ instead of ⟦ n ⟧ ? *)
    { unfold m.
      rewrite natpluscomm.
      rewrite minusplusnmm.
      - apply idpath.
      - simpl. exact (pr2 iter).
    }
    generalize iter mat b p' p x.
    set (itersucc := (stn_inhabited_implies_succ iter)).
    destruct itersucc as [pr1_ pr2_].
    rewrite pr2_ in *.
    intros iter' mat' vec' filled' is_upper_t' b'.
    apply funextfun;  intros ?.
    rewrite (@rigsum_dni hq (pr1_)  _ iter').
    rewrite nat_eq_or_neq_refl.
    destruct (natlehchoice (S (Preamble.pr1 iter')) (S pr1_)) as [lt | eq]. (* TODO why is this S _ < S _ ? **)
    - etrans. { apply maponpaths_2; apply maponpaths; reflexivity. }
      etrans.
      { apply maponpaths_2.
        apply maponpaths.
        apply funextfun. intros q.
        unfold funcomp.
        rewrite (nat_eq_or_neq_right (dni_neq_i iter' q)).
        reflexivity.
      }
      rewrite (@rigsum_dni hq ( pr1_)  _ iter').
      set (f := λ q : (⟦ pr1_ ⟧%stn), _).
      set (a := mat' iter' iter').
      set (b'' := b' iter').
      etrans.
      { apply maponpaths.
        etrans.
        { apply maponpaths.
        rewrite hqmultcomm.
        apply maponpaths.
        rewrite hqmultcomm.
        reflexivity. }
        apply (@ringminusdistr hq a).
      }
      etrans.
      { apply maponpaths.
        apply map_on_two_paths.
        rewrite <- (@rigassoc2 hq).
        rewrite hqisrinvmultinv.
        2: { unfold a.
            apply  filled'. }
        apply (@riglunax2 hq).
        apply maponpaths.
        rewrite <- (@rigassoc2 hq).
        rewrite hqisrinvmultinv. 2: { apply filled'. }
        apply (@riglunax2 hq).
      }
      set (sum := iterop_fun _ _ _).
      (* TODO extract below into  a lemma hqplusminus *)
      assert (eq: ∏ sum b'' a : hq, (sum + b''*a - b''*a)%hq = sum ).
      { clear sum b'' a. intros sum b'' a.
        replace (sum + b'' * a - b'' * a)%hq with (sum + b'' * a + (- b'' * a))%hq.
        - rewrite hqplusassoc.
          replace (b'' * a + - b'' * a)%hq with (b'' * a  - b'' * a)%hq.
          + rewrite hqrminus; apply (@rigrunax1 hq).
          + symmetry.
            rewrite hqpluscomm.
            rewrite hqrminus.
            change (- b'' * a)%hq with ((- b'') * a)%hq.
            replace  (- b'' * a)%hq with (- (b'' *a))%hq.
            * rewrite (hqlminus (b'' * a)%hq).
              reflexivity.
            * rewrite  (@ringlmultminus hq).
              reflexivity.
        - symmetry.
          rewrite hqpluscomm.
          replace  (- b'' * a)%hq with (- (b'' *a))%hq.
          * reflexivity.
          * rewrite  (@ringlmultminus hq).
            reflexivity.
      }
      etrans.
      { do 3 apply maponpaths.
        rewrite (@rigcomm2 hq).
        rewrite eq.
        reflexivity.
      }
      rewrite (@rigcomm1 hq).
      rewrite (@rigassoc1 hq).
      unfold funcomp.
      rewrite hqlminus.
      rewrite hqplusr0.
      apply idpath.
    - rewrite (@zero_function_sums_to_zero hq).
      + rewrite (@riglunax1 hq).
        rewrite <- (@rigassoc2 hq).
        rewrite hqisrinvmultinv.
        2 : { apply filled'.  }
        rewrite (@riglunax2 hq).
        reflexivity.
      + simpl.
        apply funextfun. intros q.
        etrans.
        { apply maponpaths_2.
          rewrite is_upper_t'. {reflexivity. }
          unfold dni, di; simpl.
          destruct (natlthorgeh q iter') as [gt | ?].
          { apply gt. }
          apply invmaponpathsS in eq.
          apply fromempty.
          assert (q_ge_iter' : q ≥ (pr1 iter')).
          { apply h. }
          rewrite eq in q_ge_iter'.
          apply natgehtonegnatlth in q_ge_iter'.
          assert (q_le_iter_absurd : q < pr1_).
          { apply (pr2 q). }
            exact (q_ge_iter' q_le_iter_absurd).
          }
        rewrite (@rigmult0x hq).
        reflexivity.
  Defined.

  Lemma back_sub_step_inv1 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (b : Vector hq n) (vec : Vector hq n) (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_all_nonzero mat): ∏ i : ⟦ n ⟧%stn, i ≠ iter ->
    (col_vec (back_sub_step iter mat b vec) i  = ( (col_vec  (*vec*) b)) i).
  Proof.
    intros i ne.
    unfold back_sub_step.
    unfold col_vec.
    apply funextfun. intros j.
    simpl.
    destruct (nat_eq_or_neq iter i) as [eq | ?].
    - rewrite eq in ne.
      apply isirrefl_natneq in ne.
      contradiction.
    - apply idpath.
  Defined.


  Lemma back_sub_step_inv2 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (b : Vector hq n) (vec : Vector hq n) (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_all_nonzero mat):
     ∏ i : ⟦ n ⟧%stn, i ≥ iter ->
       (mat ** (col_vec b )) i = (col_vec  vec) i
    -> (mat ** (col_vec (back_sub_step iter mat b vec))) i = ((col_vec vec) i).
  Proof.
    intros i lt H.
    unfold transpose, flip in *.
    destruct iter as [iter p''].
    rewrite <- H.
    destruct (natlehchoice iter i). {apply lt. }
    - rewrite matrix_mult_eq.
      apply pathsinv0.
      rewrite matrix_mult_eq.
      unfold matrix_mult_unf.
      rewrite matrix_mult_eq in H.
      unfold matrix_mult_unf in H.
      apply funextfun; intros ?.
      apply maponpaths.
      apply funextfun. intros i'.
      destruct (stn_eq_or_neq i' (iter,, p'')).
      2: { rewrite back_sub_step_inv1; try assumption; reflexivity. }
      replace (mat i i') with 0%hq.
      2: {rewrite p; try reflexivity.
          change (stntonat _ i) with (pr1 i) in lt.
          change (stntonat _ (iter,, p'')) with (iter) in lt.
          replace iter with (pr1 i') in lt.
          2: {rewrite p0. reflexivity. }
          rewrite p0.
          try apply lt.
          apply h.
      }
      do 2 rewrite (@rigmult0x hq); reflexivity.
    - revert lt. revert p''. rewrite p0.
      intros.
      replace (stntonat _ i,, p'') with i.
      2: { do 2 change (stntonat _ i) with (pr1 i).
           change i with (pr1 i,, pr2 i).
           simpl.
           assert (eq : (pr2 i) = p'').
           { apply proofirrelevance. apply propproperty. }
           rewrite eq. reflexivity.
      }
      rewrite back_sub_step_inv0; try reflexivity; try assumption.
      apply pathsinv0. apply H.
  Defined.

  Lemma back_sub_step_inv3 { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix hq n n)
        (b : Vector hq n) (vec : Vector hq n) (p: @is_upper_triangular hq n n mat)
        (p' : diagonal_all_nonzero mat):
     ∏ i : ⟦ n ⟧%stn, i > iter ->
       (mat ** (col_vec b )) i = (mat ** (col_vec (back_sub_step iter mat b vec))) i.
  Proof.
    intros i lt.
    unfold transpose, flip in *.
    destruct iter as [iter p''].
    destruct (natlehchoice iter i). {apply natlthtoleh in lt. apply lt. }
    - rewrite matrix_mult_eq.
      apply pathsinv0.
      rewrite matrix_mult_eq.
      unfold matrix_mult_unf.
      apply funextfun; intros ?.
      apply maponpaths.
      apply funextfun. intros i'.
      destruct (stn_eq_or_neq i' (iter,, p'')).
      2: { rewrite back_sub_step_inv1; try assumption; reflexivity. }
      replace (mat i i') with 0%hq.
      2: {rewrite p; try reflexivity.
          change (stntonat _ i) with (pr1 i) in lt.
          change (stntonat _ (iter,, p'')) with (iter) in lt.
          replace iter with (pr1 i') in lt.
          2: {rewrite p0. reflexivity. }
          rewrite p0.
          try apply lt.
          apply h.
      }
      do 2 rewrite (@rigmult0x hq); reflexivity.
    - rewrite <- p0 in lt.
      apply isirreflnatgth in lt. contradiction.
  Defined.



  (* TODO: document what this is meant to do? *)
  (* TODO fix signature *)
  Definition back_sub_internal
    { n : nat } (mat : Matrix hq n n) (b : Vector hq n) (vec : Vector hq n) (iter : ⟦ S n ⟧%stn)
    : Vector hq n.
  Proof.
    destruct iter as [iter p].
    induction iter as [ | m IHn] .
    - exact b.
    - assert (p' : m < S n). {apply (istransnatlth _ _ _ (natgthsnn m) p). }
      set (m' := dualelement (m,, p)).
      assert (p'' : (pr1 m') <  S n). {apply (istransnatlth _ _ _  (pr2 m') (natgthsnn n) ). }
      exact (back_sub_step (m') mat (IHn (p')) vec).
  Defined.

  Definition back_sub {n : nat} (mat : Matrix hq n n) (vec : Vector hq n)
    := back_sub_internal mat vec vec (n,, natgthsnn n).

  (* TODO  H not even used here ??? *)
  Lemma back_sub_internal_inv0
        { n : nat } (mat : Matrix hq n n) (b : Vector hq n)
        (vec : Vector hq n) (ut : @is_upper_triangular hq _ _ mat)
        (df : diagonal_all_nonzero mat) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < (dualelement iter)(* i < iter *)
    -> (((col_vec (back_sub_internal mat b vec iter)))) i = ((col_vec b) i).
  Proof.
    destruct iter as [iter p].
    induction iter.
    { intros i H.
      unfold dualelement in H.
      destruct (natchoice0 (S n)) in H. {clear H. apply negpaths0sx in p0. contradiction. }
      simpl.
      unfold back_sub_internal.
      simpl.
      simpl in H.
      reflexivity. }
    unfold back_sub_internal.
    intros i i_lt_dual.
    rewrite nat_rect_step.
    assert (p': iter < S n). { apply (istransnatlth _ _ _ (natgthsnn iter) p).  }
    assert (lt : i < dualelement (iter,, p')).
    {unfold dualelement in *.
     destruct (natchoice0 (S n)) in *. { pose (contr := (natneq0sx n)). rewrite p0 in contr.
                                         apply isirrefl_natneq in contr. contradiction. }
      simpl in *.
      refine (istransnatgth _ _ _ _ _).
      { set (n' := n - 0 - iter).
        apply natminus1lthn.
        rewrite minus0r.
        apply minusgth0.
        exact p.
      }
      replace (n - 0 - iter - 1) with (n - 0 - (S iter)); try apply i_lt_dual.
      rewrite minus0r.
      rewrite natminusminus.
      replace (S iter) with (iter + 1); try reflexivity.
      rewrite <- plus_n_Sm, natplusr0.
      reflexivity.
    }
    rewrite <- (IHiter p'); try assumption.
    rewrite back_sub_step_inv1; try reflexivity; try assumption.
    2: { unfold dualelement in i_lt_dual.
         unfold dualelement.
         apply natlthtoneq.
         unfold dualelement in *.
         destruct (natchoice0 n).
         {apply fromstn0. clear i_lt_dual. clear lt. rewrite <- p0 in i.
          assumption. }
          destruct (natchoice0 (S n)) in *.
         {simpl. pose (contr := natneqsx0 n). rewrite  p0 in contr.
          apply isirrefl_natneq in contr. contradiction.  }
         simpl in *.
         rewrite minus0r in i_lt_dual.
         replace (S iter) with (iter + 1) in i_lt_dual.
         2: { rewrite <- plus_n_Sm, natplusr0. reflexivity. }
         rewrite natpluscomm in i_lt_dual.
         rewrite <- natminusminusassoc in i_lt_dual. assumption.
         }
    unfold back_sub_internal.
    apply maponpaths_2.
    apply maponpaths.
    apply proofirrelevance; apply propproperty.
  Defined.

  Lemma back_sub_internal_inv2
        { n : nat } (mat : Matrix hq n n) (b : Vector hq n)
        (vec : Vector hq n) (ut : @is_upper_triangular hq _ _ mat)
        (df : diagonal_all_nonzero mat) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i ≥ (dualelement iter)
    -> (mat ** (col_vec (back_sub_internal mat b vec iter))) i = (col_vec vec) i.
  Proof. 
    unfold transpose, flip.
    intros i i_le_iter.
    unfold back_sub_internal.
    destruct iter as [iter p].
    induction iter as [| ? ?].
    { apply fromempty.
      unfold dualelement in i_le_iter.
      destruct (natchoice0 (S n)) in i_le_iter.
      {apply fromempty. clear i_le_iter. apply negpaths0sx in p0; contradiction. }
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
    destruct (natlehchoice (dualelement (iter,, p)) (i)).
      { unfold dualelement in *.
        destruct (natchoice0 n) as [p0 | ?]. {apply fromstn0. rewrite p0. assumption. }
        destruct (natchoice0 (S n)) as [p0 | ?] in *.
        { pose (contr := (natneq0sx n)). rewrite <- p0 in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2 in *.
        simpl in *.
        assert (eq' : ∏ n : nat, S n = (n + 1)%nat).
        { intros. rewrite <- plus_n_Sm, natplusr0. apply idpath.  }
        rewrite eq' in i_le_iter.
        rewrite minus0r in i_le_iter.
        rewrite natpluscomm in i_le_iter.
        rewrite <- natminusminus in i_le_iter.
        rewrite i_le_iter; reflexivity.
      }
    - rewrite back_sub_step_inv2; try reflexivity; try assumption.
      { unfold dualelement. unfold dualelement in h.
        destruct (natchoice0 n) as [p0 | ?]. {apply fromstn0. rewrite p0. assumption. }
        rewrite coprod_rect_compute_2 in *.
        apply natgthtogeh.
        assumption.
      }
      rewrite IHiter; try reflexivity.
      { unfold dualelement.
        destruct (natchoice0 (S n)) as [p0 | ?] in *.
        { pose (contr := (natneq0sx n)). rewrite <- p0 in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2.
        unfold dualelement in h.
        destruct (natchoice0 n) as [p0 | ?]. {apply fromstn0. rewrite p0. assumption. }
        rewrite coprod_rect_compute_2 in *.
        simpl; simpl in h.
        rewrite minus0r.
        apply natgthtogehsn in h.
        rewrite pathssminus in h.
        2: { rewrite pathssminus.
             - rewrite PAdics.lemmas.minussn1.
               exact p.
             - simpl; apply h1. }
        assert (e : n = S (n - 1)).
        { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
          apply pathsinv0. apply minusplusnmm. assumption. }
        rewrite <- e in h.
        apply h.
      }
    - assert (eq: (dualelement (iter,, p)) = i).
      { unfold dualelement in *.
           try rewrite  p0.
           destruct (natchoice0 n) as [? | ?]. {apply fromstn0. rewrite p1. assumption. }
           rewrite coprod_rect_compute_2 in *.
           unfold make_stn in *; simpl in *.
           change (stntonat _ i) with (pr1 i) in p0.
           symmetry in p0.
           change i with (pr1 i,, pr2 i).
           set (rhs := make_stn n (n - 1 - iter) (StandardFiniteSets.dualelement_lt iter n h)).
           change (n - 1 - iter) with (pr1 rhs).
           try rewrite <- p0. try apply p0. try assumption.
           clear IHiter.
           simpl.
           simpl in p0.
           apply subtypePath_prop.
           rewrite p0.
           reflexivity.
      }
      rewrite eq.
      rewrite back_sub_step_inv0; try reflexivity; try assumption.
  Defined.

  Lemma back_sub_inv0 { n : nat } (mat : Matrix hq n n) (b vec : Vector hq n)
        (ut : @is_upper_triangular hq _ _ mat)
    (df: diagonal_all_nonzero mat) : (mat ** (col_vec (back_sub mat vec))) = (col_vec vec).
  Proof.
    intros.
    unfold back_sub.
    destruct (natchoice0 n) as [p | ?].
    { apply funextfun. intros i. apply fromstn0. rewrite p. simpl. assumption. }
    apply funextfun; intros i.
    try apply back_sub_internal_inv0; try assumption.
    apply back_sub_internal_inv2; try assumption.
    unfold dualelement.
    destruct (natchoice0 (S n)). { apply fromempty. apply negpaths0sx in p. assumption. }
    simpl.
    rewrite minus0r.
    rewrite minusnn0.
    reflexivity.
  Defined.

  (* Construct the inverse, if additionally mat is upper triangular with non-zero diagonal *)
  Definition upper_triangular_inverse_construction
    { n : nat } (mat : Matrix hq n n)
    : Matrix hq n n.
  Proof.
    destruct (natchoice0 n).  { unfold Matrix, Vector. intros i. apply fromstn0. rewrite p. assumption. }
    (* set (ret :=  (transpose (λ i : ⟦ n ⟧%stn, (back_sub mat (@stdb_vector hq n i))))). *)
    (* intros i. *) 
    set (H:= λ i : (stn n), (back_sub (mat) ((@identity_matrix hq n) i))).
    unfold Matrix, Vector.
    apply H.
  Defined. (* TODO remove n -> S n' *)

  
  (* TODO realize this better using the elimination procedure invariants *)
  Lemma invertible_upper_triangular_to_diag_filled { n : nat } (A : Matrix hq n n)
        (p : @is_upper_triangular hq n n A)
        (p': @matrix_inverse hq n A)
        (B : (@matrix_inverse hq n A))
    : (@diagonal_all_nonzero n A).
  Proof.
    apply diagonal_nonzero_iff_transpose_nonzero.
    set (At := (λ y x : (⟦ n ⟧)%stn, A x y)).
    assert (@is_lower_triangular hq n n At).
    { apply upper_triangular_transpose_is_lower_triangular. assumption. }
    unfold diagonal_all_nonzero.
    intros i.
    destruct (isdeceqhq (At i i) 0%hq) as [contr | ne].
    2: { assumption. }
    apply fromempty.
    destruct (natchoice0 n) as [contr' | gt]. {apply fromstn0. rewrite contr'; exact i. }
    set (M :=  @clear_columns_up_to_no_switch_as_left_matrix n gt (n,, natgthsnn n) A).
    assert (invertible : matrix_inverse (M ** A)).
    { apply inv_matrix_prod_is_inv; try assumption.
      apply clear_columns_up_to_matrix_no_switch_invertible.
      apply i. (* TODO remove unnecessary argument *)
    }
    pose (inv := gauss_clear_columns_up_to_no_switch_inv5).
    pose (contr' := inv n At gt (n,, natgthsnn n) X i contr (pr2 i)).
    destruct contr' as [idx contr'].
    set ( At' := gauss_clear_columns_up_to_no_switch gt (n,, natgthsnn n) At).
    pose (noninv := @zero_row_to_non_invertibility n At' idx contr').
    apply noninv. 
    unfold At'.
    rewrite <- gauss_clear_columns_up_to_no_switch_as_matrix_eq.
    apply inv_matrix_prod_is_inv.
    2: {apply transpose_invertible_to_invertible; try assumption. }
    apply clear_columns_up_to_matrix_no_switch_invertible; try assumption. (* TODO remove unused argument *)
  Defined.

  Definition upper_triangular_inverse_is_inverse
  { n : nat } (mat : Matrix hq n n)
  (ut : @is_upper_triangular hq _ _ mat)
  (df: diagonal_all_nonzero mat)
  :
  (mat ** (transpose (upper_triangular_inverse_construction mat)))
  = (@identity_matrix hq n).
Proof.
  destruct (natchoice0 n) as [eq | ?]. {apply funextfun; intros ?. apply fromstn0. rewrite eq. assumption. }
  apply funextfun; intros i.
  unfold matrix_mult, row.
  unfold col, transpose, flip.
  apply funextfun; intros ?.
  rewrite (@col_vec_mult_eq hq n mat (λ y : (⟦ n ⟧)%stn, upper_triangular_inverse_construction mat x y) (@identity_matrix hq n x)).
  - destruct (stn_eq_or_neq i x) as [eq | neq].
    {rewrite eq; reflexivity. }
    rewrite id_mat_ij; try rewrite id_mat_ij; try reflexivity; try assumption.
    apply (issymm_natneq _ _ neq).
  - unfold upper_triangular_inverse_construction. 
    pose (H2 := @back_sub_inv0).
    unfold back_sub.
    destruct (natchoice0 n) as [eq | ?]. {apply fromstn0. rewrite eq. assumption. }
    apply H2; try assumption.
    apply (mat (0,, h0)). (* TODO remove superfluous argument in sig. *)
Defined.