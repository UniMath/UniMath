Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.WellOrderedSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.NumberSystems.Integers.
Require Import UniMath.NumberSystems.RationalNumbers.
Require Import UniMath.RealNumbers.Prelim.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.
Require Import UniMath.Algebra.Elimination.Matrices.
Require Import UniMath.Algebra.Elimination.RowOps.
Require Import UniMath.Algebra.Elimination.Elimination.


(** The purpose of this file is to store a left-over elimination procedure iterating over
    columns instead of rows in the outer loop -
    this alternative procedure allows us to show
    gauss_clear_columns_up_to_no_switch_inv6
    -> a lower triangular matrix with a zero entry in the diagonal
       is non-invertible.

    Note that there are more elementary and perhaps principled proofs of this. *)

Local Notation Σ := (iterop_fun hqzero op1).
Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

(* A variant of gccut that does not switch rows
 This will be used to find a witness to non-invertibility for lower triangular input matrices.  *)
Definition gauss_clear_columns_up_to_no_switch
  { n : nat } (p : n > 0) (k : (⟦ S n ⟧%stn))
  (mat : Matrix hq n n) : Matrix hq n n.
Proof.
  destruct k as [k lt_k_n].
  induction k as [ | k' gauss_clear_earlier_columns].
  - exact mat.
  - assert (lt : k' < S n). {apply (istransnatlth _ _ _ (natgthsnn k') lt_k_n ). }
    set (piv := k').
    destruct (isdeceqhq (mat (k',, lt_k_n) (k',, lt_k_n)) 0%hq).
    + refine ( (gauss_clear_earlier_columns _ )).
      exact lt.
    + refine (gauss_clear_column_old _   (k' ,, lt_k_n)  (k' ,, lt_k_n) (n ,, natlthnsn n ) ).
      refine ( (gauss_clear_earlier_columns _ )).
      exact lt.
Defined.


Lemma clear_columns_up_to_no_switch_as_left_matrix_internal
  { n : nat } (p : n > 0) (* Remove p when gcc is refactored *)
  (k : (⟦ S n ⟧%stn)) (mat : Matrix hq n n) :  Matrix hq n n.
  Proof.
   destruct k as [k lt_k_n].
   induction k as [ | k' gauss_clear_earlier_columns].
   { exact (@identity_matrix hq n). }
   assert (lt : k' < S n). {apply (istransnatlth _ _ _ (natgthsnn k') lt_k_n ). }
   set (mat_by_normal_op :=  (gauss_clear_columns_up_to_no_switch p (k' ,, lt) mat )).
   set (piv :=  make_stn n k' lt_k_n).
   destruct (isdeceqhq (mat (k',, lt_k_n) (k',, lt_k_n)) 0%hq).
   - refine (gauss_clear_earlier_columns _ ).
     exact lt.
   - refine ((gauss_clear_column_as_left_matrix (n,, natlthnsn n) _ (k' ,, lt_k_n) (k' ,, lt_k_n)) ** _ ).
   + exact ( mat_by_normal_op ).
   + refine (gauss_clear_earlier_columns _).
   assumption.
Defined.

Lemma clear_columns_up_to_no_switch_as_left_matrix  { n : nat } (p : n > 0)
(k : (⟦ S n ⟧%stn)) (mat : Matrix hq n n) : Matrix hq n n.
Proof.
  exact ((clear_columns_up_to_no_switch_as_left_matrix_internal p k mat)).
Defined.

Lemma clear_columns_up_to_matrix_no_switch_invertible {n : nat} (p : ⟦ S n ⟧%stn)
(H : n > 0) (k : (⟦ n ⟧%stn)) (mat : Matrix hq n n)
: @matrix_inverse hq _  (clear_columns_up_to_no_switch_as_left_matrix H p mat).
Proof.
  unfold clear_columns_up_to_no_switch_as_left_matrix.
  set (pre := gauss_clear_column_as_left_matrix p mat k).
  unfold gauss_clear_column_as_left_matrix in pre.
  destruct p as [pr1_ pr2_].
  induction pr1_.
  - simpl. apply identity_matrix_is_inv.
  - unfold clear_columns_up_to_no_switch_as_left_matrix_internal.
    rewrite nat_rect_step.
    destruct (isdeceqhq _ _).
    {apply IHpr1_. }
    refine (inv_matrix_prod_is_inv _ _ _ _ ).
    { apply clear_column_matrix_invertible . }
    apply IHpr1_.
Defined.

Lemma gauss_clear_columns_up_to_no_switch_inv0
  ( n : nat ) (mat : Matrix hq n n) (p' : n > 0)
  (iter1 iter2 : ⟦ S n ⟧%stn)  :
  iter1 ≤ iter2 ->
    @is_lower_triangular hq n n (@gauss_clear_columns_up_to_no_switch n p' iter1 mat)
  -> @is_lower_triangular hq n n (@gauss_clear_columns_up_to_no_switch n p' iter2 mat).
Proof.
  intros iter1_le_iter2.
  destruct (natlehchoice iter1 iter2) as [iter1_lt_iter2 | eq]. {assumption. }
  2: { intros H. clear iter1_le_iter2. unfold is_lower_triangular. intros ? ? ?.
  replace iter2 with iter1. {apply H; assumption. }
  apply subtypePath_prop in eq. {rewrite eq; reflexivity. }
  }
  clear iter1_le_iter2.
  destruct iter1 as [iter1 iter1p].
  destruct iter2 as [iter2 iter2p].
  induction iter2.
  { apply fromempty. apply negnatlthn0 in iter1_lt_iter2. contradiction. }
  unfold gauss_clear_columns_up_to_no_switch in *.
  rewrite nat_rect_step.
  destruct (isdeceqhq _ _).
  - intros lt i j i_lt_j.
    destruct (natlehchoice iter1 iter2) as [? | iter1_eq_iter2]. { apply natlthsntoleh. exact iter1_lt_iter2. }
    + apply (IHiter2 (istransnatlth _ _ _ (natgthsnn iter2) iter2p));
      try reflexivity; try assumption.
    + simpl in iter2p.
      replace iter2 with (iter1).
      2: {rewrite <- iter1_eq_iter2. reflexivity. }
      rewrite <- (lt i j); try assumption.
      set (f := nat_rect _ _ _).
      revert iter1_lt_iter2.
      revert p. revert iter2p.
      rewrite <- iter1_eq_iter2.
      intros.
      apply maponpaths_3.
      apply proofirrelevance.
      apply propproperty.
  - intros lt i j i_lt_j.
    destruct (natlehchoice iter1 iter2) as [lt' | eq'].
    { apply natlthsntoleh in iter1_lt_iter2. assumption.  }
    + rewrite gauss_clear_column_inv5; try reflexivity; try assumption.
      intros i' j' i'_lt_j'.
      rewrite (IHiter2 (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) iter2p)
        lt' lt i' j' i'_lt_j').
      reflexivity.
    + rewrite gauss_clear_column_inv5; try reflexivity; try assumption.
      intros i' j' i'_lt_j'.
      rewrite <- (lt i' j'); try assumption.
      simpl in iter2p.
      revert iter1_lt_iter2.
      revert n0. revert iter2p.
      rewrite <- eq'.
      intros.
      change (S iter2 < S n) with (iter2 < n) in iter2p.
      set (f := nat_rect _ _ _).
      try rewrite <- eq'.
      apply maponpaths_3.
      intros.
      apply proofirrelevance.
      apply propproperty.
  Defined.

Lemma gauss_clear_columns_up_to_no_switch_inv4
  ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
  (iter : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
  (k : ⟦ n ⟧%stn) :
  (@gauss_clear_columns_up_to_no_switch n p iter mat) k k = mat k k.
Proof.
  destruct iter as [iter p''].
  pose (inv0 := gauss_clear_columns_up_to_no_switch_inv0).
  unfold is_lower_triangular in *.
  unfold gauss_clear_columns_up_to_no_switch in *.
  induction iter. { simpl. reflexivity. }
  rewrite nat_rect_step.
  destruct (isdeceqhq _ _).
  { rewrite IHiter; reflexivity. }
  destruct (natgthorleh k iter).
  2: { rewrite gauss_clear_column_inv3; try reflexivity; try assumption. apply IHiter. }
  rewrite gauss_clear_column_inv1. 2: { apply (pr2 k). }
  unfold gauss_clear_column_step'.
  destruct (stn_eq_or_neq _ _); try apply IHiter; try assumption.
  2: {assumption. }
  set (f := nat_rect _ _ _ _).
  set (s := (istransnatlth iter (S iter) (S n) (natgthsnn iter) p'')).
  unfold gauss_add_row; rewrite stn_eq_or_neq_refl; simpl.
  etrans.
  { apply maponpaths.
  destruct (natgthorleh k iter).
  - rewrite hqmultcomm; replace  (f s _ k) with 0%hq.
  {rewrite (@rigmult0x hq); reflexivity. }
  unfold f, s; change 0%rig with 0%hq in inv0.
  set (iter_stn := make_stn (S n ) iter (istransnatlth _ _ _ (natgthsnn iter) p'')).
  change iter with (pr1 iter_stn).
  rewrite (inv0 n _ p  (0,, natgthsn0 n)); try reflexivity; try assumption.
  - replace  (f s k _) with 0%hq.
  + etrans.
    { rewrite hqmultcomm; apply maponpaths; rewrite hqmultcomm; rewrite (@rigmultx0 hq).
      pose (riu1 := ringinvunel1 hq).
      change (- 0)%ring with (- 0)%hq in riu1; change 0%ring with 0%hq in riu1.
      change 0%rig with 0%hq; rewrite riu1; reflexivity.
    }
    rewrite (@rigmultx0 hq); reflexivity.
  + unfold f, s.
    change 0%rig with 0%hq in inv0.
    set (iter_stn := make_stn (S n ) iter (istransnatlth _ _ _ (natgthsnn iter) p'')).
    change iter with (pr1 iter_stn).
    rewrite (inv0 n _ p  (0,, natgthsn0 n)); try reflexivity; try assumption.
    destruct (natlehchoice k iter); try assumption.
    simpl in h. rewrite p0 in h.
    contradiction (isirreflnatgth _ h).
  }
  rewrite (@rigrunax1 hq).
  apply IHiter.
Admitted. (* TODO - WHY slow ?*)


Lemma gauss_clear_columns_up_to_no_switch_inv3
  ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
  (iter1 iter2 : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
  (i j : ⟦ n ⟧%stn)  (le' : i ≤ j)  (* (p'' : (mat k) = (const_vec 0%hq))*)
  :
  iter1 ≤ iter2
  -> (@gauss_clear_columns_up_to_no_switch n p iter1 mat ) i j = (0%hq)
  -> (@gauss_clear_columns_up_to_no_switch n p iter2 mat ) i j = (0%hq).
Proof.
  destruct (natlehchoice i j) as [lt | eq]. {try assumption.  }
  2: { intros le H.
  replace j with i in *. 2: {apply subtypePath_prop in eq. rewrite eq. reflexivity. }
  rewrite  gauss_clear_columns_up_to_no_switch_inv4 in *; try assumption. }
  intros le.
  destruct (natlehchoice iter1 iter2) as [lt' | eq]. {assumption. }
  2: { clear le. intros H. rewrite <- H. apply maponpaths_4. symmetry. apply subtypePath_prop. assumption. }
  clear le.
  destruct iter2 as [iter2 p2].
  intros H. revert H. revert lt. revert le'. revert i j.
  revert lt'; revert p'.
  unfold is_lower_triangular.
  induction iter2. (* generalize i j first ? *)
  { simpl. intros.  apply fromempty. apply nopathsfalsetotrue. assumption. (*apply p'. assumption.*) }
  intros lowt iter1_lt_siter2. intros i j. intros le. intros lt. intros H (*lt*).
  pose( inv0 := gauss_clear_columns_up_to_no_switch_inv0 ).
  unfold gauss_clear_columns_up_to_no_switch in *.
  assert (iter1_le_iter2 : iter1 ≤ iter2). {apply natlthsntoleh in iter1_lt_siter2. assumption. }
  rewrite nat_rect_step.
  destruct (isdeceqhq _ _).
  - destruct (natlehchoice iter1 iter2) as [lt' | eq]. {assumption. }
    + assert (iter1_lt_iter2 : iter1 < iter2). {assumption. }
      { rewrite (IHiter2 (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) p2)
          lowt iter1_lt_iter2  i j); try reflexivity; try assumption. }
    + symmetry. etrans.
      { rewrite <- H. reflexivity. }
      revert p0.  revert iter1_lt_siter2. revert lt. revert p2. rewrite <- eq.
      change (pr1 iter1) with (iter1).
      intros.
      apply maponpaths_3.
      apply propproperty.
    - rewrite gauss_clear_column_inv5; try reflexivity; try assumption.
      destruct (natlehchoice iter1 iter2) as [? | eq]. {assumption. }
      2: {unfold is_lower_triangular. intros i' j' ?.
        set (f := nat_rect _ _ _ _).
        set (s := (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) p2)).
        set (f' := f s).
        unfold f', f.
        try rewrite (inv0 n f' p iter1 (iter2,, s) iter1_le_iter2 lowt i' j').
        change 0%rig with 0%hq.
        set (iter2_stn := make_stn (S n) iter2 s).
        change (iter2) with (pr1 iter2_stn).
        rewrite (inv0 n  _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
      }
      intros i' j' lt''.
      destruct (natgthorleh i' j') as [gt | le'].
      + apply fromempty. apply isasymmnatlth in gt; try contradiction; assumption.
      + destruct (natlehchoice i' j') as [lt''' | eq]. {assumption. }
        * symmetry. etrans. { change 0%rig with 0%hq. rewrite <- H. reflexivity. } (* i' j' *)
          assert (iter1_lt_iter2 : iter1 < iter2). {assumption. }
          rewrite (IHiter2 (istransnatlth iter2 (S iter2) (S n) (natgthsnn iter2) p2) lowt iter1_lt_iter2 i' j'); try reflexivity; try assumption.
          unfold gauss_clear_columns_up_to_no_switch in inv0.
          destruct (natchoice0 n) as [? | gt].
          {rewrite p0 in p. apply isirreflnatgth in p. contradiction. }
          assert (obv'' : 0 < S n). {apply natgthsn0. }
          destruct (natchoice0 iter1) as [z | eqz].
          { rewrite (inv0 n _ p (0,, obv'')); try reflexivity; try assumption. }
          apply natlthtoleh in eqz.
          refine (inv0 n _ gt (0,, obv'') iter1 eqz _ _ _ _ ); assumption.
        * rewrite  (IHiter2); try reflexivity; try assumption.
          rewrite eq in lt''.
          apply isirreflnatlth in lt''.
          apply fromempty; assumption.
Defined.


(* This is in a way an invariant for a failure case during elimination;
if we have constructed an upper triangular matrix,
this matrix has an inverse iff it's lower triangular transpose has an inverse.
Working on the transpose, we can turn this into a diagonal matrix,
and if the input matrix to gccut is lower triangular with a 0 entry on the diagonal,
we can use elementary row operations to attain a matrix A' with a constant 0 row,
a witness to non-invertibility. *)
Lemma gauss_clear_columns_up_to_no_switch_inv2
  ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
  (iter : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
  (*(k : ⟦ n ⟧%stn) (p'' : mat k k = 0%hq)*)
  : coprod
  (∏ i j: ⟦ n ⟧%stn, j < iter ->  j < i
    -> (@gauss_clear_columns_up_to_no_switch n p iter mat) i j = 0%hq)
  (∑ i : ⟦ n ⟧%stn, (@gauss_clear_columns_up_to_no_switch n p iter mat) i = (const_vec 0%hq)).
Proof.
  destruct iter as [n' lt_n'_n].
  unfold const_vec.
  induction n'.
  { left.  simpl. intros. apply nopathsfalsetotrue in X. contradiction. }
  unfold gauss_clear_columns_up_to_no_switch in *.
  set (s :=  (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) ).
  pose (inv0 := gauss_clear_columns_up_to_no_switch_inv0).
  pose( inv4 :=  gauss_clear_columns_up_to_no_switch_inv4).
  destruct (IHn' s) as [IH1 | IH2].
  - rewrite nat_rect_step.
    destruct (isdeceqhq _ _).
    + right.
      use tpair.
      {exact  (n',, lt_n'_n). }
      apply funextfun. intros j.
      destruct (natgthorleh n' j) as [gt | le].
      * rewrite IH1; try reflexivity; try assumption.
      * destruct (natlehchoice n' j). {assumption. }
        -- unfold is_lower_triangular in inv0.
          unfold gauss_clear_columns_up_to_no_switch in inv0.
          set (n'_stn := (make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n))).
          change 0%rig with 0%hq in inv0.
          change n' with (pr1 n'_stn).
          rewrite (inv0 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
        -- pose (inv3 := gauss_clear_columns_up_to_no_switch_inv3).
          unfold gauss_clear_columns_up_to_no_switch in inv3.
          set (n_stn := make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) ).
          change n' with (pr1 n_stn).
          rewrite (inv3 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
          simpl. revert IH1. revert s. revert p0. revert n_stn. revert lt_n'_n. rewrite p1.
          intros.
          rewrite <- p0.
          apply maponpaths.
          apply subtypePath_prop.
          reflexivity.
    + left. intros i j ? ?.
      destruct (natlehchoice j n'). {apply natlthsntoleh in X.  assumption. }
      * symmetry. etrans. { rewrite <- (IH1 i j); try assumption. reflexivity. }
        rewrite gauss_clear_column_inv6; try reflexivity; try assumption.
        rewrite IH1; try reflexivity; try assumption.
      * rewrite gauss_clear_column_inv1; try assumption.
        3: { rewrite p0 in X0. apply X0. }
        2: {apply (pr2 i). }
        rewrite <- gauss_clear_column_step_eq.
        revert IH1. revert s. revert n0. revert X. revert lt_n'_n. rewrite <- p0.
        intros.
        simpl in lt_n'_n.
        replace (stntonat _ j,, lt_n'_n) with j.
        2: { revert X. revert n0. revert IH1. revert s. revert lt_n'_n.
            intros.
            set (rhs := stntonat n j,, lt_n'_n).
            assert (eq : pr1 j = pr1 rhs). { unfold rhs. reflexivity.  }
            rewrite  (subtypePath_prop   eq  ).
            reflexivity.
        }
        apply (gauss_clear_column_step_inv1 hq).
        2: { apply natgthtoneq. apply X0. }
        unfold gauss_clear_columns_up_to_no_switch in inv4.
        rewrite  (inv4 n _ p (pr1 j,,  (istransnatlth j (S j) (S n) (natgthsnn j) lt_n'_n))); try assumption.
        replace (stntonat _ j,, lt_n'_n) with j in n0; try assumption.
        unfold stntonat. change j with (pr1 j,, pr2 j).
        simpl.
        assert (eq :  (pr2 j) = lt_n'_n). { apply proofirrelevance. apply propproperty. }
        rewrite eq; reflexivity.
  - right.
    rewrite nat_rect_step.
    destruct IH2 as [IH2 IH2p].
    use tpair. {apply IH2.  }
    destruct (isdeceqhq _ _).
    + pose (inv3 := gauss_clear_columns_up_to_no_switch_inv3).
      unfold gauss_clear_columns_up_to_no_switch in * .
      set (n'_stn := make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n)).
      unfold const_vec in inv3.
      change n' with (pr1 n'_stn).
      apply funextfun; intros j.
      destruct (natgthorleh (pr1 IH2) j).
      * try rewrite (inv3 n'_stn). try rewrite IHn'. change (pr1 n'_stn) with n'. unfold s in IH2p.
        rewrite IH2p; reflexivity.
      * rewrite  (inv3 _ _ p n'_stn); try reflexivity; try assumption.
        {try apply isreflnatgeh. }
        destruct IH2 as [IH_idx IH_p].
        clear inv3.
        change n' with (pr1 n'_stn) in IH2p.
        change s with (pr2 n'_stn) in IH2p.
        change (pr1 (IH_idx,, IH_p)) with IH_idx.
        change (pr2 n'_stn) with lt_n'_n.
        try simpl in *; try rewrite IH2p; try apply idpath.
  + apply funextfun. intros j.
    destruct IH2 as [inv rw].
    destruct (natgthorleh n' inv).
    { rewrite gauss_clear_column_inv3.
      change (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) with s.
      rewrite IH2p; reflexivity.
      apply natgthtogeh.
      assumption.
    }
    destruct (natlehchoice n' inv) as [le | eq]. { assumption. }
    2: { rewrite gauss_clear_column_inv3.
        - change (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) with s.
          rewrite IH2p; reflexivity.
        - change (stntonat _ (inv,, rw )) with inv.
          change (stntonat _ (n',, lt_n'_n)) with n'.
          rewrite eq.
          apply isreflnatgeh.
    }
    rewrite gauss_clear_column_inv1.
    3: { apply le. }
    2: { simpl. assumption. }
    try rewrite gauss_clear_column_step_eq.
    unfold gauss_clear_column_step'.
    destruct (stn_eq_or_neq _ _).
    { change (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n) with s.
      try apply rw.
      revert IH2p.
      set (f := nat_rect  _ _ _).
      simpl; intros.
      rewrite IH2p; reflexivity.
    }
    unfold gauss_clear_columns_up_to_no_switch in *.
    set (n'_stn := make_stn (S n) n' (istransnatlth n' (S n') (S n) (natgthsnn n') lt_n'_n)).
    change n' with (pr1 n'_stn).
    unfold is_lower_triangular in *.
    set (f := nat_rect _  _ _ _).
    set (s' := istransnatlth _ _ _ _).
    set (f' := f (s' lt_n'_n)).
    unfold gauss_add_row.
    rewrite (stn_eq_or_neq_refl); rewrite coprod_rect_compute_1.
    replace (f' (inv,, rw) j) with 0%hq.
    2: { unfold f', f. change n' with (pr1 n'_stn) in IH2p.
        change s with (s' lt_n'_n) in IH2p. rewrite IH2p; reflexivity. }
    replace (f' (inv,, rw) (pr1 n'_stn,, lt_n'_n)) with 0%hq.
    2: {unfold f', f. change n' with (pr1 n'_stn) in IH2p.
        change s with (s' lt_n'_n) in IH2p. rewrite IH2p; reflexivity.  }
    rewrite (@riglunax1 hq).
    etrans. {apply maponpaths_2. apply maponpaths.  rewrite (@rigmult0x hq). apply idpath. }
    change 0%rig with 0%hq. replace (- 0)%hq with 0%hq.
    2: {try rewrite (@ringinvunel1 hq ).
        pose (eq := @ringinvunel1 hq).
        change 0%ring with 0%hq in eq.
        change (- 0%hq)%ring with ( - 0%hq)%hq in eq.
        rewrite eq.
        reflexivity.
    }
    rewrite hqmult0x.
    apply idpath.
Defined.

Lemma gauss_clear_columns_up_to_no_switch_inv5
  ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
  (iter : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
  (k : ⟦ n ⟧%stn) (p'' : mat k k = 0%hq) :
  k < iter ->
  ∑ i : ⟦ n ⟧%stn, (@gauss_clear_columns_up_to_no_switch n p iter mat) i = (const_vec 0%hq).
Proof.
  pose (inv2 := gauss_clear_columns_up_to_no_switch_inv2).
  pose (inv0 := gauss_clear_columns_up_to_no_switch_inv0).
  pose (inv3 := gauss_clear_columns_up_to_no_switch_inv3).
  pose (inv4 := gauss_clear_columns_up_to_no_switch_inv4).
  unfold gauss_clear_columns_up_to_no_switch in *.
  intros k_lt_iter.
  unfold gauss_clear_columns_up_to_no_switch.
  destruct iter as [iter lt].
  induction iter. {simpl. apply fromempty. apply negnatlthn0  in k_lt_iter. assumption. }
  rewrite nat_rect_step.
  set (s := (istransnatlth iter (S iter) (S n) (natgthsnn iter) lt)).
  destruct (natlehchoice k iter) as [? | eq]. {apply natlthsntoleh in k_lt_iter. assumption. }
  - destruct (IHiter s) as [IH_idx IH_p]. {assumption. }
  use tpair. {exact IH_idx. }
  destruct (isdeceqhq (mat (iter,, lt) (iter,, lt)) 0%hq).
  { apply IH_p. }
  apply funextfun. intros j.
  destruct (natgthorleh IH_idx j).
  + (*rewrite <- IH_p.*)
  set (iter_stn := (make_stn (S n) iter  (istransnatlth iter (n) (S n) lt (natgthsnn n)))).
  set (iter_stn' := (make_stn n iter lt)).
  change (iter,, lt) with iter_stn'.
  assert (obv : isaprop (hProptoType (iter < S n))). {apply propproperty. }
  replace s with (pr2 iter_stn).
  2: {unfold iter_stn.
      rewrite (proofirrelevance _ obv s
    ( pr2 (make_stn (S n) iter (istransnatlth iter n (S n) lt (natgthsnn n)))) ). reflexivity. }
  change iter with (pr1 iter_stn).
  try rewrite (inv4 iter_stn').
  destruct (natgthorleh IH_idx iter_stn').
  2: {rewrite gauss_clear_column_inv3; try assumption.
      change (pr1 iter_stn) with (stntonat _ iter_stn).
      assert (eq : (pr2 iter_stn) = s).
      { apply proofirrelevance; apply propproperty. }
      rewrite eq; rewrite <- IH_p.
      reflexivity.
  }
  rewrite gauss_clear_column_inv1; try assumption.
  2: {apply (pr2 IH_idx). }
  unfold gauss_clear_column_step'.
  destruct (stn_eq_or_neq _ _).
  { change (pr1 iter_stn) with (iter).
    assert (eq' : (pr2 iter_stn) = s). { apply proofirrelevance. apply propproperty. }
    rewrite eq'; rewrite IH_p.
    reflexivity.
  }
  unfold gauss_add_row.
  set (f := nat_rect _ _ _).
  rewrite (stn_eq_or_neq_refl); rewrite coprod_rect_compute_1.
  set (f' := f _ _).
  replace (f' IH_idx j) with 0%hq.
  2: { unfold f', f.
      change (pr1 iter_stn) with (iter).
      assert (eq' : (pr2 iter_stn) = s).
      { apply proofirrelevance. apply propproperty. }
      rewrite eq'. rewrite  IH_p.
      reflexivity.
  }
  replace (f' IH_idx iter_stn') with 0%hq.
  2: { unfold f', f.
      unfold f', f.
      change (pr1 iter_stn) with (iter).
      assert (eq' : (pr2 iter_stn) = s).
      { apply proofirrelevance. apply propproperty. }
      rewrite eq'. rewrite  IH_p.
      reflexivity.
  }
  rewrite (@riglunax1 hq).
  etrans. { apply maponpaths_2. apply maponpaths. rewrite hqmult0x. reflexivity. }
  etrans. {apply maponpaths_2. apply maponpaths.  apply idpath. }
  change 0%rig with 0%hq. replace (- 0)%hq with 0%hq.
  2: {try rewrite (@ringinvunel1 hq ).
      pose (eq := @ringinvunel1 hq).
      change 0%ring with 0%hq in eq.
      change (- 0%hq)%ring with ( - 0%hq)%hq in eq.
      rewrite eq.
      reflexivity.
  }
  rewrite hqmult0x. reflexivity.
  + destruct (natlehchoice IH_idx j). {assumption. }
  * rewrite  gauss_clear_column_inv5; try reflexivity; try assumption.
    unfold is_lower_triangular; intros.
    set (s' := ((istransnatlth iter (S iter) (S n) (natgthsnn iter) lt))).
    set (iter_stn := (make_stn (S n) iter s')).
    change iter with (pr1 iter_stn).
    change s with (pr2 iter_stn).
    rewrite (inv0 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
  * replace j with (IH_idx). 2: {apply subtypePath_prop in p0. rewrite p0.  reflexivity. }
    try rewrite inv4.
    destruct (natgthorleh IH_idx iter).
    2: {rewrite gauss_clear_column_inv3; try assumption.
        rewrite <- IH_p.
        reflexivity.
    }
    rewrite gauss_clear_column_inv1; try assumption.
    2: {apply (pr2 (IH_idx)). }
    unfold gauss_clear_column_step'.
    unfold gauss_add_row.
    set (f := nat_rect _ _ _).
    destruct (stn_eq_or_neq _ _).
    { rewrite <- IH_p. unfold f. reflexivity. }
    rewrite (stn_eq_or_neq_refl); rewrite coprod_rect_compute_1.
    set (f' := f _ _).
    replace (f' IH_idx (iter,, lt)) with 0%hq. 2: {unfold f'. unfold f. rewrite  IH_p. reflexivity. }
    replace (f' IH_idx IH_idx) with 0%hq. 2: {unfold f'. unfold f. rewrite  IH_p. reflexivity. }
    rewrite (@riglunax1 hq).
    etrans. {apply maponpaths_2.
            apply maponpaths.
            rewrite hqmult0x.
            reflexivity. }
    change 0%rig with 0%hq.
    replace (- 0)%hq with 0%hq.
    2: {try rewrite (@ringinvunel1 hq ).
        pose (eq := @ringinvunel1 hq).
        change 0%ring with 0%hq in eq.
        change (- 0%hq)%ring with ( - 0%hq)%hq in eq.
        rewrite eq.
    reflexivity. }
    rewrite hqmult0x.
    reflexivity.
  - revert k_lt_iter. revert s. revert lt. rewrite <- eq in *.
    intros.
    destruct (isdeceqhq _ _).
    2: {rewrite <- p'' in n0. replace (stntonat _ k,, lt) with k in n0.
      2: {change k with (pr1 k,, pr2 k) at 1.
          assert (eq'  : pr1 k = stntonat n k). {reflexivity. }
          revert s. revert k_lt_iter. revert n0. revert lt.
          change (stntonat n k) with (pr1 k).
          intros.
          assert (eq'' :  lt = (pr2 k)). {apply proofirrelevance; apply propproperty. }
          rewrite eq''.
          reflexivity.
      }
      contradiction.
    }
    destruct (inv2 n mat p (pr1 k,, s)) as [c1 | c2] ; try assumption.
    use tpair. {exact k. }
    apply funextfun. intros j.
    destruct (natgthorleh k j).
    { rewrite c1 ; try reflexivity; try assumption. }
    destruct (natlehchoice k j). {assumption. }
    + set (kstn := make_stn (S n) k (istransnatlth k (S k) (S n) (natgthsnn k) lt)).
      change (stntonat _ k) with (pr1 kstn).
      change s with (pr2 kstn).
      rewrite (inv0 n _ p (0,, natgthsn0 n)); try reflexivity; try assumption.
    + revert c1. revert s. revert k_lt_iter. revert p0. revert lt.
      replace k with j. 2 : {apply subtypePath_prop in p1. symmetry. rewrite p1. reflexivity.  }
      intros.
      set (j_stn := (make_stn (S n) j ( (istransnatlth j n (S n)  (pr2 j) (natgthsnn n) )))).
      change (stntonat _ j) with (pr1 j_stn).
      assert (eq' : s = (pr2 j_stn)). {apply proofirrelevance; apply propproperty. }
      rewrite eq'; rewrite inv4; try assumption.
      rewrite <- p0.
      unfold const_vec.
      apply maponpaths_12; try apply subtypePath_prop; try reflexivity.
Defined.

Lemma gauss_clear_columns_up_to_no_switch_as_matrix_eq  { n : nat } (iter : ⟦ S n ⟧%stn)
  (mat : Matrix hq n n) (p : n > 0) :
  ((@clear_columns_up_to_no_switch_as_left_matrix _ p iter mat) ** mat)
  = (gauss_clear_columns_up_to_no_switch p iter mat).
Proof.
  intros.
  unfold clear_columns_up_to_no_switch_as_left_matrix, gauss_clear_columns_up_to_no_switch,
        clear_columns_up_to_no_switch_as_left_matrix_internal.
  destruct iter as [iter p'].
  induction iter. {simpl. rewrite matlunax2. apply idpath. }
  do 2 rewrite nat_rect_step.
  unfold clear_columns_up_to_no_switch_as_left_matrix_internal in *.
  rewrite <- IHiter.
  set (inner_expr := nat_rect _ _ _ _).
  rewrite <- clear_column_eq_matrix_def.
  repeat rewrite matrix_mult_assoc.
  destruct (isdeceqhq _ _).
  - reflexivity.
  - rewrite matrix_mult_assoc.
    rewrite IHiter; reflexivity.
Defined.

Lemma clear_columns_up_to_no_switch_matrix_invertible {n : nat} (iter : ⟦ S n ⟧%stn)
  (H : n > 0) (mat : Matrix hq n n)
  : @matrix_inverse hq _  (clear_columns_up_to_no_switch_as_left_matrix H iter mat).
Proof.
  unfold clear_columns_up_to_no_switch_as_left_matrix,
    clear_columns_up_to_no_switch_as_left_matrix.
  destruct iter as [iter iter_lt].
  induction iter as [| iter IH].
  - simpl. apply identity_matrix_is_inv.
  - unfold clear_columns_up_to_no_switch_as_left_matrix,
      clear_columns_up_to_no_switch_as_left_matrix_internal.
    rewrite nat_rect_step.
    destruct (isdeceqhq _ _).
    + apply IH.
    + apply inv_matrix_prod_is_inv; try assumption.
      * apply clear_column_matrix_invertible.
      * apply IH.
  Defined.

Lemma gauss_clear_columns_up_to_no_switch_inv6
  ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
  (iter : ⟦ S n ⟧%stn) (p' : @is_lower_triangular hq n n mat)
  (k : ⟦ n ⟧%stn) (p'' : mat k k = 0%hq) :
  k < iter ->
  (@matrix_right_inverse hq n n mat) -> empty.
Proof.
  intros lt contr_inv1.
  assert (forall m' : Matrix hq n n,
    (@matrix_right_inverse hq n n m') -> matrix_right_inverse (mat ** m')).
  { intros. apply right_inv_matrix_prod_is_right_inv; try assumption. }
  pose (C := @clear_columns_up_to_no_switch_as_left_matrix n p (n,, natgthsnn n) mat).
  assert (contr_inv2 : @matrix_right_inverse hq n n C).
  { pose (H := @clear_columns_up_to_no_switch_matrix_invertible n (n,, natgthsnn n) p mat).
    apply matrix_inverse_to_right_and_left_inverse in H.
    apply H.
  }
  assert (contr_inv3 : @matrix_right_inverse hq n n (C ** mat)).
  {apply right_inv_matrix_prod_is_right_inv; assumption. }
  pose (H2 := gauss_clear_columns_up_to_no_switch_inv5 n mat p (n,, natgthsnn n)
    p' k p'' (pr2 k)).
  rewrite <- gauss_clear_columns_up_to_no_switch_as_matrix_eq in H2.
  apply (zero_row_to_non_right_invertibility (C ** mat) (pr1 H2)); try assumption.
  unfold C.
  destruct H2 as [H2 H3].
  apply H3.
Defined.

Lemma gauss_clear_columns_up_to_no_switch_inv7
  ( n : nat ) (mat : Matrix hq n n) (p : n > 0)
  (iter : ⟦ S n ⟧%stn) (p' : @is_upper_triangular hq n n mat)
  (k : ⟦ n ⟧%stn) (p'' : mat k k = 0%hq) :
  k < iter ->
  (@matrix_left_inverse hq n n mat) -> empty.
Proof.
  intros lt contr_inv1.
  apply (gauss_clear_columns_up_to_no_switch_inv6 n (transpose mat)
    p iter (upper_triangular_transpose_is_lower_triangular mat p') k); try assumption.
  apply (matrix_left_inverse_to_transpose_right_inverse _ contr_inv1).
Defined.
