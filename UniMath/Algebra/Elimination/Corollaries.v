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
Require Import UniMath.Tactics.Nat_Tactics.

Require Import UniMath.PAdics.z_mod_p.
Require Import UniMath.PAdics.lemmas.

Require Import UniMath.RealNumbers.Prelim.

Require Import UniMath.Algebra.Elimination.Auxiliary.
Require Import UniMath.Algebra.Elimination.Vectors.
Require Import UniMath.Algebra.Elimination.Matrices.
Require Import UniMath.Algebra.Elimination.RowOps.
Require Import UniMath.Algebra.Elimination.Elimination.

(** 
  In this module, we define a back-substitution procedure that works on
  nxn matrices that are upper triangular with all non-zero diagonal.

  We use this procedure to show that any nxn matrix either not invertible,
  or calculate its inverse.
*)

Definition matrix_inverse_or_non_invertible_stmt
  { n : nat } {F : fld}
  (A : Matrix F n n)
  := coprod (@matrix_inverse F n A)
            (@matrix_inverse F n A -> empty).

Definition back_sub_stmt
  { n : nat } {F : fld}
  (mat : Matrix F n n)
  (vec : Vector F n)
  (ut : @is_upper_triangular F _ _ mat)
  (df : @diagonal_all_nonzero F _ mat)
  := ∑ f : (Matrix F n n -> Vector F n -> Vector F n),
    (@matrix_mult F _ _ mat _ (col_vec (f mat vec))) = (col_vec vec).


  (* TODO upstream? *)
  Local Lemma stn_eq
    {k : nat} (i j : stn k) (eq : pr1 i = pr1 j) : i = j.
  Proof.
    apply subtypePath_prop; assumption.
  Defined.

  Local Lemma stn_eq_2
    {k : nat} (i: stn k) (j : nat) (eq : pr1 i = j) : forall P : j < k, i = (j,, P).
  Proof.
    intros lt; apply subtypePath_prop; assumption.
  Defined.

  Local Lemma stn_eq_3
    {k : nat} (i: nat) (j : stn k) (eq : i = pr1 j) : forall P : i < k, j = (i,, P).
  Proof.
    apply stn_eq_2; symmetry; assumption.
  Defined.


Section BackSub.

  Context (F : fld).

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* output: a solution [x] to [mat ** x = b] (if one exists?) *)
  (* TODO: what conditions on [mat] are needed to ensure this is a solution? *)
  Definition back_sub_step { n : nat } ( row : (⟦ n ⟧)%stn )
    (mat : Matrix F n n) (x : Vector F n) (b : Vector F n) : Vector F n.
  Proof.
    intros i.
    destruct (nat_eq_or_neq row i) as [? | ?].
    - exact (((b i) * fldmultinv' (mat i i))
           - ((Σ (mat i ^ x)  - (x  i)* (mat i i))
           * (fldmultinv' (mat i i))))%ring.
    - exact (x i).
  Defined.

  Lemma back_sub_step_inv0 { n : nat }
    (row : ⟦ n ⟧%stn) (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (p: @is_upper_triangular F n n mat)
    (p' : ((mat row row != 0)%ring))
    : (mat ** (col_vec (back_sub_step row mat x b))) row = (col_vec b) row.
  Proof.
    intros.
    unfold back_sub_step, col_vec.
    unfold fldmultinv'.
    rewrite matrix_mult_eq; unfold matrix_mult_unf, pointwise.
    set (m := n - (S row)).
    assert (split_eq : n = (S row) + m).
    { unfold m.
      rewrite natpluscomm, minusplusnmm.
      - apply idpath.
      - simpl. exact (pr2 row). }
    destruct (stn_inhabited_implies_succ row) as [s_row s_row_eq].
    destruct (!s_row_eq).
    apply funextfun; intros ?.
    rewrite (@rigsum_dni F (s_row) _ row).
    rewrite nat_eq_or_neq_refl.
    destruct (fldchoice0 _) as [contr0 | neq].
    {contradiction. }
    etrans.
    { apply maponpaths_2; apply maponpaths.
      apply funextfun. intros q.
      unfold funcomp.
      rewrite (nat_eq_or_neq_right (dni_neq_i row q)).
      reflexivity. }
    rewrite (@rigsum_dni F (s_row)  _ row).
    etrans.
    { apply maponpaths.
      etrans.
      { apply maponpaths.
        rewrite (@ringcomm2 F).
        apply maponpaths.
        rewrite (@ringcomm2 F).
        reflexivity. }
      apply (@ringminusdistr F (mat row row)).
    }
    etrans.
    { apply maponpaths; apply map_on_two_paths.
      rewrite <- (@rigassoc2 F), (@fldmultinvrax F).
      { rewrite (@riglunax2 F); reflexivity. }
      apply maponpaths.
      rewrite <- (@rigassoc2 F), (@fldmultinvrax F).
      apply (@riglunax2 F). }
    etrans.
    { do 3 apply maponpaths.
      rewrite (@rigcomm2 F), (@fldplusminus F).
      reflexivity. }
    rewrite (@rigcomm1 F); rewrite (@rigassoc1 F).
    rewrite (@ringlinvax1 F), (@rigrunax1 F).
    apply idpath.
  Defined.

  Lemma back_sub_step_inv1
    { n : nat } (row : ⟦ n ⟧%stn)
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    : ∏ i : ⟦ n ⟧%stn, i ≠ row ->
      (col_vec (back_sub_step row mat b vec) i = ((col_vec b)) i).
  Proof.
    intros i ne.
    unfold back_sub_step, col_vec.
    apply funextfun. intros j; simpl.
    destruct (nat_eq_or_neq row i) as [eq | ?];
      try apply idpath.
    rewrite eq in ne.
    contradiction (isirrefl_natneq _ ne).
  Defined.

  Lemma back_sub_step_inv2 
    { n : nat }
    (row : ⟦ n ⟧%stn)
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (is_ut: @is_upper_triangular F n n mat)
    : ∏ i : ⟦ n ⟧%stn,
        i ≥ row
    -> (mat i i != 0)%ring
    -> (mat ** (col_vec b )) i = (col_vec vec) i
    -> (mat ** (col_vec (back_sub_step row mat b vec))) i = ((col_vec vec) i).
  Proof.
    unfold transpose, flip.
    intros i le neq0 H.
    rewrite <- H.
    destruct (natlehchoice row i) as [lt | eq]. {apply le. }
    - rewrite matrix_mult_eq in *.
      apply pathsinv0.
      rewrite matrix_mult_eq in *.
      unfold matrix_mult_unf in *.
      apply funextfun; intros ?.
      apply maponpaths, funextfun; intros i'.
      destruct (stn_eq_or_neq i' (row)) as [eq | neq].
      2 : { rewrite back_sub_step_inv1; try assumption; reflexivity. }
      replace (mat i i') with (@ringunel1 F).
      2 : { rewrite is_ut; try reflexivity. rewrite eq; assumption. }
      do 2 rewrite (@rigmult0x F); reflexivity.
    - revert le.
      intros.
      rewrite (stn_eq _ _ eq).
      rewrite back_sub_step_inv0; try assumption.
      rewrite H.
      reflexivity.
  Defined.

  Lemma back_sub_step_inv3
    { n : nat }
    (row : ⟦ n ⟧%stn)
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (is_ut : @is_upper_triangular F n n mat)
    : ∏ i : ⟦ n ⟧%stn, row < i
      -> (mat ** (col_vec b )) i
      = (mat ** (col_vec (back_sub_step row mat b vec))) i.
  Proof.
    intros i lt.
    unfold transpose, flip in *.
    destruct (natlehchoice row i (natlthtoleh _ _ lt)) as [? | eq].
    2: { rewrite <- eq in lt.
         apply isirreflnatgth in lt. contradiction. }
    rewrite matrix_mult_eq.
    apply pathsinv0.
    rewrite matrix_mult_eq.
    unfold matrix_mult_unf.
    apply funextfun; intros ?.
    apply maponpaths, funextfun; intros i'.
    destruct (stn_eq_or_neq i' row) as [eq | neq].
    2: { rewrite back_sub_step_inv1; try assumption; reflexivity. }
    replace (mat i i') with (@ringunel1 F).
    { do 2 rewrite (@rigmult0x F); reflexivity. }
    rewrite is_ut; try reflexivity.
    rewrite eq.
    assumption.
  Defined.

  Definition back_sub_internal
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (row : ⟦ S n ⟧%stn)
    : Vector F n.
  Proof.
    destruct row as [row p].
    induction row as [ | m IHn] .
    - exact x.
    - refine (back_sub_step (dualelement (m,, p)) mat (IHn _) b).
      apply (istransnatlth _ _ _ (natgthsnn m) p).
  Defined.

  (* Alternate version, serving different proof purpose *)
  Definition back_sub_internal'
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (sep : ⟦ S n ⟧%stn)
    (row : stn n)
    : Vector F n.
  Proof.
    destruct sep as [sep p].
    induction sep as [ | m IHn] .
    - exact x.
    - destruct (natlthorgeh (dualelement (m,, p)) row).
      + refine (back_sub_step (dualelement (m,, p)) mat (IHn _) b).
        apply (istransnatlth _ _ _ (natgthsnn m) p).
      + exact x.
  Defined.

  Definition back_sub
    {n : nat}
    (mat : Matrix F n n)
    (vec : Vector F n)
    := back_sub_internal mat vec vec (n,, natgthsnn n).

  Lemma dualelement_lt_trans_2
    {m n k q: nat} (p1 : n < k ) (p2 : n < q) (p3 : k < q)
    (lt_dual : m < dualelement (n,, p1))
    : (m < (dualelement (n,, p2))).
  Proof.
    unfold dualelement.
    destruct (natchoice0 _) as [eq | ?].
    - rewrite <- eq in p3.
      contradiction (negnatgth0n _ p3).      
    - simpl.
      refine (istransnatlth _ _ _ _ _).
      {exact lt_dual. }
      unfold dualelement.
      destruct (natchoice0 _) as [contr_eq | ?].
      + apply fromempty.
        clear lt_dual.
        rewrite <- contr_eq in p1.
        contradiction (negnatgth0n _ p1).
      + simpl.
        do 2 rewrite natminusminus.
        apply natlthandminusl; try assumption.
        refine (natlehlthtrans _ _ _ _ _).
        * rewrite natpluscomm.
          apply natlthtolehp1.
          exact p1.
        * assumption.
  Defined.
      
  Lemma dualelement_sn_eq
    {m n k q: nat} (lt : S n < S k)
    : pr1 (dualelement (n,, lt)) = (pr1 (dualelement (S n,, lt))).
  Proof.
    unfold dualelement.
    destruct (natchoice0 _) as [eq | ?].
    - apply fromempty.
      rewrite <- eq in lt.
      simpl in lt.
      contradiction (nopathsfalsetotrue).
    - destruct (natchoice0 _).
      + simpl.
        rewrite natminuseqn.
        rewrite natminusminus.
        reflexivity.
      + simpl.
        rewrite natminuseqn.
        rewrite natminusminus.
        reflexivity.
  Defined.

  Lemma dualelement_sn_le
    {m n k q: nat} (lt : S n < S k)
    : pr1 (dualelement (n,, lt)) <= (pr1 (dualelement (S n,, lt))).
  Proof.
    rewrite (@dualelement_sn_eq n n k k lt).
    apply isreflnatleh.
  Defined.

  Lemma dualelement_sn_le_2
  {m n k q: nat} (lt : S n < S k)
  : pr1 (dualelement (n,, lt)) >= (pr1 (dualelement (S n,, lt))).
  Proof.
    rewrite (@dualelement_sn_eq n n k k lt).
    apply isreflnatleh.
  Defined.


  Lemma dualelement_gt_sn
    {m n k q: nat} (lt : S k < S n)
    (gt_dual : m > dualelement (S k,, lt))
    : (m > (dualelement (k,, lt))).
  Proof.
    unfold dualelement.
    destruct (natchoice0 _) as [eq | ?].
    - apply fromempty.
      clear gt_dual.
      rewrite <- eq in lt.
      contradiction nopathsfalsetotrue.
    - simpl.
      refine (istransnatgth _ _ _ _ _).
      {exact gt_dual. }
      unfold dualelement.
      destruct (natchoice0 _) as [contr_eq | ?].
      + apply fromempty.
        clear gt_dual.
        simpl in lt.
        contradiction (negpaths0sx _ contr_eq).
      + simpl.
        rewrite minus0r.
        rewrite natminusminus.
  Abort.

  Lemma dualelement_sn_stn_nge_0
   {n : nat} (i : stn n)
   : forall lt : (0 < S n), i >= (dualelement (0,, lt)) -> empty.
  Proof.
    intros lt gt.
    unfold dualelement in gt.
    destruct (natchoice0 (S n)) as [contreq0 | ?] in gt.
    {apply fromempty. clear gt. apply negpaths0sx in contreq0; contradiction. }
    unfold make_stn in gt.
    destruct (natchoice0 n) as [contr_eq | ?].
    {simpl. apply fromstn0. rewrite contr_eq. assumption. }
    rewrite coprod_rect_compute_2 in gt.
    simpl in gt.
    do 2 rewrite minus0r in gt.
    pose (contr := pr2 i); simpl in contr.
    change (stntonat _ i) with (pr1 i) in gt.
    apply natgthtonegnatleh in contr.
    simpl in contr.
    contradiction.
  Defined.

  Lemma back_sub_internal_inv0
    { n : nat }
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (row : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < (dualelement row)
    -> (((col_vec (back_sub_internal mat b vec row)))) i = ((col_vec b) i).
  Proof.
    destruct row as [row p].
    induction row as [| row IH].
    { intros i H.
      destruct (natchoice0 (S n)) as [contr_eq | gt] in H.
      { clear H. apply negpaths0sx in contr_eq. contradiction. }
      reflexivity.
    }
    unfold back_sub_internal.
    intros i i_lt_dual.
    rewrite nat_rect_step.
    assert (p': row < S n). { apply (istransnatlth _ _ _ (natgthsnn row) p). }
    rewrite <- (IH p'); try assumption.
    rewrite back_sub_step_inv1; try reflexivity; try assumption.
    (* TODO factor this part out *)
    3:  { apply (natlthlehtrans _ _ _ i_lt_dual), dualelement_le_comp, natlehnsn. }
    2 : { apply natlthtoneq.
          apply (natlthlehtrans _ _ _ i_lt_dual).
          apply (@dualelement_sn_le_2 row row n n).
    }
    unfold back_sub_internal.
    apply maponpaths_2, maponpaths, proofirrelevance, propproperty.
  Defined.

  Lemma back_sub_internal_inv0'
    { n : nat }
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (sep : ⟦ S n ⟧%stn)
    (row : stn n)
    : ∏ (i : ⟦ n ⟧%stn), i >= row
    -> (((col_vec (back_sub_internal' mat b vec sep row)))) i = ((col_vec b) i).
  Proof.
    destruct sep as [sep p].
    induction sep as [| sep IH].
    { intros i H.
      destruct (natchoice0 (S n)) as [contr_eq | gt] in H.
      { clear H. apply negpaths0sx in contr_eq. contradiction. }
      reflexivity.
    }
    unfold back_sub_internal'.
    intros i i_lt_row.
    rewrite nat_rect_step.
    destruct (natlthorgeh _ _) as [lt | geh].
    2: {reflexivity. }
    assert (p': sep < S n). { apply (istransnatlth _ _ _ (natgthsnn sep) p). }
    rewrite <- (IH p'); try assumption.
    unfold back_sub_internal'.
    rewrite back_sub_step_inv1; try reflexivity; try assumption.
    (* TODO factor this part out *)
    { apply maponpaths_2. apply maponpaths. apply proofirrelevance, propproperty. }
    apply natgthtoneq.
    refine (natlthlehtrans _ _ _ _ _).
    {exact lt. }
    assumption.
  Defined.

  Lemma back_sub_internal_inv1
    { n : nat }
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (sep : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < (dualelement sep)
    -> ((((back_sub_internal mat b vec sep)))) i = (b i).
  Proof.
    intros.
    pose (eq := @col_vec_inj_pointwise F n (back_sub_internal mat b vec sep) (b) i).
    rewrite eq.
    {apply idpath. }
    apply (back_sub_internal_inv0); assumption.
  Defined.

  Lemma back_sub_internal_inv1'
    { n : nat }
    (mat : Matrix F n n)
    (b : Vector F n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (sep : ⟦ S n ⟧%stn)
    (row : stn n)
    : ∏ i : stn n, i >= row
    -> ((back_sub_internal' mat b vec sep row)) i = b i.
  Proof.
    intros.
    pose (eq := @col_vec_inj_pointwise F n (back_sub_internal' mat b vec sep row) (b) i).
    rewrite eq.
    {apply idpath. }
    apply (back_sub_internal_inv0'); try assumption.
  Defined.

  Lemma back_sub_internal_inv2
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (row : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i ≥ (dualelement row)
    -> (mat i i != 0)%ring
    -> (mat ** (col_vec (back_sub_internal mat x b row))) i = (col_vec b) i.
  Proof.
    unfold transpose, flip.
    intros i i_le_row neq0.
    unfold back_sub_internal.
    destruct row as [row p].
    induction row as [| row IH].
    { apply fromempty, (dualelement_sn_stn_nge_0 _ _ i_le_row). }
    rewrite nat_rect_step.
    destruct (natlehchoice (dualelement (row,, p)) (i)) as [leh | eq].
    { refine (istransnatleh _ i_le_row).
       apply (@dualelement_sn_le row row n n).
      }
    - rewrite back_sub_step_inv2; try reflexivity; try assumption.
      { unfold dualelement. unfold dualelement in leh.
        destruct (natchoice0 n) as [contr_eq | ?].
        {apply fromstn0. rewrite contr_eq. assumption. }
        rewrite coprod_rect_compute_2 in *.
        apply natgthtogeh; assumption. }
      rewrite IH; try reflexivity.
      { unfold dualelement.
        destruct (natchoice0 (S n)) as [contr_eq | gt] in *.
        { pose (contr := (natneq0sx n)). rewrite <- contr_eq in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2.
        unfold dualelement in leh.
        destruct (natchoice0 n) as [eq | gt']. {apply fromstn0. rewrite eq. assumption. }
        rewrite coprod_rect_compute_2 in *.
        simpl; simpl in leh.
        rewrite minus0r.
        apply natgthtogehsn in leh.
        rewrite pathssminus in leh.
        2: { rewrite pathssminus.
             - rewrite minussn1; exact p.
             - simpl; apply gt'. }
        assert (e : n = S (n - 1)).
        { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
          apply pathsinv0. apply minusplusnmm. assumption. }
        rewrite <- e in leh.
        apply leh. }
    - replace (dualelement (row,, p)) with i.
      { rewrite back_sub_step_inv0; try reflexivity; try assumption. }
      destruct (natchoice0 n) as [eq0 | gt]. {apply fromstn0. rewrite eq0. assumption. }
      unfold stntonat in eq.
      pose (subtype_eq := @subtypePath_prop _ _ _ _ eq).
      rewrite <- (@subtypePath_prop _ _ _ _ eq).
      reflexivity.
  Defined.

  Lemma back_sub_internal_inv2'
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (sep : ⟦ S n ⟧%stn)
    (row : stn n)
    : ∏ (i : ⟦ n ⟧%stn), i ≥ (dualelement sep)
    -> (mat i i != 0)%ring
    -> i < row
    -> (mat ** (col_vec (back_sub_internal' mat x b sep row))) i = (col_vec b) i.
  Proof.
    unfold transpose, flip.
    intros i i_le_sep neq0 lt.
    unfold back_sub_internal'.
    destruct sep as [sep p].
    induction sep as [| sep IH].
    { apply fromempty, (dualelement_sn_stn_nge_0 _ _ i_le_sep). }
    rewrite nat_rect_step.
    destruct (natlehchoice (dualelement (sep,, p)) (i)) as [leh | eq].
    { refine (istransnatleh _ i_le_sep).
      apply (@dualelement_sn_le); try assumption. }
    - destruct (natlthorgeh _ _) as [? | contr_geh].
      2 : { apply fromempty.
            pose (lt' := (istransnatlth _ _ _ leh lt)).
            pose (contr_lt := (natlthlehtrans _ _ _ lt' contr_geh)).
            contradiction (isirreflnatlth _ contr_lt).
      }
      rewrite back_sub_step_inv2; try reflexivity; try assumption.
      { unfold dualelement. unfold dualelement in leh.
        destruct (natchoice0 n) as [contr_eq | ?]. {apply fromstn0. rewrite contr_eq. assumption. }
        rewrite coprod_rect_compute_2 in *.
        apply natgthtogeh; assumption. }
      rewrite IH; try reflexivity.
      { unfold dualelement.
        destruct (natchoice0 (S n)) as [contr_eq | gt] in *.
        { pose (contr := (natneq0sx n)). rewrite <- contr_eq in contr.
          apply isirrefl_natneq in contr. contradiction. }
        rewrite coprod_rect_compute_2.
        unfold dualelement in leh.
        destruct (natchoice0 n) as [eq | gt']. {apply fromstn0. rewrite eq. assumption. }
        rewrite coprod_rect_compute_2 in *.
        simpl; simpl in leh.
        rewrite minus0r.
        apply natgthtogehsn in leh.
        rewrite pathssminus in leh.
        2: { rewrite pathssminus.
             - rewrite minussn1; exact p.
             - simpl; apply gt'. }
        assert (e : n = S (n - 1)).
        { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
          apply pathsinv0. apply minusplusnmm. assumption. }
        rewrite <- e in leh.
        apply leh. }
    - destruct (natlthorgeh _ _) as [? | contr_geh].
      2 : { rewrite <- (stn_eq _ _ eq) in lt.
            apply fromempty.
            pose (contr_lt := (natlthlehtrans _ _ _ lt contr_geh)).
            contradiction (isirreflnatlth _ contr_lt). }
      replace (dualelement (sep,, p)) with i.
      { rewrite back_sub_step_inv0; try reflexivity; try assumption. }
      destruct (natchoice0 n) as [eq0 | gt]. {apply fromstn0. rewrite eq0. assumption. }
      unfold stntonat in eq.
      pose (subtype_eq := @subtypePath_prop _ _ _ _ eq).
      rewrite <- (@subtypePath_prop _ _ _ _ eq).
      reflexivity.
  Defined.

  Lemma back_sub_inv0
    { n : nat }
    (mat : Matrix F n n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (df : @diagonal_all_nonzero F _ mat)
    : back_sub_stmt mat vec ut df.
  Proof.
    unfold back_sub_stmt.
    use tpair. {exact back_sub. }
    intros; unfold back_sub.
    destruct (natchoice0 n) as [eq0 | ?].
    { apply funextfun. intros i. apply fromstn0. rewrite eq0. simpl. assumption. }
    apply funextfun; intros i.
    apply back_sub_internal_inv2; try assumption; unfold dualelement.
    destruct (natchoice0 (S n)) as [p | ?]. { apply fromempty. apply negpaths0sx in p. assumption. }
    simpl; rewrite minus0r, minusnn0; reflexivity.
    apply df.
  Defined.

  (* inline *)
  Lemma back_sub_inv0'
    { n : nat }
    (mat : Matrix F n n) (vec : Vector F n)
    (ut : @is_upper_triangular F _ _ mat)
    (df : @diagonal_all_nonzero F _ mat)
    : (@matrix_mult F _ _ mat _ (col_vec (back_sub mat vec))) = (col_vec vec).
  Proof.
    apply (back_sub_inv0 _ _ ut df).
  Defined.

End BackSub.

Section BackSubZero.

  Context {F : fld}.

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Local Notation "0" := (@ringunel1 F).

  (* TODO might be a dupe in Vectors *)

  Local Lemma col_vec_inj_pointwise { X : rig } { n : nat } (v1 v2 : Vector X n)
    : forall i : (stn n), (col_vec v1 i) = (col_vec v2 i) -> (v1 i) = (v2 i).
  Proof.
    intros i eq.
    apply (invmaponpathsweq (@weq_vector_1 X)  _ _ eq).
  Defined.

  Lemma vector_1_inj { X : rig } { n : nat } (e1 e2 : X)
    : (λ y : (⟦ 1 ⟧)%stn, e1) = (λ y : (⟦ 1 ⟧)%stn, e2) -> e1 = e2.
  Proof.
    intros eq.
    apply (invmaponpathsweq (@weq_vector_1 X)  _ _ eq).
  Defined.

  (* End possible dupe *)

  Definition back_sub'
    { n : nat }
    (mat : Matrix F n n)
    (x : Vector F n) (b : Vector F n)
    (row : stn n)
    : Vector F n.
  Proof.
    intros j.
    destruct (natlthorgeh row j).
    - exact (back_sub_internal _ mat x b (n,, natgthsnn n) j).
    - exact (x j).
  Defined.

  (* A0 = 0 *)
  Local Lemma A0 {R : rig} {m n : nat} {mat : Matrix R m n}
  : (@matrix_mult R _ _ mat _
    (col_vec (const_vec (@rigunel1 R))))
      = (col_vec (const_vec (@rigunel1 R))).
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    apply funextfun; intros i.
    unfold col_vec.
    apply funextfun; intros _.
    rewrite zero_function_sums_to_zero;
      try reflexivity.
    unfold const_vec.
    apply funextfun; intros k.
    apply rigmultx0.
  Defined.

  Local Lemma matrix_mult_eq_left:
    ∏ {R : rig} {m n : nat} (mat1 : Matrix R m n)
    {p : nat} (mat2 : Matrix R n p) (mat3 : Matrix R n p),
    mat2 = mat3 -> 
    ((@matrix_mult R m n mat1 p mat2)) = (@matrix_mult R m n mat1 p (mat3)).
  Proof.
    intros ? ? ? ? ? ? ? eq.
    rewrite eq.
    reflexivity.
  Defined.

  (* A better proof of that in EliminationAlts.v, and should replace that file when finished. 
     TODO rename *)
  Lemma back_sub_zero
    { n : nat }
    (mat : Matrix F n n)
    (ut : @is_upper_triangular F _ _ mat)
    (zero: ∑ i : stn n, (mat i i = 0)%ring
      × (forall j : stn n, j < i -> ((mat j j) != 0)%ring))
    (inv : @matrix_left_inverse F _ _ mat)
    : empty.
  Proof.
    unfold transpose, flip.
    destruct (natchoice0 (pr1 zero)) as [eq0_1 | gt].
    { apply (zero_row_to_non_right_invertibility (transpose mat) (pr1 zero)); try assumption.
      apply funextfun; intros k.
      destruct (natchoice0 k) as [eq0_2 | ?].
      - rewrite <- (pr1 (pr2 zero)).
        unfold const_vec.
        rewrite eq0_1 in eq0_2.
        rewrite (stn_eq _ _ eq0_2).
        apply idpath.
      - unfold transpose, flip.
        rewrite ut; try reflexivity.
        rewrite <- eq0_1.
        assumption.
      - apply matrix_left_inverse_to_transpose_right_inverse.
        assumption.
    }
    assert (contr_exists :  ∑ x : (Vector F n), (∑ i' : stn n,
      (x i' != 0) × ((mat ** (col_vec x)) = (@col_vec F _ (const_vec 0)) ))).
    2: { assert (eqz : (mat ** (@col_vec F _ (const_vec 0))) = (@col_vec F _ (const_vec 0))).
        { rewrite matrix_mult_eq; unfold matrix_mult_unf.
          apply funextfun; intros k.
          unfold col_vec, const_vec.
          etrans.
          { rewrite zero_function_sums_to_zero.
            - apply idpath.
            - apply funextfun; intros ?; apply rigmultx0. }
          reflexivity.
        }
        assert (contr_eq' : ((@ringunel1 F) != (@ringunel1 F))).
        - rewrite <- eqz in contr_exists.     
          destruct contr_exists as [x1 contr_exists].
          destruct contr_exists as [x2 contr_exists].
          destruct contr_exists as [x3 contr_exists].
          destruct inv as [inv isinv].
          rewrite <- contr_exists in eqz.
          pose (eq := matrix_mult_eq_left inv _ _  eqz).
          rewrite <- matrix_mult_assoc in eq.
          rewrite isinv in eq.
          rewrite matlunax2 in eq.
          pose (eq' := @A0 F _ _ inv).
          symmetry in eq.
          change 0%ring with (@rigunel1 F) in *.
          unfold col_vec, const_vec in *.
          rewrite eq' in eq.
          destruct zero as [zero iszero].
          apply toforallpaths in eq.
          set (idx0 := (make_stn _ 0 (stn_implies_ngt0 (zero)))).
          assert (contr_eq' :
            ((λ (_ : (⟦ n ⟧)%stn) (_ : (⟦ 1 ⟧)%stn), (@rigunel1 F)) (idx0)) =
            ((λ (i : (⟦ n ⟧)%stn) (_ : (⟦ 1 ⟧)%stn), x1 x2) (idx0))
          ).
          { rewrite <- eq. reflexivity. }
          simpl in contr_eq'.
          apply toforallpaths in contr_eq'.
          change 0%rig with (@rigunel1 F) in *.
          rewrite contr_eq' in x3.
          2: { exact (make_stn _ _ (natgthsnn 0)). }
          contradiction.
      - contradiction.
    }
    destruct zero as [zero iszero].
    use tpair.
    { apply back_sub_internal'.
      - exact mat.
      - intros j.
        destruct (natlthorgeh (pr1 zero) j).
        + exact 0.
        + destruct (natgehchoice (pr1 zero) j); try assumption.
          * exact 0.
          * exact (@rigunel2 F).
      - exact (const_vec 0).
      - exact (n,, natgthsnn n).
      - exact (zero).
    }
    use tpair. {apply zero. }
    use tpair.
    - rewrite back_sub_internal_inv1'; try assumption.
      2: {apply isreflnatleh. }
      destruct (natlthorgeh _ _) as [lt | ge].
      * contradiction (isirreflnatgth _ lt).
      * simpl; clear gt. destruct (natgehchoice _ _) as [gt | eq].
        {contradiction (isirreflnatlth _ gt). }
        apply (@nonzeroax F).
    - apply funextfun; intros j.
      destruct (natlthorgeh j zero) as [? | ge].
      + rewrite back_sub_internal_inv2'; try assumption.
        {reflexivity. }
        * (* TODO generalize, forall n, j : stn, j >= dualelement n,, natgthsnn n)*)
          unfold dualelement.
          destruct (natchoice0 (S n)).
          {simpl. rewrite minus0r, minusxx. apply idpath. }
          rewrite coprod_rect_compute_2.
          simpl. rewrite minus0r, minusxx. apply idpath.
        * apply (pr2 iszero); assumption.
      + rewrite matrix_mult_eq; unfold matrix_mult_unf.
        unfold col_vec, const_vec.
        apply funextfun; intros ?.
        rewrite zero_function_sums_to_zero.
        {reflexivity. }
        apply funextfun; intros k.
        destruct (natgthorleh j k) as [? | le].
        {rewrite ut; try assumption; apply rigmult0x. }
        destruct (stn_eq_or_neq (zero) k) as [eq | ?].
        * rewrite <- eq in *.
          rewrite <- (stn_eq _ _ (isantisymmnatgeh _ _ le ge)).
          rewrite (pr1 iszero).
          apply rigmult0x.
        * etrans.
          -- apply maponpaths.
             rewrite back_sub_internal_inv1'; try assumption.
             2: {apply (istransnatleh ge le). }
             destruct (natlthorgeh _ _) as [? | ?].
             ++ reflexivity.
             ++ destruct (natgehchoice _ _) as [? | eq].
                ** reflexivity.
                ** rewrite (stn_eq _ _ eq) in *.
                   contradiction (isirrefl_natneq k).
          -- apply rigmultx0.
  Defined.


End BackSubZero.

Section Inverse.

  Context (F : fld).

  Local Notation Σ := (iterop_fun (@ringunel1 F) op1).
  Local Notation "A ** B" := (@matrix_mult F _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* Construct the inverse, if additionally mat is upper triangular with non-zero diagonal *)
  Definition upper_triangular_right_inverse_construction
    { n : nat }
    (mat : Matrix F n n)
    := transpose (λ i : (stn n), (back_sub F (mat) ((@identity_matrix F n) i))).
    
  Local Definition flip_fld_bin
    (e : F) : F.
  Proof.
    destruct (fldchoice0 e).
    - exact 1%ring.
    - exact 0%ring.
  Defined.

  Local Definition flip_fld_bin_vec
    {n : nat} (v : Vector F n) := λ i : (stn n), flip_fld_bin (v i).

  (* TODO should take matrix *)
  Definition diagonal_all_nonzero_compute_internal
    {n : nat} (v : Vector F n)
    : coprod (∏ j : (stn n), (v j) != 0%ring)
             (∑ i : (stn n), ((((v i) = 0%ring) ×
                (forall j : stn n, (j < (pr1 i) -> (v j) != 0%ring))))).
  Proof.
    pose (H1 := leading_entry_compute F (flip_fld_bin_vec v)).
    destruct (@maybe_stn_choice F n H1) as [some | none].
    - right; use tpair. {apply some. }
      simpl.
      pose (H2 := @leading_entry_compute_internal_correct1
        F _ (flip_fld_bin_vec v) (*(n,, natgthsnn n)*) (pr1 some) (pr2 some)).
      destruct H2 as [H2 H3].
      unfold is_leading_entry, flip_fld_bin_vec, flip_fld_bin in *.
      destruct (fldchoice0 (v (pr1 some))); try contradiction.
      use tpair; try assumption; simpl.
      intros j lt.
      pose (eq := H3 _ lt).
      generalize eq; clear eq H3.
      intros c.
      destruct (fldchoice0 (v (j))); try contradiction.
      assumption.
    - left; intros j.
      pose (H3 := @leading_entry_compute_internal_correct2
        _ _ (flip_fld_bin_vec v) _ none j).
      rewrite <- H3; try apply (pr2 (dualelement j)); clear H3.
      destruct (fldchoice0 (v j)) as [eq | neq];
        unfold is_leading_entry, flip_fld_bin_vec, flip_fld_bin in *.
      + destruct (fldchoice0 _); try assumption.
        rewrite eq; intros contr_neq.
        contradiction (nonzeroax _ (pathsinv0 contr_neq)).
      + destruct (fldchoice0 (v j)) as [contr_eq | ?]; try assumption.
        rewrite contr_eq in neq; contradiction.
  Defined.

  Definition diagonal_all_nonzero_compute
    {n : nat} (v : Vector F n)
    : coprod (∏ j : (stn n), (v j) != 0%ring)
             (∑ i : (stn n), (v i) = 0%ring).
  Proof.
    pose (H := @diagonal_all_nonzero_compute_internal n v).
    destruct H as [l | r].
    - left. assumption.
    - right.
      use tpair. {exact (pr1 r). }
      exact (pr1 (pr2 r)).
  Defined.

  (* actually only needs right invertibility ? *)
  Lemma invertible_upper_triangular_to_diagonal_all_nonzero
    {n : nat }
    (A : Matrix F n n)
    (p : @is_upper_triangular F n n A)
    (p': @matrix_left_inverse F _ _ A)
    : (@diagonal_all_nonzero F n A).
  Proof.
    pose (H := @diagonal_all_nonzero_compute_internal _ (@diagonal_sq F _ A)).
    destruct H as [l | r].
    { unfold diagonal_all_nonzero.
      intros i. unfold diagonal_sq in l.
      apply l. }
    unfold diagonal_sq in r.
    pose (H := @back_sub_zero _ _ A p).
    apply fromempty.
    apply H; try assumption.
  Defined.

  Lemma right_inverse_construction_correct
    { n : nat } (mat : Matrix F n n)
    (ut : @is_upper_triangular F _ _ mat)
    (df: @diagonal_all_nonzero F n mat)
    : (mat ** ((upper_triangular_right_inverse_construction mat)))
      = (@identity_matrix F n).
  Proof.
    apply funextfun; intros i.
    unfold matrix_mult, row.
    unfold col, transpose, flip.
    apply funextfun; intros ?.
    unfold upper_triangular_right_inverse_construction.
    rewrite (@col_vec_mult_eq F n n mat
      (λ y : (⟦ n ⟧)%stn, upper_triangular_right_inverse_construction mat y x)
        (@identity_matrix F n x)).
    - destruct (stn_eq_or_neq i x) as [eq | neq].
      {rewrite eq; reflexivity. }
      rewrite id_mat_ij; try rewrite id_mat_ij; try reflexivity; try assumption.
      apply (issymm_natneq _ _ neq).
    - unfold upper_triangular_right_inverse_construction.
      pose (H2 := @back_sub_inv0).
      destruct (natchoice0 n) as [eq | ?].
      {apply fromstn0. rewrite eq. assumption. }
      apply (H2 _ _ _ _ ut df).
  Defined.

  Local Lemma row_vec_col_vec_mult_eq
  { n : nat }
  (A : Matrix F n n)
  : ∏ x, transpose ((row_vec x) ** (transpose A)) = (A ** (col_vec x)).
  Proof.
    intros; unfold transpose, flip, row_vec, col_vec, row, col; intros.
    do 2 (rewrite matrix_mult_eq; unfold matrix_mult_unf).
    assert (eq: ∏ x0 : (stn n), iterop_fun 0%ring op1
        (λ k : (⟦ n ⟧)%stn, (x k * A x0 k)%ring)
      = iterop_fun 0%ring op1 (λ k : (⟦ n ⟧)%stn, (A x0 k * x k )%ring)).
    { intros x0.
      assert (sum_pointwise_eq : ∏ (f g : (stn n) -> F),
      (∏ i : (stn n), f i = g i) ->
        iterop_fun 0%ring op1 f =  iterop_fun 0%ring op1 g).
      { intros f g H. apply maponpaths. apply funextfun. intros j. apply H. }
      apply sum_pointwise_eq.
      intros; apply (@ringcomm2 F). }
    assert (f_eq : ∏ f g: (stn n) -> (stn 1) -> F,
      (∏ i : (stn n), ∏ j : (stn 1), f i j = g i j) -> f = g).
    { intros f g. intros H. apply funextfun; intros i.
      apply funextfun; intros j. apply H. }
    apply f_eq; intros i j; apply eq.
  Defined.

  (* (BA)C = I -> D, s.t. BD = I*)
  Local Lemma matrix_product_right_inverse_to_left_term_right_inverse
    {R : rig} {n : nat} 
    (A : Matrix R n n) (B : Matrix R n n)
    (inv : (matrix_right_inverse (matrix_mult A B))) : matrix_right_inverse A.
  Proof.
    use tpair. { exact (matrix_mult B (pr1 inv)). }
    simpl; rewrite <- matrix_mult_assoc; apply inv.
  Defined.

  (* C(BA) -> D s.t. DA = I*)
  Local Lemma matrix_product_left_inverse_to_right_term_left_inverse
    {R : rig} {n : nat}
    (A : Matrix R n n) (B : Matrix R n n)
    (inv : (matrix_left_inverse (matrix_mult A B))) : matrix_left_inverse B.
  Proof.
    use tpair. { exact (matrix_mult (pr1 inv) A). }
    simpl; rewrite matrix_mult_assoc; apply inv.
  Defined.

  Local Lemma left_inverse_implies_right_internal
    {n : nat}
    (A B: Matrix F n n)
    (ut : @is_upper_triangular F _ _ A) (df: @diagonal_all_nonzero F n A)
    : (B ** A) = (@identity_matrix F n) -> (@matrix_inverse F n A).
  Proof.
    intros H0.
    use tpair. { exact B. }
    use tpair; try assumption.
    assert (eq0: ∏ y, (A ** (col_vec (back_sub F A y))) = (col_vec y)).
    { intros. apply (back_sub_inv0 _ _ _ ut df); assumption. }
    assert (eq1 : ∏ y,
      (B ** (A ** (col_vec (back_sub F A y)))) = (B ** (col_vec y))).
    { intros y. pose (H := eq0 y).
      rewrite H. reflexivity.  }
    assert (eq2 : ∏ y, (col_vec (back_sub F A y) = (B ** (col_vec y)))).
    { intros y.
      pose (H := eq1 y).
      rewrite <- matrix_mult_assoc, H0, matlunax2 in H.
      assumption. }
    assert (eq3 : ∏ y,
      (A ** (col_vec (back_sub F A y))) = (A ** (B ** (col_vec y)))).
    { intros y.
      rewrite <- (eq2 y); reflexivity. }
    assert (eq4 : ∏ y, col_vec y = (A ** (B ** (col_vec y)))).
    { intros y.
      pose (H := eq3 y).
      pose (H1 := eq0 y).
      unfold col_vec in *.
      rewrite <- H1.
      apply maponpaths.
      rewrite <- matrix_mult_assoc, H0, matlunax2.
      apply idpath. }
    apply identity_matrix_unique_left.
    intros n' A'.
    apply funextfun; intros i.
    apply funextfun; intros j.
    pose (H := (eq4 (col A' j))).
    rewrite <- matrix_mult_assoc in H.
    symmetry in H.
    pose (eq5 := @col_vec_mult_eq F n n _ _ _ H).
    unfold col, transpose, flip in eq5.
    rewrite <- eq5.
    apply idpath.
  Defined.

  Lemma make_matrix_left_inverse
    {R : rig}
    {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix)
    : matrix_left_inverse B.
  Proof.
    unfold matrix_left_inverse.
    use tpair. {exact A. }
    exact eq.
  Defined.

  Lemma make_matrix_right_inverse
    {R : rig} {m n k: nat}
    (A : Matrix R m n) (B : Matrix R n m)
    (eq : matrix_mult A B = identity_matrix)
    : matrix_right_inverse A.
  Proof.
    unfold matrix_left_inverse.
    use tpair. {exact B. }
    exact eq.
  Defined.

  Lemma left_inverse_implies_right { n : nat } (A B: Matrix F n n)
    : (B ** A) = (@identity_matrix F n)
    -> (@matrix_right_inverse F n n A).
  Proof.
    intros H0.
    destruct (natchoice0 n) as [eq0 | gt].
    { unfold matrix_inverse. use tpair. {assumption. }
      simpl. apply funextfun; intros i; apply fromstn0; rewrite eq0; assumption. }
    pose (C := (clear_rows_up_to_as_left_matrix_internal F A (n,, natgthsnn n)) gt).
    pose (C' := gauss_clear_rows_up_to_as_matrix_eq F (n,, natgthsnn n) C).
    pose (CA := C ** A).
    pose (D := @upper_triangular_right_inverse_construction n CA).
    use tpair. {exact (D ** C). }
    assert (H1 : is_upper_triangular CA).
    { pose (H1 := @row_echelon_partial_to_upper_triangular_partial F n n CA gt (n,, natgthsnn n)).
      unfold is_upper_triangular.
      unfold is_upper_triangular_partial in H1.
      intros.
      apply H1; try assumption.
      2: {exact (pr2 i). }
      unfold is_row_echelon_partial.
      pose (H2 := @gauss_clear_rows_up_to_inv1 F n n A gt (n,, natgthsnn n)).
      pose (H3 := @gauss_clear_rows_up_to_inv2 F n n A gt (n,, natgthsnn n)).
      use tpair.
      - rewrite <- (gauss_clear_rows_up_to_as_matrix_eq F _ _ gt) in H2.
        apply H2.
      - rewrite <- (gauss_clear_rows_up_to_as_matrix_eq F _ _ gt) in H3.
        apply H3.
    }
    assert (H2 : @diagonal_all_nonzero F _ CA).
    { apply invertible_upper_triangular_to_diagonal_all_nonzero; try assumption.
      pose (H3 := @clear_rows_up_to_matrix_invertible
        F _ n (n,, natgthsnn n) (0,, gt) A gt). (* TODO why the superfluous idx? *)
      destruct H3 as [M isinv].
      destruct isinv as [linv rinv].
      apply left_inv_matrix_prod_is_left_inv.
      - use tpair.
        {exact M. }
        simpl; assumption.
      - use tpair.
        { exact B. }
        assumption.
    }
    pose (H4 := @right_inverse_construction_correct _ _ H1 H2).
    unfold CA in H4.
    rewrite matrix_mult_assoc in H4.
    pose (CM := @gauss_clear_rows_up_to_matrix_invertible F _ _ (n,, natgthsnn n) A gt).
    pose (H5 := @matrix_product_left_inverse_to_right_term_left_inverse).
    pose (H6 := @matrix_product_right_inverse_to_left_term_right_inverse).
    pose (H7 := left_inverse_implies_right_internal _ (B ** (pr1 CM) ) H1 H2).
    assert (eq : (C ** A ** D) = (A ** D ** C)).
    { unfold CA in H4. unfold D, CA.
      rewrite matrix_mult_assoc. rewrite H4.
      pose (H8 := @matrix_left_inverse_equals_right_inverse).
      apply pathsinv0.
      unfold matrix_left_inverse in H7.
      pose (H9 := @gauss_clear_rows_up_to_matrix_invertible F n n (n,, natgthsnn n) A gt).
      apply (matrix_inverse_to_right_and_left_inverse) in H9.
      destruct H9 as [H9 H10].
      unfold clear_rows_up_to_as_left_matrix in *.
      pose (H11 := @H8 F n _ n
        (clear_rows_up_to_as_left_matrix_internal F A (n,, natgthsnn n) gt) (H9) ((A ** D),, H4)).
      simpl in H11.
      unfold D, CA in H11.
      replace (@matrix_mult F _ _ A _
        (upper_triangular_right_inverse_construction (@matrix_mult F _ _ C _ A)))
          with (pr1 H9).
      2: { rewrite H11. reflexivity. }
      simpl.
      pose (H12 := @matrix_left_inverse_equals_right_inverse _ n _ n _ H9 H10).
      unfold matrix_left_inverse in H9.
      destruct H9 as [H9 H9'].
      simpl; unfold C.
      assumption.
    }
    rewrite (@matrix_mult_assoc F n n A n D n C) in eq.
    rewrite <- matrix_mult_assoc in H4.
    unfold D, CA in eq.
    rewrite H4 in eq.
    apply pathsinv0 in eq.
    apply eq.
  Defined.

  Lemma right_inverse_implies_left 
    { n : nat }
    (A B: Matrix F n n) 
    : @matrix_right_inverse F _ _ A
      -> (@matrix_left_inverse F _ _ A).
  Proof.
    intros A_right_inv.
    destruct A_right_inv as [rinv isrinv].
    pose (linv := @make_matrix_left_inverse F _ _ n A rinv isrinv).
    pose (linv_to_rinv := @left_inverse_implies_right n _ _ isrinv).
    use tpair. {exact rinv. }
    pose (inv_eq := @matrix_left_inverse_equals_right_inverse _ n _ n _ linv linv_to_rinv).
    simpl in inv_eq.
    rewrite inv_eq.
    apply linv_to_rinv.
  Defined.

  Theorem matrix_inverse_or_non_invertible { n : nat }
    (A : Matrix F n n)
    : @matrix_inverse_or_non_invertible_stmt _ _ A.
  Proof.
    unfold matrix_inverse_or_non_invertible_stmt.
    destruct (natchoice0 n) as [? | gt].
    { left. apply nil_matrix_is_inv; symmetry; assumption. }
    set (B:= @clear_rows_up_to_as_left_matrix _ _ _ A (n,, natgthsnn n) gt).
    set (BA := B ** A).
    set (C := upper_triangular_right_inverse_construction BA).
    assert (ut : is_upper_triangular BA).
    { unfold BA.
      pose (is_echelon := @gauss_clear_rows_up_to_inv3 F _ _ A gt (n,, natgthsnn n)).
      rewrite <- (gauss_clear_rows_up_to_as_matrix_eq F _ _ gt) in is_echelon.
      apply row_echelon_to_upper_triangular; try assumption. }
    destruct (diagonal_all_nonzero_compute (λ i : (stn n), BA i i)) as [nz | hasz].
    2 : { right.
          intros H; destruct H as [invM isinv].
          destruct isinv as [isl isr].
          pose (isinv := @make_matrix_left_inverse _ _ _ n _ _ isr).
          assert (isinvprod : (matrix_left_inverse BA)).
          { apply left_inv_matrix_prod_is_left_inv; try assumption.
            apply (@matrix_inverse_to_right_and_left_inverse F _ B).
            apply clear_rows_up_to_matrix_invertible.
            (* TODO remove unused arg*)
            exact (0,, gt).
          }
          destruct hasz as [idx isnotz].
          pose (contr_eq := @invertible_upper_triangular_to_diagonal_all_nonzero
                _ _ ut isinvprod idx).
          rewrite isnotz in contr_eq.
          contradiction.
    }
    left.
    set (BAC := BA ** C).
    set (BAC_id := @right_inverse_construction_correct _ _ ut nz).
    assert (rinv_eq : (C ** BA) = identity_matrix).
    { pose (linv := @right_inverse_implies_left _ BA C (C,, BAC_id)).
      pose (eq := @matrix_left_inverse_equals_right_inverse F n _ n BA linv (C,, BAC_id)).
      change (pr1 (C,, BAC_id)) with C in eq.
      apply linv. }
    use tpair. {exact (C ** B). }
    simpl; use tpair.
    2: { simpl. rewrite matrix_mult_assoc. apply rinv_eq. }
    rewrite <- matrix_mult_assoc.
    unfold BA in BAC_id.
    assert (linv_eq : ((B ** A ** C) = (A ** C ** B))).
    { rewrite matrix_mult_assoc.
      rewrite matrix_mult_assoc in BAC_id.
      unfold C in *; clear C; set (C := (upper_triangular_right_inverse_construction BA)).
      pose (B_rinv := @make_matrix_right_inverse F _ _ n B (A ** C) (BAC_id)).
      pose (linv := @right_inverse_implies_left _ B C B_rinv).
      pose (eq := @matrix_left_inverse_equals_right_inverse F n _ n B linv ((A** C),, BAC_id)).
      replace (A ** C) with (pr1 B_rinv).
      2: {simpl. reflexivity. }
      rewrite (pr2 B_rinv).
      replace (pr1 B_rinv) with (pr1 linv); try assumption.
      2: {rewrite eq. simpl; reflexivity. }
      rewrite (pr2 linv); reflexivity.
    }
    simpl in *.
    rewrite <- BAC_id, <- linv_eq.
    unfold C, BA.
    reflexivity.
  Defined.

End Inverse.