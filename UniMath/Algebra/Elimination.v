(** * Matrices

Gaussian Elimination over integers.

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Matrix.

Require Import UniMath.NumberSystems.Integers.
Require Import UniMath.NumberSystems.RationalNumbers.

Require Import UniMath.Combinatorics.WellOrderedSets.

Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Foundations.NaturalNumbers.

(*Local Definition R := pr1hSet natcommrig.*)
Context { R : rig }.
Local Definition F := hq.

(* The first few sections contain Definitions and Lemmas that
   should be moved further up the project tree *)



Local Notation "A ** B" := (matrix_mult A B) (at level 80).
Local Notation  Σ := (iterop_fun 0%hq op1).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).


Section Misc.



  Definition min' (n m : nat) : nat.
  Proof.
    induction (natgtb n m).
    - exact m.
    - exact n.
  Defined.


End Misc.


Section PrelStn.

  Local Definition truncate_pr1 { n : nat } ( f : ⟦ n ⟧%stn → hq) ( k : ⟦ n ⟧%stn ) : ( ⟦ n ⟧%stn → hq).
  Proof.
    intros.
    induction (natgtb X k).
    - exact (f X).
    - exact (f k).
  Defined.

  Lemma stn_implies_nneq0 { n : nat } (i : ⟦ n ⟧%stn) : n ≠ 0.
  Proof.
    induction (natchoice0 n) as [T | F].
    - rewrite <- T in i.
      apply weqstn0toempty in i. apply fromempty. assumption.
    - change (0 < n) with (n > 0) in F.
      destruct n.
      + apply isirreflnatgth in F. apply fromempty. assumption.
      + apply natgthtoneq in F. reflexivity.
  Defined.

  Lemma stn_implies_ngt0 { n : nat} (i : ⟦ n ⟧%stn) : n > 0.
  Proof.
    exact (natneq0to0lth n (stn_implies_nneq0 i)).
  Defined.

  Definition decrement_stn_by_m { n : nat } ( i : (⟦ n ⟧)%stn ) (m : nat) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgehchoice m 0).
    - assert ( p :  ((pr1 i) - m) < n).
        {  unfold stn in i. set (p0 := pr2 i). assert (pr1 i < n).
           - exact (pr2 i).
           - assert ((pr1 i - m <= ( pr1 i))). {apply (natminuslehn ). }
              apply (natlehlthtrans (pr1 i - m) (pr1 i) ).
              + assumption.
              + assumption.
        }
      exact (pr1 i - m,, p).
    - exact i.
    - reflexivity.
  Defined.

  Local Definition mltntommin1ltn { n m : nat } (p : m < n) : (m - 1 < n).
  Proof.
    apply natlthtolthm1. assumption.
  Defined.


  Definition set_stn_vector_el { n : nat } (vec : Vector (⟦ n ⟧%stn) n) (idx : ⟦ n ⟧%stn) (el : (⟦ n ⟧%stn)) : Vector (⟦ n ⟧%stn) n.
  Proof.
  intros i.
  induction (stn_eq_or_neq i idx).
  + exact el.
  + exact (vec i).
  Defined.

  Definition nat_lt_minmn_to_stnm_stnn {m n : nat} (i : nat) (p : i < min' m n) : ⟦ m ⟧%stn × ⟦ n ⟧%stn.
  Proof.
   (* unfold min in p. *)
    assert (min n n = n).
      { unfold min.  induction n. reflexivity. unfold natgtb. destruct n. { reflexivity. }

    assert (i < n).
    (* cbn in p. *)
    induction (natgehchoice m n) as [MGT | NGE].
      - unfold min in p.

  Abort.

  (*
  Definition decrement_stn_by_m { n : nat } ( i : (⟦ n ⟧)%stn ) (m : nat) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgehchoice m 0).
    - assert ( p :  ((pr1 i) - m) < n).
        {  unfold stn in i. set (p0 := pr2 i). assert (pr1 i < n).
           - exact (pr2 i).
           - assert ((pr1 i - m <= ( pr1 i))). {apply (natminuslehn ). }
              apply (natlehlthtrans (pr1 i - m) (pr1 i) ).
              + assumption.
              + assumption.
        }
      exact (pr1 i - m,, p).
    - exact i.
    - reflexivity.
  Defined.
  *)

  Definition stnn_to_stn_sminusn1 { n : nat } ( i : (⟦ n ⟧)%stn ) : ((⟦ S (n - 1) ⟧)%stn).
  Proof.
    intros.
    induction (natgehchoice n 0).
    3 : { exact (natgehn0 n). }
    2 : { apply stn_implies_ngt0 in i.
          apply natgthtoneq in i.
          rewrite b in i.
          contradiction i.
    }
    assert (e : n = S (n - 1)). (* Small proof taken verbatim from stnsum. *)
    { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
      apply pathsinv0. apply minusplusnmm. assumption.
    }
    rewrite <- e.
    assumption.
  Defined.

  (* TODO this should just be a matter of rewriting using above ? *)
  Definition stn_sminusn1_to_stnn { n : nat }  (i : (⟦ S (n - 1) ⟧)%stn) : (⟦ n ⟧%stn).
  Proof.
    intros.
    induction (natgehchoice (S (n - 1)) 0).
      3 : { exact (natgehn0 n ). }
      2 : { rewrite b in i.
            apply (stn_implies_ngt0) in i.
            apply isirreflnatgth in i.
            apply fromempty. assumption.
      }
    assert (e : n = S (n - 1)). (* Small proof taken verbatim from stnsum. *)
    { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
      apply pathsinv0. rewrite minusplusnmm.
      - apply idpath.
      - apply natlthsntoleh.
    Abort.

End PrelStn.



Section Matrices.

  Definition matunel2 { n : nat } := @identity_matrix R n.

  Local Notation  Σ := (iterop_fun rigunel1 op1).


  (* Identical to transport_stnsum but with Σ , R*)
  Lemma transport_rigsum {m n : nat} (e: m = n) (g: ⟦ n ⟧%stn -> R) :
     Σ g =  Σ (λ i, g (transportf stn e i)).
  Proof.
    intros.
    induction e.
    apply idpath.
  Defined.


  (* Is there some tactical way to re-use previous proofs
     with a few changes? *)
  Lemma rigsum_eq {n : nat} (f g : ⟦ n ⟧%stn -> R) : f ~ g ->  Σ f =  Σ g.
  Proof.
    intros h.
    induction n as [|n IH].
    - apply idpath.
    - rewrite 2? iterop_fun_step. 2: { apply riglunax1. }
                                  2: { apply riglunax1. }
      induction (h lastelement).
      apply (maponpaths (λ i, op1 i (f lastelement))).
      apply IH.
      intro x.
      apply h.
  Defined.

  Lemma rigsum_step {n : nat} (f : ⟦ S n ⟧%stn -> R) :
    Σ f = op1 (Σ (f ∘ (dni lastelement))) (f lastelement).
  Proof.
    intros.
    apply iterop_fun_step.
    apply riglunax1.
  Defined.


  Lemma rigsum_left_right :
  ∏ (m n : nat) (f : (⟦ m + n ⟧)%stn → R),
   Σ f =  op1 (Σ (f ∘ stn_left m n)) (Σ (f ∘ stn_right m n)).
  Proof.
    intros.
    induction n as [| n IHn].
    (*unfold stn_left. unfold stn_right.*)
    { change (Σ  _) with (@rigunel1 R) at 3.
      set (a := m + 0). assert (a = m). { apply natplusr0. } (* In the stnsum case,
                                                                this can affect ⟦ m ⟧
                                                                and zeroes elsewhere *)
      assert (e := ! natplusr0 m).
      rewrite (transport_rigsum e).
      unfold funcomp.
      rewrite  rigrunax1.
      apply maponpaths. apply pathsinv0.
      apply funextfun. intros i.
      rewrite <- stn_left_0.
      reflexivity.
    }
    rewrite rigsum_step.
    assert (e : S (m + n) = m + S n).
    { apply pathsinv0. apply natplusnsm. }
    rewrite (transport_rigsum e).
    rewrite rigsum_step.
    rewrite <- rigassoc1. apply map_on_two_paths.
    { rewrite IHn; clear IHn. apply map_on_two_paths.
      { apply rigsum_eq; intro i. unfold funcomp.
        apply maponpaths. apply subtypePath_prop.
        rewrite stn_left_compute. induction e.
        rewrite idpath_transportf. rewrite dni_last.
        apply idpath. }
      { apply rigsum_eq; intro i. unfold funcomp.
        apply maponpaths. apply subtypePath_prop.
        rewrite stn_right_compute. unfold stntonat. induction e.   (* we have stn_right instead of stn_left? *)
        rewrite idpath_transportf. rewrite 2? dni_last.
        apply idpath. } }
    unfold funcomp. apply maponpaths. apply subtypePath_prop.
    induction e. apply idpath.
  Defined.

  (* stnsum_dni with
     stnsum -> Σ
     transport_stnsum -> transport_rigsum
     stnsum_left_right -> rigsum_left_right
     natplusassoc -> rigassoc1*)
  Lemma rigsum_dni {n : nat} (f : ⟦ S n ⟧%stn -> R) (j : ⟦ S n ⟧%stn ) :
    Σ f = op1 (Σ (f ∘ dni j)) (f j).
Proof.
  intros.
  induction j as [j J].
  assert (e2 : j + (n - j) = n).
  { rewrite natpluscomm. apply minusplusnmm. apply natlthsntoleh. exact J. }
  assert (e : (S j) + (n - j) = S n).
  { change (S j + (n - j)) with (S (j + (n - j))). apply maponpaths. exact e2. }
  intermediate_path (Σ  (λ i, f (transportf stn e i))).
  - apply (transport_rigsum e).
  - rewrite (rigsum_left_right (S j) (n - j)); unfold funcomp.
    apply pathsinv0. rewrite (transport_rigsum e2).
    rewrite (rigsum_left_right j (n-j)); unfold funcomp.
    rewrite (rigsum_step (λ x, f (transportf stn e _))); unfold funcomp.
    apply pathsinv0.
    rewrite rigassoc1. rewrite (@rigcomm1 R (f _) ). rewrite  <- rigassoc1. (* natpluss to @ R ... *)
    apply map_on_two_paths.
    + apply map_on_two_paths.
      * apply rigsum_eq; intro i. induction i as [i I].
        apply maponpaths. apply subtypePath_prop.
        induction e. rewrite idpath_transportf. rewrite stn_left_compute.
        unfold dni,di, stntonat; simpl.
        induction (natlthorgeh i j) as [R|R].
        -- unfold stntonat; simpl; rewrite transport_stn; simpl.
           induction (natlthorgeh i j) as [a|b].
           ++ apply idpath.
           ++ contradicts R (natlehneggth b).
        -- unfold stntonat; simpl; rewrite transport_stn; simpl.
           induction (natlthorgeh i j) as [V|V].
           ++ contradicts I (natlehneggth R).
           ++ apply idpath.
      * apply rigsum_eq; intro i. induction i as [i I]. apply maponpaths.
        unfold dni,di, stn_right, stntonat; repeat rewrite transport_stn; simpl.
        induction (natlthorgeh (j+i) j) as [X|X].
        -- contradicts (negnatlthplusnmn j i) X.
        -- apply subtypePath_prop. simpl. apply idpath.
    + apply maponpaths.
      rewrite transport_stn; simpl.
      apply subtypePath_prop.
      apply idpath.
Defined.


  (* Should be n not S n *)
  Lemma pulse_function_sums_to_point_rig { n : nat }  (f : ⟦ S n ⟧%stn -> R) :
  ∏ (i : ⟦ S n ⟧%stn ), (f i != 0%rig) -> (∏ (j : ⟦ S n ⟧%stn), ((i ≠ j) -> (f j = 0%rig))) ->  (Σ f = f i).
  Proof.
    intros i. intros f_i_neq_0 j.  (*impj0.*)

    rewrite (rigsum_dni f i).
    rewrite zero_function_sums_to_zero.
    { rewrite riglunax1. apply idpath. }
    apply funextfun.
    intros k.
    unfold funcomp.

    replace (const_vec 0%rig k) with (@rigunel1 R). 2: { reflexivity. }
    assert (i_neq_dni : i ≠ dni i k) . {exact (dni_neq_i i k). }
    - intros. destruct (stn_eq_or_neq i (dni i k) ).
        + apply (stnneq_iff_nopath i (dni i k)) in p.
          apply weqtoempty. intros. apply p. assumption.
          exact (dni_neq_i i k). (* Move up *)
        + apply j. exact h.
   Defined.

  Definition is_pulse_function { n : nat } ( i : ⟦ n ⟧%stn )  (f : ⟦ n ⟧%stn -> R) :=

    ∏ (j: ⟦ n ⟧%stn), (f i != 0%rig) -> (i ≠ j) -> (f j = 0%rig).

  Lemma pulse_function_sums_to_point_rig' { n : nat } ( i : ⟦ n ⟧%stn ) {f : ⟦ n ⟧%stn -> R}
    (p : is_pulse_function i f) : (Σ f = f i).
  Proof.
    unfold is_pulse_function in p.
    revert p.
    intros.
  Admitted. (* Tired ... *)
  (*
    rewrite (rigsum_dni f i).
    apply rigsum_dni.
    refine p.
    specialize (p ).
    revert p.

    apply (pulse_function_sums_to_point_rig).
    use tpair.
    apply p.
    destruct p.
  Defined.
  *)

  Lemma id_math_row_is_pf { n : nat }  : ∏ (r : ⟦ n ⟧%stn), (is_pulse_function r (identity_matrix r) ).
  Proof.
    unfold is_pulse_function.
    intros r i rr_neq_0 r_neq_j.
    unfold identity_matrix.
    destruct (stn_eq_or_neq r i) as [T | F].
    - rewrite T in r_neq_j.
      apply isirrefl_natneq in r_neq_j. apply fromempty. assumption.
    - rewrite coprod_rect_compute_2.
      reflexivity.
  Defined.

    (* Is n ≥ 1 necessary ? *)
  Definition vector_n_to_vector_snm1 { n : nat } (v : Vector R n) (p : n ≥ 1) : (Vector R (S ( n - 1 ))).
  Proof.
    unfold Vector in v.
    unfold Vector.
    change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
    rewrite minusplusnmm. 2 : {exact p. }
    exact v.
  Defined.


  (* This should be trivially true but how do we correctly formulate / prove it ? *)
  Lemma isirrefl_rigunel1_to_empty : (@rigunel1 R != @rigunel1 R ) -> ∅.
  Admitted.



  Lemma matlunel2 : ∏ (n : nat) (mat : Matrix R n n),
    (identity_matrix ** mat) = mat.
  Proof.
    intros.
    apply funextfun. intros i.
    apply funextfun. intros j.

    - unfold "**". unfold row. unfold "^".

      assert (X: is_pulse_function i (λ i0 : (⟦ n ⟧)%stn, op2 (identity_matrix i i0) (col mat j i0))).
      { unfold is_pulse_function.

        intros k id_ii_m_neq_0 i_neq_k.
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
      rewrite (pulse_function_sums_to_point_rig' i X).
      unfold identity_matrix.
      destruct (stn_eq_or_neq i i).
      + rewrite coprod_rect_compute_1.
        apply riglunax2.
      + (*apply isirrefl_natneq in h. *)
        rewrite coprod_rect_compute_2.
        apply isirrefl_natneq in h.
        apply fromempty. assumption.

  Defined.

  Definition matrix_is_invertible {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix) × ((B ** A) = identity_matrix).

  Definition matrix_is_invertible_left {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix).

  Definition matrix_is_invertible_right {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((B ** A) = identity_matrix).


  Lemma inv_matrix_prod_is_inv {n : nat} (A : Matrix R n n)
    (A' : Matrix R n n) (pa : matrix_is_invertible A) (pb : matrix_is_invertible A') :
    (matrix_is_invertible (A ** A')).
  Proof.
    intros.
    unfold matrix_is_invertible in pa.
    unfold matrix_is_invertible in pb.
    unfold matrix_is_invertible.
    use tpair. { exact ((pr1 pb) ** (pr1 pa)). }
    use tpair.
    - rewrite matrix_mult_assoc.
      rewrite <- (matrix_mult_assoc A' _ _).
  (* We need I ** M = M *)
  Abort.

  Lemma identity_is_inv { n : nat } : matrix_is_invertible (@identity_matrix _ n).
  Proof.
    unfold matrix_is_invertible.
    use tpair. { exact identity_matrix. }
    set (id := @identity_matrix R n).
    Abort.

  (*
  Definition eq_set_invar_by_invmatrix_mm { n : nat } ( A : Matrix R n n )
    (C : Matrix R n n)
    (x : Matrix R n 1) (b : Matrix R n 1) : (A ** x) = b -> ((C ** A) ** x) = (C ** b).
  Proof.

  Abort.
  *)

End Matrices.


Section MatricesF.



  (* Not really a clamp but setting every element at low indices to zero.  *)
  Local Definition clamp_f {n : nat} (f : ⟦ n ⟧%stn -> hq) (cutoff : ⟦ n ⟧%stn) : (⟦ n ⟧%stn -> hq).
    intros i.
    induction (natlthorgeh i cutoff) as [LT | GTH].
    - exact 0%hq.
    - exact (f i).
  Defined.


  Definition zero_vector_hq (n : nat) : ⟦ n ⟧%stn -> hq :=
    λ i : ⟦ n ⟧%stn, 0%hq.

  Definition zero_vector_nat (n : nat) : ⟦ n ⟧%stn -> nat :=
    λ i : ⟦ n ⟧%stn, 0%nat.

  (* This is not really a zero vector, it might be [0 1 2 3] ... Serves the purpose of a placeholder however. *)
  Definition zero_vector_stn (n : nat) : ⟦ n ⟧%stn -> ⟦ n ⟧%stn.
  Proof.
    intros i.
    assumption.
  Defined.


  (* The following definitions set up helper functions on finite sets which are then used in formalizing Gaussian Elimination*)

  Definition max_hq (a b : hq) : hq.
    induction (hqgthorleh a b).
    - exact a.
    - exact b.
  Defined.

  Definition max_hq_one_arg (a : hq) : hq -> hq := max_hq a.

  (* This should exist somewhere *)
  Definition tl' { n : nat }  (vec: Vector F n) : Vector F (n - 1).
    induction (natgtb n 0).
     assert  ( b: (n - 1 <= n)). { apply (natlehtolehm1 n n). apply isreflnatleh. }
    + exact (λ i : (⟦ n - 1 ⟧%stn), vec (stnmtostnn (n - 1) n b i)).
    + exact (λ i : (⟦ n - 1 ⟧%stn), 0%hq). (* ? *)
  Defined.




  (* We can generalize this to just ordered sets *)
  Definition max_hq_index { n : nat } (ei ei' : hq × ⟦ n ⟧%stn) : hq × ⟦ n ⟧%stn.
    induction (hqgthorleh (pr1 ei) (pr1 ei')).
    - exact ei.
    - exact ei'.
  Defined.

  Definition max_hq_index_one_arg { n : nat } (ei : hq × ⟦ n ⟧%stn) : (hq × ⟦ n ⟧%stn) -> (hq × ⟦ n ⟧%stn)
    := max_hq_index ei.

  (* Some of the following lemmata are very specific and could be better without the general definition form, or we
     could write these as local definitions *)
  Definition max_argmax_stnhq {n : nat} (vec : Vector F n) (pn : n > 0) : hq × (⟦ n ⟧)%stn.
  Proof.
    set (max_and_idx := (foldleft (0%hq,,(0%nat,,pn)) max_hq_index (λ i : (⟦ n ⟧%stn), (vec i) ,, i))).
    exact (max_and_idx).
  Defined.



  (*TODO: This is mostly a repetition of the rig equivalent. Can we generalize ? *)
  Lemma zero_function_sums_to_zero_hq:
    ∏ (n : nat) (f : (⟦ n ⟧)%stn -> F),
    (λ i : (⟦ n ⟧)%stn, f i) = const_vec 0%hq ->
    (Σ (λ i : (⟦ n ⟧)%stn, f i) ) = 0%hq.
  Proof.
    intros n f X.
    rewrite X.
    unfold const_vec.
    induction n.
    - reflexivity.
    - intros. rewrite iterop_fun_step.
      + rewrite hqplusr0.
        unfold "∘".
        rewrite -> IHn with ((λ _ : (⟦ n ⟧)%stn, 0%hq)).
        reflexivity.
        reflexivity.
      + unfold islunit. intros.
        rewrite hqplusl0.
        apply idpath.
  Defined.


End MatricesF.



Section Gauss.
  (* Gaussian elimination over the field of rationals *)


  Definition gauss_add_row { m n : nat } ( mat : Matrix F m n )
    ( s : F ) ( r1 r2 : ⟦ m ⟧%stn ) : ( Matrix F m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r1).
    - exact ( op1 ( mat r1 j )  ( op2 s ( mat r2 j ))).
    - exact ( mat r1 j ).
  Defined.

  (* Is stating this as a Lemma more in the style of other UniMath work?*)
  Local Definition identity_matrix { n : nat } : ( Matrix F n n ).
  Proof.
    apply ( @identity_matrix hq ).
  Defined.


  (* Need again to restate several definitions to use the identity on rationals*)
  Local Notation Σ := (iterop_fun 0%hq op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* TODO: replace with upstream version? *)
  Local Definition matrix_mult {m n : nat} (mat1 : Matrix F m n)
    {p : nat} (mat2 : Matrix F n p) : (Matrix F m p) :=
    λ i j, Σ ((row mat1 i) ^ (col mat2 j)).

  Local Notation "A ** B" := (matrix_mult A B) (at level 80).

  (* Can be defined inductively, directly, too.*)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : F)  :=
    gauss_add_row (identity_matrix) s r1 r2.

  Definition add_row_by_matmul { n m : nat } ( r1 r2 : ⟦ m ⟧%stn ) (mat : Matrix F m n) (s : F) : Matrix F m n :=
    (make_add_row_matrix r1 r2 s ) **  mat.

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix F m n)
    (s : F) (r : ⟦ m ⟧%stn): Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
  Defined.

  (* These could really be m x n ...*)
  Definition make_scalar_mult_row_matrix { n : nat}
    (s : F) (r : ⟦ n ⟧%stn): Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r).
    + exact ((gauss_scalar_mult_row identity_matrix s r) r).
    + exact (identity_matrix r).
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

  Definition make_gauss_switch_row_matrix (n : nat)  (r1 r2 : ⟦ n ⟧ %stn) : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r1).
    - exact (identity_matrix r2).
    - induction (stn_eq_or_neq i r2).
      + exact (identity_matrix r1).
      + exact (identity_matrix i).
  Defined.


  Definition test_row_switch_statement {m n : nat} (mat : Matrix F m n)
    (r1 r2 : ⟦ m ⟧%stn) : (gauss_switch_row (gauss_switch_row mat r1 r2) r1 r2) = mat.
  Proof.
    use funextfun; intros i.
    use funextfun; intros j.
    unfold gauss_switch_row.
    destruct (stn_eq_or_neq i r1) as [ e_ir1 | ne_ir1 ]; simpl.
    - destruct (stn_eq_or_neq r2 r1) as [ e_r1r2 | ne_r1r2 ]; simpl.
      + destruct e_ir1, e_r1r2. apply idpath.
      + destruct (stn_eq_or_neq r2 r2) as [ ? | absurd ]; simpl.
        * destruct e_ir1. apply idpath.
        * set (H := isirrefl_natneq _ absurd). destruct H.
    - destruct (stn_eq_or_neq i r2) as [ e_ir2 | ne_ir2 ]; simpl.
      + destruct e_ir2; simpl.
        destruct (stn_eq_or_neq r1 r1) as [ ? | absurd ]; simpl.
        * reflexivity.
        * destruct (stn_eq_or_neq r1 i) as [ e_ir1 | ne_ir1' ]; simpl.
        -- rewrite e_ir1. apply idpath.
        -- set (H := isirrefl_natneq _ absurd). destruct H.
      + reflexivity.
  Defined.


  (* TODO: look for other places this can simplify proofs! and upstream? *)
  Lemma stn_neq_or_neq_refl {n} {i : ⟦ n ⟧%stn} : stn_eq_or_neq i i = inl (idpath i).
  Proof.
  Admitted.

  (* The following three lemmata test the equivalence of multiplication by elementary matrices
     to swaps of indices. *)
  Lemma matrix_scalar_mult_is_elementary_row_op {n : nat} (mat : Matrix F n n) (s : F) (r : ⟦ n ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros j.
    unfold make_scalar_mult_row_matrix. unfold gauss_scalar_mult_row.
    unfold "**". unfold "^". unfold col. unfold transpose. unfold row. unfold flip.
    unfold coprod_rect. unfold identity_matrix.
    destruct (stn_eq_or_neq i r) as [? | ?] ; simpl.
    - rewrite p.
      rewrite stn_neq_or_neq_refl.
      (* apply pulse_function_sums_to_point.*)
  Abort.

  (* Order of arguments should be standardized... *)
  Lemma matrix_row_mult_is_elementary_row_op {n : nat} (r1 r2 : ⟦ n ⟧%stn) (mat : Matrix F n n) (s : F) :
    ((make_add_row_matrix r1 r2 s) ** mat) = gauss_add_row mat s r1 r2.
  Proof.
    intros.
  Abort.

  Lemma matrix_switch_row_is_elementary_row_op {n : nat} (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧%stn) :
    gauss_switch_row mat r1 r2 = ((make_gauss_switch_row_matrix n r1 r2) ** mat).
  Proof.
    intros.
  Abort.

  (* The following three lemmata test the correctness of elementary row operations, i.e. they do not affect the solution set. *)
  Lemma eq_sol_invar_under_scalar_mult {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_scalar_mult_row_matrix s r) ** A ** x)  = ((make_scalar_mult_row_matrix s r) ** (transpose b)).
  Proof.
    intros.
  Abort.

  (* s != 0 ... *)
  Lemma eq_sol_invar_under_row_add {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r1 r2 : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_add_row_matrix r1 r2 s) ** A ** x)  = ((make_add_row_matrix r1 r2 s)  ** (transpose b)).
  Proof.
    intros.
  Abort.

  (* s != 0 ... *)
  Lemma eq_sol_invar_under_row_switch {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n) (s : F) (r1 r2 : ⟦ n ⟧%stn) :
    (A ** x) = (transpose b) -> ((make_gauss_switch_row_matrix n r1 r2) ** A ** x)  = ((make_gauss_switch_row_matrix n r1 r2) ** (transpose b)).
  Proof.
    intros.
  Abort.



  Definition select_pivot_row {m n : nat} (mat : Matrix F m n) ( k : ⟦ m ⟧%stn ) (pm : m > 0) (pn : n > 0) : ⟦ m ⟧%stn
    := pr2 (max_argmax_stnhq (truncate_pr1  ( λ i : (⟦ m ⟧%stn),  pr1 (max_argmax_stnhq ( ( mat) i) pn)) k ) pm).

  (* Helper Lemma. Possibly unecessary. *)
  Local Definition opt_matrix_op {n : nat} (b : bool) (mat : Matrix F n n) (f : Matrix F n n -> Matrix F n n) : Matrix F n n.
  Proof.
    induction b.
    - exact (f mat).
    - exact mat.
  Defined.



  (* Stepwise Gaussian Elimination definitions *)

  (* We can probably assert at this point that m and n are > 0, as the base cases can be handled by caller *)
  (* Performed k times . *)
  (* We should be able to assert n, m > 0 wherever needed, by raa.*)
  Definition gauss_step  { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n × ⟦ n ⟧%stn.
  Proof.
    assert (pn : (n > 0)). { exact (stn_implies_ngt0 k). }
    set (ik := (select_pivot_row mat k pn pn)).
    use tpair. 2: {exact ik. }
    intros i j.
    destruct (natlthorgeh i k) as [LT | GTH]. {exact ((mat i j)). }
    set (mat' := gauss_switch_row mat k ik).
    set (mat'' := gauss_scalar_mult_row mat' ((- 1%hq)%hq * (hqmultinv ( mat' k k )))%hq i%nat).
    destruct (natgtb j k).
    - exact (((mat'' i j) + (mat'' i k) * (mat k j))%hq).
    - exact (mat'' i j).
  Defined.

  (* ( i,, i < n) to (i-1,, i-1 < n *)
  Definition decrement_stn { n : nat } ( i : (⟦ n ⟧)%stn ) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgtb (pr1 i) 0).
    (*- assert ( p : ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }*)
    - assert ( p :  ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }
      exact ((pr1 i) - 1,, p).
    - exact i.
  Defined.



  Definition switch_vector_els { n : nat } (vec : Vector F n) (e1 e2 : ⟦ n ⟧%stn) : Vector F n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i e1).
    - exact (vec e2).
    - induction (stn_eq_or_neq i e2).
      + exact (vec e1).
      + exact (vec i).
  Defined.

  (* k  : 1 -> n - 1 *)
  Definition vec_row_ops_step { n : nat } (k pivot_ik: ⟦ n ⟧%stn)  (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    induction (natlthorgeh i k). 2 : {exact (vec i). }
    set (vec' := switch_vector_els vec pivot_ik k).
    assert (pr2stn1 : 0 < 1). { reflexivity. }
    set ( j := make_stn 1 0 pr2stn1).
    exact (  ((((vec' i)) + ((vec' k)) * (mat i k))%hq)).  (* Would like to verify this construction works*)
  Defined.


  (* This one especially needs to be checked for correctness (use of indices) *)
  Definition back_sub_step { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    set ( m := pr1 i ).
    induction (natlehchoice ((S (pr1 iter)) ) (n)) as [LT | GTH].
    - exact ((((vec i) - Σ (clamp_f vec i)) * (hqmultinv (mat i i)))%hq).
    - exact ((vec i) * (hqmultinv (mat i i)))%hq.
    - unfold stn in i.
      apply (pr2 iter).
  Defined.




  (* Now, three fixpoint definitions for three subroutines.
     Partial pivoting on "A", defining b according to pivots on A,
     then back-substitution. *)
  Fixpoint gauss_iterate
     ( pr1i : nat ) { n : nat } ( current_idx : ⟦ n ⟧%stn)
     (start_idx : ⟦ n ⟧%stn ) (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n) {struct pr1i }
    : (Matrix F n n) × (Vector (⟦ n ⟧%stn) n).
  Proof.
    destruct pr1i as [ | m ].
    { (* pr1i = 0 *) exact (mat,,pivots). }
    clear current_idx. (* TODO: remove it from parameters? check redundancy here with pr1i *)
    set (current_idx := decrement_stn_by_m start_idx (n - (S m))).
    set (idx_nat := pr1 current_idx).
    set (proof   := pr2 current_idx).
    set (mat_vec_tup := ((gauss_step current_idx mat))).
    set (mat' := pr1 mat_vec_tup).
    set (piv  := (pr2 mat_vec_tup)).
    set (pivots' := set_stn_vector_el pivots current_idx piv).
    exact (gauss_iterate m _ current_idx start_idx mat' pivots').
Defined.

Fixpoint vec_ops_iterate ( iter : nat ) { n : nat }  ( start_idx : ⟦ n ⟧%stn) (b : Vector F n) ( pivots : Vector (⟦ n ⟧%stn) n) (mat : Matrix F n n) { struct iter }: Vector F n :=
  let current_idx := decrement_stn_by_m start_idx (n - iter)  in
  match iter with
  | 0 => b
  | S m => vec_ops_iterate m start_idx (vec_row_ops_step current_idx (pivots current_idx) mat b) pivots mat
  end.

Fixpoint back_sub_iterate ( iter : nat ) { n : nat }  ( start_idx : ⟦ n ⟧%stn) (b : Vector F n) ( pivots : Vector (⟦ n ⟧%stn) n) (mat : Matrix F n n) { struct iter }: Vector F n :=
  let current_idx := decrement_stn_by_m start_idx (n - iter)  in
  match iter with
  | 0 => b
  | S m => back_sub_iterate m start_idx ( back_sub_step current_idx mat b) pivots mat
  end.


  (* The main definition using above Fixpoints, which in turn use stepwise definitions.*)
  Definition gaussian_elimination { n : nat } (mat : Matrix F n n) (b : Vector F n) (pn : n > 0) : Matrix F n n × Vector F n.
  Proof.
    set (A_and_pivots := gauss_iterate n (0,,pn) (0,,pn) mat (zero_vector_stn n)).
    set (A  := pr1 A_and_pivots).
    set (pv := pr2 A_and_pivots).
    set (b'  := vec_ops_iterate 0 (0,,pn) b pv A).
    set (b'' := back_sub_iterate n (0,, pn) b' pv A).
    exact (A,, b').
  Defined.



  (* Some properties on the above procedure which we would like to prove. *)

  Definition is_upper_triangular { m n : nat } (mat : Matrix F m n) :=
    ∏ i : ⟦ m ⟧%stn, ∏ j : ⟦ n ⟧%stn, i < j -> mat i j = 0%hq.

  Definition is_upper_triangular_to_k { m n : nat} ( k : nat ) (mat : Matrix F m n) :=
    ∏ i : ⟦ m ⟧%stn, ∏ j : ⟦ n ⟧%stn, i < k -> i < j -> mat i j = 0%hq.


  Lemma gauss_step_clears_row  { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) :
    is_upper_triangular_to_k (pr1 k) (pr1 (gauss_step k mat)).
  Proof.
    intros.
  Abort.

  Lemma A_is_upper_triangular { n : nat} ( temp_proof_0_lt_n : 0 < n ) (mat : Matrix F n n) :
    is_upper_triangular (pr1 (gauss_iterate 0 (0,, temp_proof_0_lt_n) (0,, temp_proof_0_lt_n) mat (zero_vector_stn n))).
  Proof.
    intros.
  Abort.


  (* Reliance on pn, coercing matrices could be done away with. *)
  Lemma sol_is_invariant_under_gauss  {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n)  (pn : n > 0) (pn' : 1 > 0) :
    (A ** x) = (transpose b) -> ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** A ** x)  = ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** (transpose b)).
  Proof.
    intros.
  Abort.





  (* Determinants, minors, minor expansions ... *)

  (* TODO : Verify this is close to accurate ... *)
  Definition make_minor {n : nat} ( i j : ⟦ S n ⟧%stn )  (mat : Matrix F (S n) (S n)) : Matrix F n n.
  Proof.
    intros i' j'.
    assert (bound_si : (S i') < (S n)). {exact (pr2 i'). }
    assert (bound_sj : (S j') < (S n)). {exact (pr2 j'). }
    set (stn_si := make_stn (S n) (S i') bound_si).
    set (stn_sj := make_stn (S n) (S j') bound_sj).
    induction (natgtb i'  (i - 1)).
    - induction (natgtb j' (j - 1)).
      + exact (mat (stnmtostnn n (S n) (natlehnsn n) i') (stnmtostnn n ( S n) (natlehnsn n) j')).
      + exact (mat ((stnmtostnn n (S n) (natlehnsn n) i')) stn_sj).
    - induction (natgtb j' (j - 1)).
      + exact (mat stn_si  (stnmtostnn n ( S n) (natlehnsn n) j')).
      + exact (mat stn_si stn_sj).
  Defined.


  (* TODO: need to figure out the recursive step ! *)
  (*
  Definition determinant_step { n : nat} (mat : Matrix F (S n) (S n)) : (Matrix F n n) × F.
  Proof.
    set (exp_row := 0).
    use tpair.
    - (* Minors *)
      intros i j.
      (* Carefully do induction on S n, not n. *)
      induction (natlthorgeh n 2) as [L | G]. (* Possibly better using natneqchoice on n != 2 *)
        + (* n ∈ ⦃0, 1⦄ *)
(*
          assert (x  : 0 < (S n)). {apply (istransnatgth (S n) n 0).
                                    - apply natlthnsn.
                                    - apply (istransnatgth n 1 0).
                                      + apply
G.
                                      + reflexivity.
                                   }
*)
           induction (nat_eq_or_neq n 1) as [T' | F'].
           * exact 1%hq.
           * exact 0%hq.
        + induction (nat_eq_or_neq n 2) as [T' | F'].
          * exact 1%hq.
          * assert (x  : 0 < (S n)). {apply (istransnatgth (S n) n 0).
                                       - apply natlthnsn.
                                       - apply (istransnatgth n 1 0).
                                         + apply G.
                                         + reflexivity.
                                     }
            assert (x' : 1 < (S n)). {apply (istransnatgth (S n) n 1).
                                       - apply natlthnsn.
                                       - apply G. }
            assert (pexp : exp_row < S n). { reflexivity. }
            assert (psj : (pr1 j) < S n). {  apply natlthtolths. exact (pr2 j). }.
            set (stn_0 := make_stn (S n) 0 x ).
            set (stn_1 := make_stn (S n) 1 x').
            set (cof := 1%hq). (* TODO : this is a dummy for (-1)^(i + j) *)
            exact (Σ (λ j : (⟦ S n ⟧%stn), cof * (mat (exp_row,, pexp) (j)))%hq).
    - (* Scalar terms *)
      intros i j.
      set (exp_row := 0).
      induction (natlthorgeh n 2) as [L | G]. (* Possibly better using natneqchoice on n != 2 *)
        + (* n ∈ ⦃0, 1⦄ *)
           induction (nat_eq_or_neq n 1) as [T' | F'].
           * exact 1%hq.
           * exact 0%hq.
        + induction (nat_eq_or_neq n 2) as [T' | F'].

    induction (natgtb n 1) as [T | F].
    - induction (nat_eq_or_neq n 2) as [T' | F'].
      assert (x :  0 < (S n)). {rewrite T'. reflexivity.}.
      assert (x' : 1 < (S n)). {rewrite T'. reflexivity.}.
      set (stn_0 := make_stn (S n) 0 x).
      set (stn_1 := make_stn (S n) 1 x').
      + exact (1%hq,, (mat stn_0 stn_0) * (mat stn_1 stn_1) - (mat stn_0 stn_1) * (mat stn_1 stn_0))%hq).
      + set (cof := 1). (* TODO : this is a dummy for (-1)^(i + j) *)
        exact (Σ (λ j : (⟦ n ⟧%stn), cof * mat ( exp_row j) (determinant ( make_minor i j mat)))).  (* TODO *)
    - induction (nat_eq_or_neq n 0).
      + exact 0%hq.
      + assert (x :  0 < n). {apply natneq0togth0. assumption.}
        set (stn_0 := make_stn n 0 x).
        exact (mat stn_0 stn_0).
  Defined.
  *)

  (*How do we produce either a smaller matrix or scalar value? *)
  (*
  Fixpoint determinant_iter {n : nat} (mat : Matrix F (S n) (S n)) := Matrix F n n.
  *)


End Gauss.





Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.

  (* Such code might go intro Matrix.v *)
  Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i != (stntonat _ j)) -> (mat i j) = 0%rig.



  Definition MinAij {m n : nat} (A : Matrix I m n) (s : nat) (p : s < min m n) : I.
  Proof.
  Abort.


End SmithNF.
