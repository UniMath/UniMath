 (** * Matrices

Background on vectors, for [Algebra.Elimination.Elimination]

Author: @Skantz (April 2021)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.Algebra.Elimination.Auxiliary.


Section Vectors.

  Context { R : rig }.

  Local Notation  Σ := (iterop_fun rigunel1 op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* The following few lemmata are slight generalizations of the pre-existing proofs
     for natural numbers. Could be upstreamed. *)

  (* Identical to transport_stnsum but with Σ , R*)
  Lemma transport_rigsum {m n : nat} (e: m = n) (g: ⟦ n ⟧%stn -> R) :
     Σ g =  Σ (λ i, g (transportf stn e i)).
  Proof.
    intros.
    induction e.
    apply idpath.
  Defined.

  Lemma rigsum_eq {n : nat} (f g : ⟦ n ⟧%stn -> R) : f ~ g ->  Σ f =  Σ g.
  Proof.
    intros H.
    induction n as [|n IH]; try apply idpath.
    rewrite 2 iterop_fun_step; try apply riglunax1.
      induction (H lastelement).
      apply (maponpaths (λ i, op1 i (f lastelement))).
      apply IH; intro x; apply H.
  Defined.

  Lemma rigsum_step {n : nat} (f : ⟦ S n ⟧%stn -> R) :
    Σ f = op1 (Σ (f ∘ (dni lastelement))) (f lastelement).
  Proof.
    intros; apply iterop_fun_step; apply riglunax1.
  Defined.

  Lemma rigsum_left_right :
  ∏ (m n : nat) (f : (⟦ m + n ⟧)%stn → R),
   Σ f =  op1 (Σ (f ∘ stn_left m n)) (Σ (f ∘ stn_right m n)).
  Proof.
    intros.
    induction n as [| n IHn].
    { change (Σ  _) with (@rigunel1 R) at 3.
      set (a := m + 0). assert (a = m). { apply natplusr0. }
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
        rewrite stn_right_compute. unfold stntonat. induction e.
        rewrite idpath_transportf. rewrite 2? dni_last.
        apply idpath. } }
    unfold funcomp. apply maponpaths. apply subtypePath_prop.
    induction e. apply idpath.
  Defined.

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
      rewrite rigassoc1. rewrite (@rigcomm1 R (f _) ). rewrite  <- rigassoc1.
      apply map_on_two_paths.
      + apply map_on_two_paths.
        * apply rigsum_eq; intro i. induction i as [i I].
          apply maponpaths. apply subtypePath_prop.
          induction e. rewrite idpath_transportf. rewrite stn_left_compute.
          unfold dni,di, stntonat; simpl.
          induction (natlthorgeh i j) as [R'|R'].
          -- unfold stntonat; simpl; rewrite transport_stn; simpl.
             induction (natlthorgeh i j) as [a|b].
             ++ apply idpath.
             ++ contradicts R' (natlehneggth b).
          -- unfold stntonat; simpl; rewrite transport_stn; simpl.
             induction (natlthorgeh i j) as [V|V].
             ++ contradicts I (natlehneggth R').
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

  Lemma rigsum_to_rightsum {n m' n' : nat} (p : m' + n' = n) (f :  ⟦ m' + n' ⟧%stn -> R)
    (left_part_is_zero : (f ∘ stn_left m' n') = const_vec 0%rig):
    iterop_fun 0%rig op1 f = iterop_fun 0%rig op1 (f ∘ stn_right m' n' ).
  Proof.
    rewrite rigsum_left_right, zero_function_sums_to_zero.
    - rewrite riglunax1.
      apply idpath.
    - rewrite (left_part_is_zero ).
      apply idpath.
  Defined..

  Lemma rigsum_to_leftsum {n m' n' : nat} (p : m' + n' = n) (f :  ⟦ m' + n' ⟧%stn -> R)
    (right_part_is_zero : (f ∘ stn_right m' n') = const_vec 0%rig):
    iterop_fun 0%rig op1 f = iterop_fun 0%rig op1 (f ∘ stn_left m' n' ).
  Proof.
    rewrite rigsum_left_right, rigcomm1, zero_function_sums_to_zero.
    - rewrite riglunax1.
      apply idpath.
    - rewrite (right_part_is_zero).
      apply idpath.
  Defined.

  Definition is_pulse_function { n : nat } ( i : ⟦ n ⟧%stn ) 
  (f : ⟦ n ⟧%stn -> R)
  := ∏ (j: ⟦ n ⟧%stn), (i ≠ j) -> (f j = 0%rig).

  Lemma pulse_function_sums_to_point { n : nat }
    (f : ⟦ n ⟧%stn -> R) (i : ⟦ n ⟧%stn)
    (f_pulse_function : is_pulse_function i f)
    : Σ f = f i.
  Proof.
    destruct (stn_inhabited_implies_succ i) as [n' e_n_Sn'].
    destruct (!e_n_Sn').
    rewrite (rigsum_dni f i).
    rewrite zero_function_sums_to_zero.
    { rewrite riglunax1. apply idpath. }
    apply funextfun; intros k.
    unfold funcomp.
    replace (const_vec 0%rig k) with (@rigunel1 R). 2: { reflexivity. }
    assert (i_neq_dni : i ≠ dni i k) . {exact (dni_neq_i i k). }
    - intros. destruct (stn_eq_or_neq i (dni i k) ) as [eq | neq].
        + apply (stnneq_iff_nopath i (dni i k)) in eq.
          apply weqtoempty. intros. apply eq. assumption.
          exact (dni_neq_i i k). (* Move up *)
        + apply f_pulse_function. exact neq.
  Defined.

  Lemma empty_sum_eq_0  (v1 : Vector R 0) : Σ v1 = 0%rig.
  Proof.
    reflexivity.
  Defined.

  (* TODO resolve this situation with multiple aliases for essentially the same lemma
    - this is just rigsum_add. *)
  Lemma sum_pointwise_op1 { n : nat } (v1 v2 : Vector R n)
    : Σ (pointwise n op1 v1 v2) = (Σ v1 + Σ v2)%rig.
  Proof.
    unfold pointwise.
    apply pathsinv0.
    apply rigsum_add.
  Defined.

  Definition stdb_vector { n : nat } (i : ⟦ n ⟧%stn) : Vector R n.
  Proof.
    intros j.
    induction (stn_eq_or_neq i j).
    - exact rigunel2.
    - exact rigunel1.
  Defined.

  Definition stdb_ii {n : nat} (i : ⟦ n ⟧%stn)
    : (stdb_vector i) i = rigunel2.
  Proof.
    unfold stdb_vector; rewrite (stn_eq_or_neq_refl); apply idpath.
  Defined.

  Definition stdb_ij {n : nat} (i j : ⟦ n ⟧%stn)
    : i ≠ j -> (stdb_vector i) j = rigunel1.
  Proof.
    intros i_neq_j. unfold stdb_vector.
    rewrite (stn_eq_or_neq_right i_neq_j). apply idpath.
  Defined.

  Lemma is_pulse_function_stdb_vector
      { n : nat } (i : ⟦ n ⟧%stn)
    : is_pulse_function i (stdb_vector i).
  Proof.
    intros j i_neq_j.
    unfold stdb_vector, pointwise.
    rewrite (stn_eq_or_neq_right i_neq_j).
    reflexivity.
  Defined.

  Lemma stdb_vector_sums_to_1 { n : nat } (i : ⟦ n ⟧%stn)
    : Σ (@stdb_vector n i) = 1%rig.
  Proof.
    etrans.
    { apply (pulse_function_sums_to_point _ i), is_pulse_function_stdb_vector. }
    unfold stdb_vector.
    rewrite stn_eq_or_neq_refl.
    apply idpath.
  Defined.

  Lemma pulse_prod_is_pulse {n : nat}
    (f g : stn n -> R) {i : stn n} (H : is_pulse_function i f)
    : is_pulse_function i (f ^ g).
  Proof.
    unfold is_pulse_function in *; intros j.
    intros neq; unfold pointwise.
    replace (f j) with (@rigunel1 R).
    - apply rigmult0x.
    - rewrite H; try reflexivity; assumption.
  Defined.

  Lemma sum_stdb_vector_pointwise_prod { n : nat } (v : Vector R n) (i : ⟦ n ⟧%stn)
    : Σ (stdb_vector i ^ v) = (v i).
  Proof.
    etrans.
    { apply (pulse_function_sums_to_point _ i).
      apply (pulse_prod_is_pulse _ _ ).
      apply is_pulse_function_stdb_vector. }
    unfold pointwise, stdb_vector.
    rewrite stn_eq_or_neq_refl.
    apply riglunax2.
  Defined.

  Lemma pointwise_prod_stdb_vector {n : nat} (v : Vector R n) (i : ⟦ n ⟧%stn)
    : v ^ (stdb_vector i) = scalar_lmult_vec (v i) (stdb_vector i).
  Proof.
    apply funextfun. intros j.
    unfold scalar_lmult_vec, const_vec, pointwise.
    destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
    - rewrite i_eq_j; apply idpath.
    - unfold stdb_vector.
      rewrite (stn_eq_or_neq_right i_neq_j).
      do 2 rewrite rigmultx0.
      apply idpath.
  Defined.

  Lemma two_pulse_function_sums_to_points { n : nat }
      (f : ⟦ n ⟧%stn -> R)
      (i : ⟦ n ⟧%stn) (j : ⟦ n ⟧%stn) (ne_i_j : i ≠ j)
      (X : ∏ (k: ⟦ n ⟧%stn), (k ≠ i) -> (k ≠ j) -> (f k = 0%rig))
    : (Σ f = f i + f j)%rig.
  Proof.
    assert (H : f = pointwise n op1  (scalar_lmult_vec (f i) (stdb_vector i))
                    (scalar_lmult_vec (f j) (stdb_vector j))).
    { unfold pointwise.
      apply funextfun. intros k.
      unfold stdb_vector, scalar_lmult_vec, pointwise, const_vec.
      destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k].
      - destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
        + rewrite i_eq_k in ne_i_j.
          rewrite j_eq_k in ne_i_j.
          apply isirrefl_natneq in ne_i_j.
          contradiction.
        + rewrite rigmultx0, rigrunax1, rigrunax2.
          rewrite i_eq_k.
          reflexivity.
      - rewrite rigmultx0, riglunax1.
        destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
        + rewrite rigrunax2.
          rewrite j_eq_k.
          apply idpath.
        + rewrite rigmultx0.
          apply X.
          * apply issymm_natneq. assumption.
          * apply issymm_natneq. assumption.
    }
    rewrite H, sum_pointwise_op1.
    unfold scalar_lmult_vec.
    rewrite <- (sum_is_ldistr _ (stdb_vector i)).
    rewrite <- (sum_is_ldistr _ (stdb_vector j)).
    do 2 rewrite stdb_vector_sums_to_1, rigrunax2.
    unfold pointwise, stdb_vector.
    do 2 rewrite stn_eq_or_neq_refl.
    apply issymm_natneq in  ne_i_j.
    rewrite (stn_eq_or_neq_right ne_i_j); simpl.
    apply issymm_natneq in ne_i_j.
    rewrite (stn_eq_or_neq_right ne_i_j); simpl.
    do 2 rewrite rigmultx0.
    rewrite rigrunax1, riglunax1.
    do 2 rewrite rigrunax2.
    apply idpath.
  Defined.

  Definition zero_vector_nat (n : nat) : ⟦ n ⟧%stn -> nat :=
    λ i : ⟦ n ⟧%stn, 0%nat.

  Definition zero_vector_stn (n : nat) : ⟦ n ⟧%stn -> ⟦ n ⟧%stn :=
    λ i : ⟦ n ⟧%stn, (0%nat,, (natneq0to0lth _ (stn_implies_nneq0 i))).

  Lemma vector_1_inj { X : rig } { n : nat } (e1 e2 : X)
    : (λ y : (⟦ 1 ⟧)%stn, e1) = (λ y : (⟦ 1 ⟧)%stn, e2) -> e1 = e2.
  Proof.
    intros eq.
    apply (invmaponpathsweq (@weq_vector_1 X)  _ _ eq).
  Defined.

  Lemma weq_rowvec
    : ∏ X : UU, ∏ n : nat, Vector X n ≃ Matrix X 1 n.
  Proof.
    intros.
    apply weq_vector_1.
  Defined.

  Lemma weq_colvec
    : ∏ X : UU, ∏ n : nat, weq (Vector X n) (Matrix X n 1).
  Proof.
    intros.
    apply weqffun.
    apply weq_vector_1.
  Defined.

  Lemma col_vec_inj { X : rig } { n : nat } (v1 v2 : Vector X n)
    : col_vec v1 = col_vec v2 -> v1 = v2.
  Proof.
    intros H.
    apply (invmaponpathsweq (@weq_colvec X n)  _ _ H).
  Defined.

  Lemma col_vec_inj_pointwise { X : rig } { n : nat } (v1 v2 : Vector X n)
    : forall i : (stn n), (col_vec v1 i) = (col_vec v2 i) -> (v1 i) = (v2 i).
  Proof.
    intros i eq.
    apply (invmaponpathsweq (@weq_vector_1 X)  _ _ eq).
  Defined.

  Lemma row_vec_inj { X : rig } { n : nat } (v1 v2 : Vector X n)
    : row_vec v1 = row_vec v2 -> v1 = v2.
  Proof.
    intros H.
    apply (invmaponpathsweq (@weq_rowvec X n)  _ _ H).
  Defined.

  Lemma const_vec_eq  {X : UU} {n : nat} (v : Vector X n) (e : X) (i : ⟦ n ⟧%stn)
    : v = const_vec e -> v i = e.
  Proof.
    intros eq. rewrite eq. reflexivity.
  Defined.

  Lemma col_vec_eq {X : UU} {n : nat} (v : Vector X n)
  : ∏ i : (stn 1), v = col (col_vec v) i.
  Proof.
    reflexivity.
  Defined.

End Vectors.