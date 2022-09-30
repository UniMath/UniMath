 (** * Matrices

Background on vectors, for [Algebra.Elimination.Elimination]

Author: Daniel @Skantz (September 2022)
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Nat.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.Algebra.Elimination.Auxiliary.

Section Misc.
(** * Vectors sans algebra
*)
  Lemma vector_fmap {X Y : UU} (f : X -> Y) {n} : Vector X n -> Vector Y n.
  Proof.
    intros ? ?; auto.
  Defined.

  Lemma iscontr_nil_vector {X : UU} : iscontr (Vector X 0).
  Proof.
    apply iscontrfunfromempty2. apply fromstn0.
  Defined.

End Misc.

Section Vectors.

  (** Additional material on vectors --
      facts for zero vectors, sums, products, standard basis vectors. *)

  Context { R : rig }.

  Local Notation  Σ := (iterop_fun rigunel1 op1).
  Local Notation "v1 *pw v2" := ((pointwise _ op2) v1 v2) (at level 40, left associativity).
  Local Notation "v1 +pw v2" := ((pointwise _ op1) v1 v2) (at level 50, left associativity).

  Definition scalar_lmult_vec (s : R) {n} (vec: Vector R n)
    := vector_fmap (fun x => s * x)%rig vec.

  Definition scalar_rmult_vec {n} (vec: Vector R n) (s : R)
    := vector_fmap (fun x => x * s)%rig vec.

  Lemma zero_function_sums_to_zero:
    ∏ (n : nat)
      (f : (⟦ n ⟧)%stn -> R),
    (λ i : (⟦ n ⟧)%stn, f i) = const_vec 0%rig ->
    (Σ (λ i : (⟦ n ⟧)%stn, f i) ) = 0%rig.
  Proof.
    intros n f X.
    rewrite X.
    unfold const_vec.
    induction n as [| n IH]. {apply idpath. }
    intros. rewrite iterop_fun_step.
    - rewrite rigrunax1; unfold funcomp.
      rewrite IH with ((λ _ : (⟦ n ⟧)%stn, 0%rig));
      try assumption; reflexivity.
    - apply riglunax1.
  Defined.

  Lemma sum_is_ldistr :
    ∏ (n : nat) (vec : Vector R n) (s : R),
    op2 s (Σ vec) =  Σ (scalar_lmult_vec s vec).
  Proof.
    intros. induction n as [| n IH].
    - simpl. apply rigmultx0.
    - rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite rigldistr. rewrite IH.
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      reflexivity.
  Defined.

  Lemma sum_is_rdistr:
    ∏ (n : nat) (vec : Vector R n) (s : R),
    op2 (Σ vec) s =  Σ (scalar_rmult_vec vec s).
  Proof.
    intros. induction n as [| n IH].
    - apply rigmult0x.
    - rewrite iterop_fun_step. 2: { apply riglunax1. }
      rewrite rigrdistr. rewrite IH.
      rewrite iterop_fun_step. 2: { apply riglunax1. }
      reflexivity.
  Defined.

  Lemma rigsum_add :
    ∏ (n : nat) (f1 f2 : (⟦ n ⟧)%stn -> R),
    op1 (Σ (λ i: (⟦ n ⟧)%stn, f1 i))  (Σ (λ i : (⟦ n ⟧)%stn, f2 i))
    = Σ (λ i: (⟦ n ⟧)%stn, op1 (f1 i) (f2 i)).
  Proof.
    intros.
    induction n as [| n IH].
    - assert ( sum0 : Σ (λ i : (⟦ 0 ⟧)%stn, f1 i) = 0%rig). {reflexivity. }
      assert ( sum0': Σ (λ i : (⟦ 0 ⟧)%stn, f2 i) = 0%rig). {reflexivity. }
      rewrite sum0, sum0'.
      apply riglunax1.
    - rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite <- rigassoc1.
      do 3 rewrite -> rigcomm1.
      rewrite <- (rigcomm1 _ (f1 lastelement)).
      rewrite rigassoc1, IH.
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite <- rigassoc1, rigcomm1.
      now rewrite (rigcomm1 R (f2 lastelement) (f1 lastelement)).
  Defined.

  Lemma sum_pointwise_op1 { n : nat } (v1 v2 : Vector R n)
    : Σ (v1 +pw v2) = (Σ v1 + Σ v2)%rig.
  Proof.
    unfold pointwise.
    apply pathsinv0, rigsum_add.
  Defined.

  Lemma interchange_sums :
    ∏ (m n : nat)
      (f : (⟦ n ⟧)%stn ->  (⟦ m ⟧)%stn -> R),
    Σ (λ i: (⟦ m ⟧)%stn, Σ (λ j : (⟦ n ⟧)%stn, f j i) )
    = Σ (λ j: (⟦ n ⟧)%stn, Σ (λ i : (⟦ m ⟧)%stn, f j i)).
  Proof.
    intros. induction n as [| n IH].
    - induction m.
      { reflexivity. }
      change (Σ (λ i : (⟦ 0 ⟧)%stn, Σ ((λ j : (⟦ _ ⟧)%stn, f i j) )))
        with (@rigunel1 R).
      apply zero_function_sums_to_zero.
      reflexivity.
    - rewrite -> iterop_fun_step. 2: { apply riglunax1. }
      unfold funcomp.
      rewrite <- IH, rigsum_add.
      apply maponpaths, funextfun; intros i.
      rewrite -> iterop_fun_step. 2: { apply riglunax1. }
      reflexivity.
  Defined.

  (** The following few lemmata are variants of existing proofs
     for natural numbers. *)

  (** Identical to transport_stnsum but with Σ , R*)
  Lemma transport_rigsum {m n : nat} (e: m = n) (g: ⟦ n ⟧%stn -> R) :
     Σ g =  Σ (λ i, g (transportf stn e i)).
  Proof.
    intros; now induction e.
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
      now rewrite <- stn_left_0.
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
    now induction e.
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
        apply subtypePath_prop, idpath.
  Defined.

  Lemma rigsum_to_rightsum {n m' n' : nat} (p : m' + n' = n) (f :  ⟦ m' + n' ⟧%stn -> R)
    (left_part_is_zero : (f ∘ stn_left m' n') = const_vec 0%rig):
    iterop_fun 0%rig op1 f = iterop_fun 0%rig op1 (f ∘ stn_right m' n' ).
  Proof.
    rewrite rigsum_left_right, zero_function_sums_to_zero.
    - now rewrite riglunax1.
    - now rewrite (left_part_is_zero ).
  Defined.

  Lemma rigsum_to_leftsum {n m' n' : nat} (p : m' + n' = n) (f :  ⟦ m' + n' ⟧%stn -> R)
    (right_part_is_zero : (f ∘ stn_right m' n') = const_vec 0%rig):
    iterop_fun 0%rig op1 f = iterop_fun 0%rig op1 (f ∘ stn_left m' n' ).
  Proof.
    rewrite rigsum_left_right, rigcomm1, zero_function_sums_to_zero.
    - now rewrite riglunax1.
    - now rewrite right_part_is_zero.
  Defined.

  Definition is_pulse_function { n : nat } ( i : ⟦ n ⟧%stn )
  (f : ⟦ n ⟧%stn -> R)
    := ∏ (j: ⟦ n ⟧%stn), (i ≠ j) -> (f j = 0%rig).

  (** Some lemmata on vectors with one or two non-zero values.
      Useful later for computations using standard basis vectors,
      identity matrix, elementary row operations. *)
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
    assert (i_neq_dni : i ≠ dni i k). {exact (dni_neq_i i k). }
    intros; destruct (stn_eq_or_neq i (dni i k) ) as [eq | neq].
      - apply (stnneq_iff_nopath i (dni i k)) in eq.
        apply weqtoempty. intros. apply eq. assumption.
        exact (dni_neq_i i k).
      - apply f_pulse_function; exact neq.
  Defined.

  Lemma empty_sum_eq_0 (v1 : Vector R 0) : Σ v1 = 0%rig.
  Proof.
    reflexivity.
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
    now rewrite (stn_eq_or_neq_right i_neq_j).
  Defined.

  Lemma is_pulse_function_stdb_vector
      { n : nat } (i : ⟦ n ⟧%stn)
    : is_pulse_function i (stdb_vector i).
  Proof.
    intros j i_neq_j.
    unfold stdb_vector, pointwise.
    now rewrite (stn_eq_or_neq_right i_neq_j).
  Defined.

  Lemma stdb_vector_sums_to_1 { n : nat } (i : ⟦ n ⟧%stn)
    : Σ (@stdb_vector n i) = 1%rig.
  Proof.
    etrans.
    { apply (pulse_function_sums_to_point _ i), is_pulse_function_stdb_vector. }
    unfold stdb_vector; now rewrite stn_eq_or_neq_refl.
  Defined.

  Lemma pulse_prod_is_pulse {n : nat}
    (f g : stn n -> R) {i : stn n} (H : is_pulse_function i f)
    : is_pulse_function i (f *pw g).
  Proof.
    unfold is_pulse_function in * |- ; intros j.
    intros neq; unfold pointwise.
    replace (f j) with (@rigunel1 R).
    - apply rigmult0x.
    - now rewrite H.
  Defined.

  Lemma sum_stdb_vector_pointwise_prod { n : nat } (v : Vector R n) (i : ⟦ n ⟧%stn)
    : Σ (stdb_vector i *pw v) = (v i).
  Proof.
    etrans.
    { apply
        (pulse_function_sums_to_point _ i)
      , (pulse_prod_is_pulse _ _ )
      , is_pulse_function_stdb_vector. }
    unfold pointwise, stdb_vector.
    rewrite stn_eq_or_neq_refl.
    apply riglunax2.
  Defined.

  Lemma pointwise_prod_stdb_vector {n : nat} (v : Vector R n) (i : ⟦ n ⟧%stn)
    : v *pw (stdb_vector i) = scalar_lmult_vec (v i) (stdb_vector i).
  Proof.
    apply funextfun. intros j.
    unfold scalar_lmult_vec, vector_fmap, pointwise.
    destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
    - rewrite i_eq_j; apply idpath.
    - unfold stdb_vector.
      rewrite (stn_eq_or_neq_right i_neq_j).
      now do 2 rewrite rigmultx0.
  Defined.

  Lemma two_pulse_function_sums_to_points { n : nat }
      (f : ⟦ n ⟧%stn -> R)
      (i : ⟦ n ⟧%stn) (j : ⟦ n ⟧%stn) (ne_i_j : i ≠ j)
      (f_two_pulse : ∏ (k: ⟦ n ⟧%stn), (k ≠ i) -> (k ≠ j) -> (f k = 0%rig))
    : (Σ f = f i + f j)%rig.
  Proof.
    assert (H : f = (scalar_lmult_vec (f i) (stdb_vector i))
                    +pw (scalar_lmult_vec (f j) (stdb_vector j))).
    { apply funextfun. intros k.
      unfold stdb_vector, scalar_lmult_vec, vector_fmap, pointwise.
      destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k].
      - destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k]; destruct i_eq_k.
        + destruct j_eq_k.
          now apply isirrefl_natneq in ne_i_j.
        + now rewrite rigmultx0, rigrunax1, rigrunax2.
      - rewrite rigmultx0, riglunax1.
        destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
        + now rewrite rigrunax2, j_eq_k.
        + rewrite rigmultx0; apply f_two_pulse; now apply issymm_natneq.
    }
    etrans. { apply maponpaths, H. }
    etrans. { apply sum_pointwise_op1. }
    apply maponpaths_12;
    rewrite <- sum_is_ldistr, stdb_vector_sums_to_1; apply rigrunax2.
  Defined.

  Definition zero_vector_nat (n : nat) : ⟦ n ⟧%stn -> nat :=
    λ i : ⟦ n ⟧%stn, 0%nat.

  Lemma vector_1_inj { X : rig } { n : nat } (e1 e2 : X)
    : (λ y : (⟦ 1 ⟧)%stn, e1) = (λ y : (⟦ 1 ⟧)%stn, e2) -> e1 = e2.
  Proof.
    intros eq; apply (invmaponpathsweq (@weq_vector_1 X)  _ _ eq).
  Defined.

  Lemma weq_rowvec
    : ∏ X : UU, ∏ n : nat, Vector X n ≃ Matrix X 1 n.
  Proof.
    intros; apply weq_vector_1.
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

  Lemma row_vec_inj { X : rig } { n : nat } (v1 v2 : Vector X n)
    : row_vec v1 = row_vec v2 -> v1 = v2.
  Proof.
    intros H; apply (invmaponpathsweq (@weq_rowvec X n)  _ _ H).
  Defined.

  Lemma const_vec_eq  {X : UU} {n : nat} (v : Vector X n) (e : X) (i : ⟦ n ⟧%stn)
    : v = const_vec e -> v i = e.
  Proof.
    intros eq. rewrite eq. reflexivity.
  Defined.

  Lemma col_vec_eq {X : UU} {n : nat} (v : Vector X n)
  : ∏ i : (stn 1), v = col (col_vec v) i.
  Proof. easy. Defined.

  Lemma pointwise_rdistr_vector { n : nat } (v1 v2 v3 : Vector R n)
    : (v1 +pw v2) *pw v3 = (v1 *pw v3) +pw (v2 *pw v3).
  Proof.
    use (pointwise_rdistr (rigrdistr R)).
  Defined.

  Lemma pointwise_assoc2_vector { n : nat } (v1 v2 v3 : Vector R n)
    : (v1 *pw v2) *pw v3 = v1 *pw (v2 *pw v3).
  Proof.
    use (pointwise_assoc (rigassoc2 R)).
  Defined.

  Lemma pointwise_comm2_vector {CR: commrig} { n : nat } (v1 v2 : Vector CR n)
    : v1 *pw v2 = v2 *pw v1.
  Proof.
    use (pointwise_comm (rigcomm2 CR)).
  Defined.

End Vectors.
