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
Require Import UniMath.Tactics.Nat_Tactics.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.PAdics.z_mod_p.


(* Which of these contextual definitions and notations if any should be included here? *)
(*Local Definition R := pr1hSet natcommrig.*)
(* Context { R : rig }. *)
Local Definition F := hq. (* TODO we probably don't want this and presumably not here at top level - remove *)
Opaque F.

(* The first few sections contain Definitions and Lemmas that
   should be moved further up the project tree *)

(* Local Notation "A ** B" := (matrix_mult A B) (at level 80).
Local Notation  Σ := (iterop_fun 0%hq op1).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2). *)


Section Misc.

  Definition min' (n m : nat) : nat.
  Proof.
    induction (natgthorleh n m).
    - exact m.
    - exact n.
  Defined.

  Lemma min'_eq_min (n m : nat) : min n m = min' n m.
  Proof.
  Abort.

  Lemma min_le_b: ∏ a b : (nat), min a b ≤ b.
  Proof.
    intros.
    unfold min.
    revert a.
    induction b; destruct a ; try reflexivity.
    apply IHb.
  Defined.

  Lemma min_le_a: ∏ a b : (nat), min a b ≤ a.
  Proof.
    intros.
    unfold min.
    revert a.
    induction b; destruct a ; try reflexivity.
    apply IHb.
  Defined.

  Lemma min_eq_a_or_eq_b :  ∏ a b : (nat),  coprod (min a b = a) (min a b  = b).
  Proof.
    intros.
    destruct (natgthorleh a b).
    - apply ii2.
      unfold min.
      revert h. revert b.
      induction a; destruct b; try reflexivity.
      { intros. apply fromempty. apply negnatgth0n in h. assumption.  }
      intros.
      rewrite IHa.
      {  reflexivity. }
      apply h.
    - apply ii1.
      unfold min.
      revert h. revert b.
      induction a; destruct b; try reflexivity.
      { intros.
        apply negnatlehsn0 in h.
        apply fromempty; assumption.
      }
      intros.
      rewrite IHa.
      {  reflexivity. }
      apply h.
  Defined.

  Lemma minsymm (a b : nat) : min a b = min b a.
  Proof.
  Abort.

  Lemma minabstn_to_astn { a b : nat } (i : ⟦ min a b ⟧%stn) : ⟦ a ⟧%stn.
  Proof.
    intros.
    refine (pr1 i,, _).
    exact (natlthlehtrans _ _ _ (pr2 i)  (min_le_a a b)).
  Defined.
  Lemma minabstn_to_bstn { a b : nat } (i : ⟦ min a b ⟧%stn) : ⟦ b ⟧%stn.
  Proof.
    intros.
    refine (pr1 i,, _).
    exact (natlthlehtrans _ _ _ (pr2 i)  (min_le_b a b)).
  Defined.

  Lemma natminus1lthn (n : nat) : n > 0 -> n - 1 < n.
  Proof.
    intros n_gt_0.
    apply natminuslthn.
    - assumption.
    - reflexivity.
  Defined.

End Misc.


Section PrelStn.

  Lemma nat_neq_or_neq_refl (i : nat) : nat_eq_or_neq i i = inl (idpath i).
  Proof.
    intros.
    destruct (nat_eq_or_neq i i) as [ ? | cnt].
    2 : { remember cnt as cnt'. clear Heqcnt'.
          apply isirrefl_natneq in cnt. contradiction. }
    apply maponpaths.
    apply proofirrelevance.
    apply isaproppathsfromisolated.
    apply isisolatedn.
  Defined.

  Lemma fromnatcontr {X : UU} (m n : nat) : (m = n) -> (m ≠ n) -> X.
  Proof.
    intros m_eq_n m_neq_n.
    rewrite m_eq_n in m_neq_n.
    apply isirrefl_natneq in m_neq_n.
    apply fromempty.
    exact (m_neq_n). (* Do we prefer to rename this premise before applying it? *)
  Defined.


  (* TODO refactor the three-step contradiction since it's used everywhere  *)
  (* Also, can we simply use  *)
  Lemma nat_eq_or_neq_left: ∏ {i j: nat} (p : (i = j)),
                            nat_eq_or_neq i j = inl p.
  Proof.
    intros i j i_eq_j.
    rewrite i_eq_j.
    apply nat_neq_or_neq_refl.
  Defined.

  Lemma nat_eq_or_neq_right: ∏ {i j: nat} (p : (i ≠ j)),
                            nat_eq_or_neq i j = inr p.
  Proof.
    intros i j i_neq_j.
    destruct (nat_eq_or_neq i j) as [i_eq_j | ?].
    - apply (fromnatcontr i j i_eq_j i_neq_j).
    - apply proofirrelevance.
      apply isapropcoprod.
      + apply isaproppathsfromisolated.
        apply isisolatedn.
      + apply propproperty.
      + intros i_eq_j.
        apply (fromnatcontr i j i_eq_j i_neq_j).
  Defined.

      (* TODO: look for other places this can simplify proofs! and upstream? *)
  Lemma stn_neq_or_neq_refl {n} {i : ⟦ n ⟧%stn} : stn_eq_or_neq i i = inl (idpath i).
  Proof.
    intros.
    unfold stn_eq_or_neq.
    simpl.
    destruct (nat_eq_or_neq i i).  (* TODO rewrite h*)
    2 : { remember h as h'. clear Heqh'. apply isirrefl_natneq in h. contradiction. } (* i ≠ i, i in stn*)
    rewrite coprod_rect_compute_1.
    apply maponpaths.
    remember p as p'. clear Heqp'.
    apply subtypePath_prop in p.
    set (fst := pr1 i).
    assert (X : fst = fst). { apply idpath. }
    apply proofirrelevance.
    apply isaproppathsfromisolated.
    apply isisolatedinstn.
  Defined.


   (* TODO: naming ? upstream?  Certainly rename p, p0. *)
  Lemma stn_eq_or_neq_left : ∏ {n : nat} {i j: (⟦ n ⟧)%stn} (p : (i = j)),
                              stn_eq_or_neq i j = inl p.
  Proof.
    intros ? ? ? p. rewrite p. apply stn_neq_or_neq_refl.
  Defined.

  Lemma stn_eq_or_neq_right : ∏ {n : nat} {i j : (⟦ n ⟧)%stn} (p : (i ≠ j)),
    stn_eq_or_neq i j = inr p.
  Proof.
    intros ? ? ? p. unfold stn_eq_or_neq.
    destruct (nat_eq_or_neq i j).
    - apply fromempty. rewrite p0 in p.
       apply isirrefl_natneq in p.
       assumption.
    -  apply isapropcoprod.
       + apply stn_ne_iff_neq in p. apply isdecpropfromneg.  assumption.
       (*apply stn_ne_iff_neq in p.*)
       + apply negProp_to_isaprop.
       + intros i_eq_j.
         rewrite i_eq_j in p.
         apply isirrefl_natneq in p.
         apply fromempty. assumption.
  Defined.

  (* Consider a version A : UU -> i : ⟦ n ⟧%stn -> p : n = 0 ->  A? *)
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

  (* And the following two seem completely unecessary and needlessly confusing - if not the forthcoming 4... *)
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

  Lemma snlehtotonlt (m n : nat) : n > 0 -> (S n ≤ m) -> n < m.
  Proof.
    intros ngt0 snltm.
    assert (n_lt_sn : n < S n).
      { apply natlthnsn. }
    apply natlehsntolth.
      assumption.
  Defined.

  Lemma stn_eq_nat_eq { n : nat} (i j : ⟦ n ⟧%stn) : i = j <-> (pr1 i = pr1 j).
  Proof.
    split.
    - intros i_eq_j.
      { rewrite i_eq_j. apply idpath. }
    - intros pr1i_eq_pr1j.
      { apply subtypePath_prop; assumption. }
  Defined.

  Lemma stn_neq_nat_neq { n : nat} (i j : ⟦ n ⟧%stn) : i ≠ j <-> (pr1 i ≠ pr1 j).
  Proof.
    split.
    - intros i_neq_j.
      { apply i_neq_j. }
    - intros pr1i_neq_pr1j.
      { apply pr1i_neq_pr1j. }
  Defined.

  Lemma stnmn_to_stn0n { X : UU } {n : nat} (i : ⟦ n ⟧%stn) : ⟦ n ⟧%stn.
  Proof.
    destruct n.
    - apply weqstn0toempty in i. contradiction.
    - exact (make_stn (S n) 0 (natgthsn0 0)).
  Defined.

  Lemma stnmn_to_stn01 { X : UU } {n : nat} (i : ⟦ n ⟧%stn) : ⟦ 1 ⟧%stn.
  Proof.
    destruct n.
    - apply weqstn0toempty in i. contradiction.
    - exact (make_stn (S 0) 0 (natgthsn0 0)).
  Defined.

  Lemma issymm_stnneq (A : UU) {n : nat} (i j : ⟦ n ⟧%stn) :
    (i ≠ j) <-> (j ≠ i).
  Proof.
    split.
    - intros i_neq_j.
      destruct i, j.
  Abort.

End PrelStn.


Section Vectors.

  Context { R : rig }.

  Local Notation  Σ := (iterop_fun rigunel1 op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  (* The following few lemmata are slight generalizations of the pre-existing proofs
     for natural numbers *)

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
    iterop_fun 0%rig op1  f = iterop_fun 0%rig op1 (f ∘ stn_right m' n' ).
  Proof.
    unfold funcomp.
    rewrite rigsum_left_right.
    rewrite zero_function_sums_to_zero.
    - rewrite riglunax1.
      reflexivity.
    - rewrite (left_part_is_zero ).
      apply idpath.
  Defined.


  Definition is_pulse_function { n : nat } ( i : ⟦ n ⟧%stn )  (f : ⟦ n ⟧%stn -> R) :=
   ∏ (j: ⟦ n ⟧%stn), (i ≠ j) -> (f j = 0%rig).

  Lemma stn_inhabited_implies_succ {n:nat} (i : ⟦ n ⟧%stn)
    : ∑ m, n = S m.
  Proof.
    destruct n as [ | m].
    - destruct i as [i le_i_0].
      destruct (nopathsfalsetotrue le_i_0).
    - exists m. apply idpath.
  Defined.

  (* TODO standardize, get rid of multiple versions ('' is the main one ? *)
  Lemma pulse_function_sums_to_point_rig'' { n : nat }  (f : ⟦ n ⟧%stn -> R) (p : n > 0) :
  ∏ (i : ⟦ n ⟧%stn ),  (∏ (j : ⟦ n ⟧%stn), ((i ≠ j) -> (f j = 0%rig))) ->  (Σ f = f i).
  Proof.
    intros i.
    destruct (stn_inhabited_implies_succ i) as [n' e_n_Sn'].
    destruct (!e_n_Sn').
    intros j.
    rewrite (rigsum_dni f i).
    rewrite zero_function_sums_to_zero. (* TODO rephrase in terms of stnsum_const *)
    { rewrite riglunax1. apply idpath. }
    apply funextfun; intros k.
    unfold funcomp.
    replace (const_vec 0%rig k) with (@rigunel1 R). 2: { reflexivity. }
    assert (i_neq_dni : i ≠ dni i k) . {exact (dni_neq_i i k). }
    - intros. destruct (stn_eq_or_neq i (dni i k) ) as [eq | neq].
        + apply (stnneq_iff_nopath i (dni i k)) in eq.
          apply weqtoempty. intros. apply eq. assumption.
          exact (dni_neq_i i k). (* Move up *)
        + apply j. exact neq.
  Defined.

  Definition drop_el_vector { n : nat } (f : ⟦ S n ⟧%stn -> R) (i : ⟦ S n ⟧%stn) :
    ⟦ n ⟧%stn -> R.
  Proof.
    intros X.
    induction (natlthorgeh X i) as [X_le_i | X_geq_i].
    - assert (e : X < S n ).
      { set (p := pr2 X).
        apply (istransnatgth (S n) n X (natgthsnn n) (pr2 X)).
      }
      exact (f ((pr1  X),, e)).

    - assert (e :S ( X ) < S n ).
      { set (p := pr2 X).
        apply p. }
      exact (f (S X,, e)).
  Defined.

  (* Used to be in PAdics *)
  Lemma minussn1 ( n : nat ) : n ≤ ( S n ) - 1.
  Proof.
    intros. destruct n. apply idpath.
    assert (e : (S (S n)) > (S n)).
    { apply natgthsnn. }
    apply natgthtogehm1 in e. assumption.
  Defined.

  Lemma dnisum_dropsum : ∏ (n : nat) (f : (⟦ S n ⟧)%stn → R) (j : (⟦ S n ⟧)%stn),
                         Σ ((drop_el_vector f j)) = Σ ((f ∘ (dni j) )).
  Proof.
    intros.
    apply maponpaths.
    unfold funcomp, dni, di.  unfold drop_el_vector.
    apply funextfun. intros k.
    destruct (natlthorgeh k j).
    - do 2 rewrite coprod_rect_compute_1.
      unfold natgthtogths.
      apply maponpaths.
      reflexivity.
    - do 2 rewrite coprod_rect_compute_2.
      apply idpath.
  Defined.

  Lemma rigsum_drop_el : ∏ (n : nat) (f : (⟦ S n ⟧)%stn → R) (j : (⟦ S n ⟧)%stn),
    Σ f = (Σ ((drop_el_vector f j)) + f j)%ring.
  Proof.
    intros.
    rewrite (rigsum_dni f j).
    rewrite dnisum_dropsum.
    apply idpath.
  Defined.

  Lemma empty_sum_eq_0  (v1 : Vector R 0) : Σ v1 = 0%rig.
  Proof.
    apply zero_function_sums_to_zero.
    apply funextfun. intros i.
    apply fromempty. apply weqstn0toempty.
    assumption.
  Defined.

  Lemma sum_pointwise_op1 { n : nat } (v1 v2 : Vector R n) : Σ (pointwise n op1 v1 v2) = (Σ v1 + Σ v2)%rig.
  Proof.
    unfold pointwise.
    induction n.
    - rewrite zero_function_sums_to_zero.
      + assert (p1: Σ v1 = 0%rig). { apply (empty_sum_eq_0 v1). }
        assert (p2: Σ v2 = 0%rig). { apply (empty_sum_eq_0 v2). }
        rewrite p1, p2.
        rewrite riglunax1. apply idpath.
      + unfold const_vec.
        apply funextfun. intros i.
        apply fromempty. apply weqstn0toempty in i.
        assumption.
    - rewrite iterop_fun_step. 2: {apply riglunax1. }
      unfold funcomp. rewrite replace_dni_last.
      rewrite <- rigassoc1.
      rewrite eqlen_vec_sums_mergeable. (* todo not the best name*)
      rewrite (rigassoc1 R _ _  (v1 _) ).
      rewrite <- (rigcomm1 _ (v1 _)).
      rewrite (rigassoc1 R _ _ (v2 _)).
      rewrite  (rigassoc1 R (v1 _ ) _ _).
      rewrite <- (rigassoc1 R _ (v1 _) _).
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      rewrite iterop_fun_step. 2: {apply riglunax1. }
      unfold funcomp.
      rewrite replace_dni_last.
      reflexivity.
  Defined.

  Definition stdb_vector { n : nat } (i : ⟦ n ⟧%stn) : Vector R n.
  Proof.
    intros j.
    destruct (stn_eq_or_neq i j).
    - exact rigunel2.
    - exact rigunel1.
  Defined.

  Definition idvec_i_i {n : nat} (i : ⟦ n ⟧%stn) : (stdb_vector i) i = rigunel2.
  Proof.
    unfold stdb_vector. rewrite (stn_neq_or_neq_refl). apply idpath.
  Defined.

  Definition idvec_i_j {n : nat} (i j : ⟦ n ⟧%stn) : i ≠ j ->  (stdb_vector i) j = rigunel1.
  Proof.
    intros i_neq_j. unfold stdb_vector. rewrite (stn_eq_or_neq_right i_neq_j). apply idpath.
  Defined.

  Lemma stdb_vector_sums_to_1 { n : nat } (i : ⟦ n ⟧%stn) :
    Σ (@identity_matrix R n i) = 1%rig.
  Proof.
    rewrite (pulse_function_sums_to_point_rig'' _ (stn_implies_ngt0 i) i).
    (*TODO less versions of this, remove rig in name *) (* and p should be obtained inside pf sums... *)
    - unfold identity_matrix.
      rewrite stn_neq_or_neq_refl, coprod_rect_compute_1.
      apply idpath.
    - unfold identity_matrix.
      intros ? i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      apply idpath.
  Defined.

  Lemma two_pulse_function_sums_to_point_rig { n : nat }
      (f : ⟦ n ⟧%stn -> R) (p : n > 0)
      (i : ⟦ n ⟧%stn) (j : ⟦ n ⟧%stn) (ne_i_j : i ≠ j)
      (X : forall (k: ⟦ n ⟧%stn), (k ≠ i) -> (k ≠ j) -> (f k = 0%rig))
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
        + rewrite rigmultx0.
          rewrite rigrunax1.
          rewrite rigrunax2.
          rewrite i_eq_k.
          reflexivity.
      - rewrite rigmultx0.
        rewrite riglunax1.
        destruct (stn_eq_or_neq j k) as [j_eq_k | j_neq_k].
        + rewrite rigrunax2.
          rewrite j_eq_k.
          apply idpath.
        + rewrite rigmultx0.
          apply X.
          * apply issymm_natneq. assumption.
          * apply issymm_natneq. assumption.
    }
    rewrite H.
    rewrite sum_pointwise_op1.  (*TODO rename to something sensible*)
    unfold scalar_lmult_vec, const_vec.
    rewrite <- (sum_is_ldistr _ (stdb_vector i)).
    rewrite <- (sum_is_ldistr _ (stdb_vector j)).
    rewrite stdb_vector_sums_to_1, rigrunax2.
    rewrite stdb_vector_sums_to_1, rigrunax2.
    unfold pointwise. (* TODO: the following just a result of excessive unfolds and
                               some lemma(s) should be stated using
                               const_vec etc *)
    unfold stdb_vector.
    do 2 rewrite stn_neq_or_neq_refl.
    apply issymm_natneq in  ne_i_j.
    rewrite (stn_eq_or_neq_right ne_i_j).
    apply issymm_natneq in ne_i_j.
    rewrite (stn_eq_or_neq_right ne_i_j).
    do 2 rewrite rigmultx0.
    rewrite rigrunax1.
    rewrite riglunax1.
    do 2 rewrite rigrunax2.
    apply idpath.
  Defined.

  (* TODO remove and change mentions to the non apostrophesized version *)
  Lemma two_pulse_function_sums_to_points_rig' { n : nat }  (f : ⟦ n ⟧%stn -> R) (p : n > 0) :
    ∏ (i j: ⟦ n ⟧%stn ), i ≠ j -> (∏ (k: ⟦ n ⟧%stn), ((k ≠ i) -> (k ≠ j) ->
   (f k = 0%rig))) ->  (Σ f = op1 (f i) (f j)).
  Proof.
    intros.
    apply two_pulse_function_sums_to_point_rig; try assumption.
  Defined.

  Lemma id_math_row_is_pf { n : nat }  : ∏ (r : ⟦ n ⟧%stn), (is_pulse_function r (identity_matrix r) ).
  Proof.
    unfold is_pulse_function.
    intros r i r_neq_j.
    unfold identity_matrix.
    destruct (stn_eq_or_neq r i) as [T | F].
    - rewrite T in r_neq_j.
      apply isirrefl_natneq in r_neq_j. apply fromempty. assumption.
    - rewrite coprod_rect_compute_2.
      reflexivity.
  Defined.

  (* TODO prove over rigs *)
  Lemma id_pointwise_prod { n : nat } (v : Vector F n) (i : ⟦ n ⟧%stn) :
    (@identity_matrix hq n i) ^ v = (@scalar_lmult_vec F (v i) n (identity_matrix i)).
  Proof.
    unfold identity_matrix, scalar_lmult_vec, pointwise.
    apply funextfun. intros k.
    destruct (stn_eq_or_neq i k) as [eq | neq].
    - simpl.
      rewrite (@riglunax2 F).
      rewrite (@rigrunax2 F).
      rewrite eq.
      reflexivity.
    - simpl.
      rewrite (@rigmultx0 F).
      rewrite (@rigmult0x F).
      apply idpath.
  Defined.

  Lemma sum_id_pointwise_prod { n : nat } (v : Vector R n) (i : ⟦ n ⟧%stn) :
    Σ ((identity_matrix i) ^ v) =  (v i).
  Proof.
    unfold identity_matrix, pointwise, Matrix.identity_matrix.
    assert (p: n > 0). {apply (stn_implies_ngt0 i). } (*TODO this should be gt0 *)
    rewrite (pulse_function_sums_to_point_rig'' _  (stn_implies_ngt0 i)  i ).
    - rewrite stn_neq_or_neq_refl.
      simpl.
      apply (riglunax2).
    - intros j i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_j).
      simpl.
      apply (rigmult0x).
  Defined.

  (* TODO should this really be necessary? Used? *)
  Lemma sum_id_pointwise_prod_unf { n : nat } (v : Vector R n) (i : ⟦ n ⟧%stn) :
    Σ (λ j : ⟦ n ⟧%stn, (identity_matrix i j) * (v j))%rig =  (v i).
  Proof.
    apply sum_id_pointwise_prod.
  Defined.

  Definition zero_vector_hq (n : nat) : ⟦ n ⟧%stn -> hq :=
    λ i : ⟦ n ⟧%stn, 0%hq.

  Definition zero_vector_nat (n : nat) : ⟦ n ⟧%stn -> nat :=
    λ i : ⟦ n ⟧%stn, 0%nat.

  Definition zero_vector_stn (n : nat) : ⟦ n ⟧%stn -> ⟦ n ⟧%stn :=
    λ i : ⟦ n ⟧%stn, (0%nat,, (natneq0to0lth _ (stn_implies_nneq0 i))).

  Definition vectorize_1 ( X : UU ) : X -> Vector X 1.
  Proof.
    apply weq_vector_1.
  Defined.

  Lemma weq_rowvec
    : ∏ X : UU, ∏ n : nat,  Vector X n ≃ Matrix X 1 n.
  Proof.
    intros.
    apply weq_vector_1.
  Defined.

  Lemma weq_colwec
    : ∏ X : UU, ∏ n : nat,  weq (Vector X n) (Matrix X n 1).
  Proof.
    intros.
    apply weqffun.
    apply weq_vector_1.
  Defined.

End Vectors.


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
      rewrite stn_neq_or_neq_refl.
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
    rewrite (stn_neq_or_neq_refl); simpl; apply idpath.
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
      rewrite stn_neq_or_neq_refl, coprod_rect_compute_1.
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

  Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn), (stntonat _ i ≠ (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_upper_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i > (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_lower_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ), (stntonat _ i < (stntonat _ j)) -> (mat i j) = 0%rig.


  Definition ij_minor {X : rig} {n : nat} ( i j : ⟦ S n ⟧%stn )  (mat : Matrix X (S n) (S n)) : Matrix X n n.
  Proof.
    intros i' j'.
    exact (mat (dni i i') (dni  j j')).
  Defined.

  Definition determinant { n : nat } (mat : Matrix hq (n) (n)) : hq.
  Proof.
    induction n. {  exact (@rigunel2 hq). }
    destruct (nat_eq_or_neq n 0 ). { exact (@rigunel2 hq). }
    destruct (nat_eq_or_neq n 1 ). { exact (firstValue (firstValue mat)). }
    destruct (nat_eq_or_neq n 2 ).
    { exact (firstValue (firstValue mat) * (lastValue (lastValue (mat)))
           - (lastValue (firstValue mat))  * (firstValue(lastValue (mat))))%hq. }
  Abort.


End Matrices.


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
          -- rewrite stn_neq_or_neq_refl.
             assumption.
          -- rewrite (stn_eq_or_neq_right j_neq).
             apply idpath.
    - intros k.
      unfold transposition_fun.
      destruct (stn_eq_or_neq i k) as [i_eq_k | i_neq_k];
      destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
      + rewrite  i_eq_k in *.
        symmetry; assumption.
      + rewrite stn_neq_or_neq_refl.
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
        * rewrite stn_neq_or_neq_refl.
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


Section Vectorshq.

  Definition abs_hq (e: F) : F.
  Proof.
    destruct (hqgthorleh e 0%hq) as [? | ?].
    - exact e.
    - exact (- e)%hq.
  Defined.

  Lemma abs_ge_0_hq : ∏ (e : F), (hqgeh (abs_hq e) 0)%hq.
  Proof.
    intros e.
    unfold abs_hq.
    destruct (hqgthorleh e 0%hq).
    - apply hqgthtogeh in h. assumption.
    - apply hqleh0andminus in h. assumption.
  Defined.

  (* We can generalize this. And TODO fix or remove - does not look correct. *)
  Definition max_and_index_vec_hq' { n : nat } (f : ⟦ n ⟧%stn -> hq) (max_el: hq) (max_idx: ⟦ n ⟧%stn)
    (pr1iter : nat) (pr2iter : pr1iter < n)  : F × ⟦ n ⟧%stn.
  Proof.
    induction (pr1iter) as [| m IHn].
    - set (idx := (make_stn n 0 pr2iter)).
      destruct (hqgthorleh (f idx) max_el).
      + exact ((f idx) ,, idx).
      + exact (max_el ,, max_idx).
    - set (idx := (make_stn n (S m) pr2iter)).
      set (nextidx := (make_stn n m  ((istransnatlth m (S m) n) (natgthsnn m ) pr2iter))).
      set (f' := IHn ( pr2 nextidx)).
      destruct (hqgthorleh (f idx) (pr1 f')).
      + exact ((f idx) ,, idx).
      + exact (IHn (pr2 nextidx)).
  Defined.

  Definition max_and_index_vec_hq { n : nat } (f : ⟦ n ⟧%stn -> F) (p : n > 0) : F × ⟦ n ⟧%stn.
  Proof.
    set (zeroidx := make_stn n 0 p).
    set (eq := stn_inhabited_implies_succ zeroidx).
    destruct eq as [ m eq' ].
    rewrite eq' in *.
    set (v := lastValue f).
    set (i := @lastelement m).
    exact (max_and_index_vec_hq' f v i (pr1 i) (pr2 i)).
  Defined.

  Definition max_hq (a b : hq) : hq.
    induction (hqgthorleh a b).
    - exact a.
    - exact b.
  Defined.

  (* We can generalize this to just ordered sets *)
  Definition max_hq_index { n : nat } (ei ei' : hq × ⟦ n ⟧%stn) : hq × ⟦ n ⟧%stn.
    induction (hqgthorleh (pr1 ei) (pr1 ei')).
    - exact ei.
    - exact ei'.
  Defined.

  Definition max_and_index_vec_hq_works { n : nat } (f : ⟦ n ⟧%stn -> F) (p : n > 0) :
    ∏ j : ⟦ n ⟧%stn, (hqleh (f j) (pr1 (max_and_index_vec_hq f p))) × (hqleh (f j) (f (pr2 (max_and_index_vec_hq f p)))).
  Proof.
  Abort.

  Definition max_hq_index_bounded { n : nat } (k : ⟦ n ⟧%stn) (f : ⟦ n ⟧%stn -> F) (ei ei' : hq × (⟦ n ⟧%stn)): hq × (⟦ n ⟧%stn).
  Proof.
    set (hq_index := max_hq_index ei ei').
    induction (natlthorgeh (pr2 ei') k).
    - induction (natlthorgeh (pr2 ei) k ).
      + exact (f k,, k).
      + exact ei. (* This case should not occur in our use *)
    - induction (natlthorgeh (pr2 ei) k).
      + exact ei'.
      + exact (max_hq_index ei ei').

  Defined.

  Lemma max_hq_index_bounded_geq_k { n : nat } (k : ⟦ n ⟧%stn) (f : ⟦ n ⟧%stn -> F)
    (ei ei' : hq × (⟦ n ⟧%stn)): k ≤ (pr2 (max_hq_index_bounded k f ei ei')).
  Proof.
    unfold max_hq_index_bounded.
    destruct (natlthorgeh (pr2 ei') k).
    - rewrite coprod_rect_compute_1.
      destruct (natlthorgeh (pr2 ei) k).
      + rewrite coprod_rect_compute_1. apply isreflnatleh.
      + rewrite coprod_rect_compute_2. assumption.
    - rewrite coprod_rect_compute_2.
      unfold max_hq_index.
      destruct (natlthorgeh (pr2 ei) k).
      + rewrite coprod_rect_compute_1.
        assumption.
      + rewrite coprod_rect_compute_2.
        destruct (hqgthorleh (pr1 ei) (pr1 ei')).
        * rewrite coprod_rect_compute_1.
          assumption.
        * rewrite coprod_rect_compute_2.
          assumption.
  Defined.

  (* TODO: indicate absolute value in naming *)
  Definition max_argmax_stnhq_bounded { n : nat } (vec : Vector F n) (pn : n > 0 ) (k : ⟦ n ⟧%stn) :=
  foldleft (0%hq,, (0,, pn)) (max_hq_index_bounded k vec) (λ i : (⟦ n ⟧)%stn, abs_hq (vec i),, i).


  Definition max_el' { n : nat } (v : Vector F n) (max' : F) : F.
  Proof.
    induction n as [ | m IH]. (* TODO naming *)
    {exact max'. }
    exact (max_hq max' (IH (@drop_el_vector F m v lastelement))). (* todo this or DNI ? *)
  Defined.

  Definition max_el { n : nat } (vec: Vector F n) := max_el' vec 0%hq.


End Vectorshq.



Section GaussOps.
  (* Gaussian elimination over the field of rationals *)
  (* TODO better (or any) comments for all these functions including assumptions*)
  (* TODO Carot operator is used similarly throughout the document, move out *)
  Local Notation Σ := (iterop_fun 0%hq op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).
  Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).

  Context { R : hq }.
  (* Gaussian elimination over the field of rationals *)

  Definition gauss_add_row { m n : nat } ( mat : Matrix F m n )
    ( r1 r2 : ⟦ m ⟧%stn )  ( s : F ) : ( Matrix F m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r2).
    - exact ( op1 ( mat r2 j )  ( op2 s ( mat r1 j ))).
    - exact ( mat i j ).
  Defined.

  Definition add_row_op { n : nat } (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧ %stn) (s : F) : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (mat r1) (mat r2)).
    - exact (mat i).
  Defined.

  (* TODO rename *)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : F)  : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (@identity_matrix hq n i) (const_vec s ^ ((@identity_matrix hq) n r1))).
    - exact (@identity_matrix hq n i).
  Defined.

  (*Definition add_row_by_matmul { n m : nat } ( r1 r2 : ⟦ m ⟧%stn ) (mat : Matrix F m n) (s : F) : Matrix F m n :=
    @matrix_mult hq m m (make_add_row_matrix r1 r2 s ) n mat. *)

  Definition gauss_scalar_mult_row { m n : nat} (mat : Matrix F m n)
    (s : F) (r : ⟦ m ⟧%stn): Matrix F m n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r).
    - exact (s * (mat i j))%rig.
    - exact (mat i j).
  Defined.

  (* TODO  generalize to m x n whereever possible*)
  Definition make_scalar_mult_row_matrix { n : nat}
    (s : F) (r : ⟦ n ⟧%stn): Matrix F n n.
  Proof.
    intros i j.
    induction (stn_eq_or_neq i j).
      - induction (stn_eq_or_neq i r).
        + exact s.
        + exact 1%hq.
      - exact 0%hq.
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

  Lemma gauss_switch_row_inv0 {m n : nat} (mat : Matrix hq n n)
        (r1 : ⟦ n ⟧%stn) (r2 : ⟦ n ⟧%stn) : ∏ (i : ⟦ n ⟧%stn), i ≠ r1 -> i ≠ r2
      -> (gauss_switch_row mat r1 r2 ) i = mat i.
  Proof.
    intros i i_ne_r1 i_ne_r2.
    unfold gauss_switch_row.
    apply funextfun. intros i'.
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1]
    ; destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
    - simpl. rewrite i_eq_r2; apply idpath.
    - simpl. rewrite i_eq_r1 in i_ne_r1. apply isirrefl_natneq in i_ne_r1. contradiction.
    - simpl. rewrite i_eq_r2 in i_ne_r2. apply isirrefl_natneq in i_ne_r2. contradiction.
    - simpl. apply idpath.
  Defined.

  Definition make_gauss_switch_row_matrix (n : nat)  (r1 r2 : ⟦ n ⟧ %stn) : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r1).
    - exact (@identity_matrix hq n r2).
    - induction (stn_eq_or_neq i r2).
      + exact (@identity_matrix hq n r1).
      + exact (@identity_matrix hq n i).
  Defined.


  Definition test_row_switch {m n : nat} (mat : Matrix F m n)
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

  (* The following three lemmata test the equivalence of multiplication by elementary matrices
     to swaps of indices. *)
  Lemma scalar_mult_mat_elementary {n : nat} (mat : Matrix F n n) (s : hq) (r : ⟦ n ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros ?.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_scalar_mult_row_matrix. unfold gauss_scalar_mult_row.
    assert (p : n > 0). { apply (stn_implies_ngt0 r). }
    destruct (stn_eq_or_neq i r) as [? | ?].
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F n _ p i ).
      + rewrite stn_neq_or_neq_refl.
        simpl.
        apply idpath.
      + intros k i_neq_k.
        rewrite (stn_eq_or_neq_right i_neq_k).
        simpl.
        apply (@rigmult0x F).
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F n _ p i ).
      + rewrite stn_neq_or_neq_refl.
        simpl.
        rewrite (@riglunax2 F).
        reflexivity.
      + intros k i_neq_k.
        rewrite (stn_eq_or_neq_right i_neq_k).
        simpl.
        apply (@rigmult0x F).
  Defined.

  (* TODO should certainly be over R *)
  Lemma switch_row_mat_elementary { n : nat } (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧%stn) :
    ((make_gauss_switch_row_matrix n r1 r2) ** mat)  = gauss_switch_row mat r1 r2.
  Proof.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_gauss_switch_row_matrix, gauss_switch_row.
    apply funextfun. intros i.
    apply funextfun. intros ?.
    assert (p: n > 0).  { apply ( stn_implies_ngt0 r1).  }
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F n (λ i : (⟦ n ⟧%stn), @identity_matrix hq n r2 i * _)%ring p r2).
      + unfold identity_matrix.
        rewrite stn_neq_or_neq_refl.
        simpl.
        apply (@riglunax2 F).
      + intros k r2_neq_k.
        rewrite (@id_mat_ij hq n r2 k r2_neq_k).
        apply (@rigmult0x F).
    - simpl.
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
      + simpl.
        destruct (stn_eq_or_neq i r1) as [? | ?].
        * rewrite (@sum_id_pointwise_prod_unf hq).
          apply idpath.
        * rewrite (@sum_id_pointwise_prod_unf hq).
          apply idpath.
      + simpl.
        rewrite (@sum_id_pointwise_prod_unf hq).
        apply idpath.
  Defined.


  (* TODO fix mixed up signatures on add_row  / make_add_row_matrix *)
  Lemma add_row_mat_elementary { n : nat } (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧%stn) (p : r1 ≠ r2) (s : F) :
    ((make_add_row_matrix  r1 r2 s) ** mat)  = (gauss_add_row mat r1 r2 s).
  Proof.
    intros.
    unfold make_add_row_matrix, gauss_add_row.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold pointwise.
    apply funextfun. intros k.
    apply funextfun. intros l.
    assert (p': n > 0). { apply (stn_implies_ngt0 r1). }
    destruct (stn_eq_or_neq k r1) as [k_eq_r1 | k_neq_r1].
    - simpl.
      destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
      + simpl.
        rewrite k_eq_r1 in k_eq_r2.
        rewrite k_eq_r2 in p.
        apply isirrefl_natneq in p.
        contradiction.
      + simpl.
        rewrite (@pulse_function_sums_to_point_rig'' F n (λ i : (⟦ n ⟧%stn), @identity_matrix hq n k i * _)%ring p' k).
        * rewrite k_eq_r1 in *.
          rewrite id_mat_ii.
          rewrite (@riglunax2 F).
          apply idpath.
        * intros j k_neq_j.
          rewrite (id_mat_ij k j k_neq_j).
          apply (@rigmult0x F).
    - destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
      + simpl.
        rewrite (@two_pulse_function_sums_to_point_rig F n (λ i : ( ⟦ n ⟧%stn), ((@identity_matrix hq n  _ _ + _ * _) * _ ))%rig p' k r1).
        * unfold const_vec, identity_matrix.
          rewrite stn_neq_or_neq_refl. simpl.
          apply issymm_natneq in k_neq_r1.
          rewrite (stn_eq_or_neq_right k_neq_r1). simpl.
          rewrite stn_neq_or_neq_refl. simpl.
          apply issymm_natneq in k_neq_r1.
          rewrite (stn_eq_or_neq_right k_neq_r1). simpl.
          rewrite (@rigmultx0 F).
          rewrite (@rigrunax1 F).
          rewrite (@riglunax1 F (s * _))%hq.
          rewrite (@rigrunax2 F).
          rewrite (@riglunax2 F).
          rewrite k_eq_r2.
          apply idpath.
        * exact k_neq_r1.
        * intros q q_neq_k q_neq_k'.
          unfold identity_matrix.
          apply issymm_natneq in q_neq_k.
          rewrite (stn_eq_or_neq_right q_neq_k).
          simpl.
          rewrite (@riglunax1 F).
          unfold const_vec.
          apply issymm_natneq in q_neq_k'.
          rewrite (stn_eq_or_neq_right q_neq_k').
          simpl.
          rewrite (@rigmultx0 F).
          rewrite (@rigmult0x F).
          apply idpath.
      + simpl.
        rewrite (@sum_id_pointwise_prod_unf hq).
        apply idpath.
  Defined.



  (* TODO : F should also be a general field, not short-hand for rationals specifically.
            This does not mandate any real change in any proofs ?*)
  Lemma scalar_mult_matrix_is_inv { n : nat } ( i : ⟦ n ⟧%stn ) ( s : F ) ( ne : hqneq s 0%hq ) :
    @matrix_inverse F n (make_scalar_mult_row_matrix s i ).
  Proof.
    (*unfold matrix_is_invertible.
    unfold make_scalar_mult_row_matrix.*)
    use tpair.
    { exact (make_scalar_mult_row_matrix (hqmultinv s ) i). }
    use tpair.
    - apply funextfun. intros k.
      apply funextfun. intros l.
      destruct (stn_eq_or_neq k l) as [T' | F'].
      + (*rewrite T.*)
        unfold gauss_scalar_mult_row.
        unfold identity_matrix.
        unfold make_scalar_mult_row_matrix.
        rewrite matrix_mult_eq; unfold matrix_mult_unf.
        destruct (stn_eq_or_neq l i).
        * destruct (stn_eq_or_neq l l).
          2 : { apply isirrefl_natneq in h.
                apply fromempty. assumption. }
          -- rewrite T'. rewrite p.
             destruct (stn_eq_or_neq i i).
             ++ do 2 rewrite coprod_rect_compute_1.
                rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i ) l).
                rewrite p.
                destruct (stn_eq_or_neq i i).
                ** do 3 rewrite coprod_rect_compute_1.
                   apply (hqisrinvmultinv). assumption.
                ** do 2 rewrite coprod_rect_compute_2.
                   apply isirrefl_natneq in h.
                   apply fromempty. assumption.
                ** unfold is_pulse_function.
                   intros q l_neq_q.
                   rewrite <- p.
                   destruct (stn_eq_or_neq l q) as [l_eq_q' | l_neq_q'].
                   --- rewrite l_eq_q' in l_neq_q.
                       apply isirrefl_natneq in l_neq_q.
                       apply fromempty. assumption.
                   --- rewrite coprod_rect_compute_2.
                       apply rigmult0x.
             ++ remember h as h'. clear Heqh'.
                apply isirrefl_natneq in h.
                apply fromempty. assumption.
        * rewrite <- T' in h.
          destruct (stn_eq_or_neq k i).
          -- rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq k l).
             ++ rewrite coprod_rect_compute_1.
                rewrite(@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) k).
                ** destruct (stn_eq_or_neq k l).
                   --- rewrite coprod_rect_compute_1.
                       destruct (stn_eq_or_neq k k).
                       +++ rewrite coprod_rect_compute_1.
                           destruct (stn_eq_or_neq k i).
                           *** rewrite coprod_rect_compute_1.
                               apply hqisrinvmultinv.
                               assumption.
                           *** rewrite coprod_rect_compute_2.
                               rewrite p in h0.
                               apply isirrefl_natneq in h0.
                               apply fromempty. assumption.
                       +++ remember h0 as h0'. clear Heqh0'.
                           apply isirrefl_natneq in h0.
                           apply fromempty. assumption.
                   --- rewrite  coprod_rect_compute_2.
                       rewrite <- p0 in h0.
                       apply isirrefl_natneq in h0.
                       apply fromempty. assumption.
                ** rewrite p in h.
                   apply isirrefl_natneq in h.
                   apply fromempty. assumption.
             ++ remember h0 as h0'. clear Heqh0'.
                rewrite T' in h0.
                apply isirrefl_natneq in h0.
                apply fromempty. assumption.
          --
            rewrite coprod_rect_compute_2.
            destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l] .
            2 : { remember k_neq_l as k_neq_l'.
                  clear Heqk_neq_l'.
                  rewrite T' in k_neq_l.
                  apply isirrefl_natneq in k_neq_l.
                  apply fromempty. assumption. }
            rewrite coprod_rect_compute_1.
            rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) k).
            ++ destruct (stn_eq_or_neq k k) as [k_eq_k | k_neq_k].
               2 : { rewrite coprod_rect_compute_2.
                     apply isirrefl_natneq in k_neq_k.
                     apply fromempty. assumption.
               }
               destruct (stn_eq_or_neq k l) as [ ? | cntr].
               2 : { rewrite coprod_rect_compute_2.
                     rewrite k_eq_l in cntr.
                     apply isirrefl_natneq in cntr.
                     apply fromempty. assumption.
               }
               do 2rewrite coprod_rect_compute_1.
               destruct (stn_eq_or_neq k i) as [cntr | k_neq_i].
               { rewrite cntr in h. apply isirrefl_natneq in h.
                 apply fromempty. assumption.
               }
               rewrite coprod_rect_compute_2.
               apply riglunax2.
            ++ unfold is_pulse_function.
               intros q l_neq_q.
               rewrite <- k_eq_l.
               destruct (stn_eq_or_neq l q) as [l_eq_q' | l_neq_q'].
               --- rewrite k_eq_l in l_neq_q.
                   rewrite l_eq_q' in l_neq_q.
                   apply isirrefl_natneq in l_neq_q.
                   apply fromempty. assumption.
               --- destruct (stn_eq_or_neq q k) as [ ? | ? ].
                 +++
                   rewrite coprod_rect_compute_1.
                   rewrite p in l_neq_q.
                   apply isirrefl_natneq in l_neq_q.
                   apply fromempty. assumption.
                 +++ rewrite coprod_rect_compute_2.
                     destruct (stn_eq_or_neq k q).
                     *** rewrite coprod_rect_compute_1.
                         apply rigmultx0.
                     *** rewrite coprod_rect_compute_2.
                         apply rigmultx0.
      + unfold make_scalar_mult_row_matrix.
        unfold Matrix.identity_matrix.
        destruct (stn_eq_or_neq k l) as [cntr | dup ].
        { rewrite cntr in F'. (* really should have a one_liner *)
          apply isirrefl_natneq in F'.
          apply fromempty. assumption.
        }
        rewrite coprod_rect_compute_2.
        unfold Matrix.matrix_mult.
        unfold col. unfold row. unfold "^".
        unfold transpose. unfold flip.
        destruct (stn_eq_or_neq k i) as [k_eq_i | k_neq_i] .
        * rewrite coprod_rect_compute_1.
          rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) i).
          -- destruct (stn_eq_or_neq k i) as [ ? | cntr ].
             rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq i i) as [? | cntr ].
             ++ destruct (stn_eq_or_neq i l) as [i_eq_l | i_neq_l].
                **
                  do 2 rewrite coprod_rect_compute_1.
                  rewrite <- k_eq_i in i_eq_l.
                  rewrite i_eq_l in F'.
                  apply isirrefl_natneq in F'.
                  apply fromempty. assumption.
                ** rewrite coprod_rect_compute_2.
                   apply rigmultx0.
             ++ rewrite coprod_rect_compute_2.
                apply isirrefl_natneq in cntr.
                apply fromempty. assumption.
             ++ rewrite coprod_rect_compute_2.
                rewrite k_eq_i in cntr.
                apply isirrefl_natneq in cntr.
                apply fromempty. assumption.
          -- unfold is_pulse_function.
             intros q i_neq_q.
             rewrite k_eq_i.
             destruct (stn_eq_or_neq q i ) as [q_eq_i | q_neq_i] .
             ++ rewrite q_eq_i in i_neq_q.
                apply isirrefl_natneq in i_neq_q.
                apply fromempty. assumption.
             ++ destruct (stn_eq_or_neq i q) as [i_eq_q | i_neq_q'].
                { rewrite i_eq_q in i_neq_q.
                  apply isirrefl_natneq in i_neq_q.
                  apply fromempty. assumption.
                }
                do 2 rewrite coprod_rect_compute_2.
                destruct (stn_eq_or_neq q l) as [q_eq_l | q_neq_l].
                ** apply rigmult0x.
                ** apply rigmult0x.
      * rewrite coprod_rect_compute_2.
        rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) k).
        -- destruct (stn_eq_or_neq k k) as [? | cntr].
           2 : { rewrite coprod_rect_compute_2.
                 apply isirrefl_natneq in cntr.
                 apply fromempty. assumption.
           }
           destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l] .
           { rewrite k_eq_l in F'.  apply isirrefl_natneq in F'.
             apply fromempty. assumption.
           }
           rewrite coprod_rect_compute_2. rewrite coprod_rect_compute_1.
           apply rigmultx0.

        -- unfold is_pulse_function.
           intros j k_neq_j.
           destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j'].
           { rewrite k_eq_j in k_neq_j. apply isirrefl_natneq in k_neq_j.
             apply fromempty. assumption.
           }
           destruct (stn_eq_or_neq j l) as [j_eq_l | j_neq_l].
           ++ rewrite coprod_rect_compute_1.
             rewrite coprod_rect_compute_2.
             apply rigmult0x.
           ++ apply rigmult0x.
    - simpl.
      (* Here in the second half, we try to be slightly more efficient *)
      unfold make_scalar_mult_row_matrix.
      unfold Matrix.identity_matrix.
      unfold matrix_mult.
      unfold Matrix.matrix_mult.
      unfold row. unfold col. unfold transpose. unfold flip.
      unfold "^".
      apply funextfun. intros k.
      apply funextfun. intros l.
      destruct (stn_eq_or_neq k i) as [ k_eq_i | k_neq_i ].
      +
        destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l ].
        * rewrite coprod_rect_compute_1.
          rewrite <- k_eq_l.
          rewrite <- k_eq_i.
          rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) k).
          -- rewrite stn_neq_or_neq_refl.
            do 3 rewrite coprod_rect_compute_1.
            apply (hqislinvmultinv).
            assumption.
          -- unfold is_pulse_function.
             intros q k_neq_q.
             rewrite (stn_eq_or_neq_right k_neq_q).
             rewrite coprod_rect_compute_2.
             apply rigmult0x.
        * rewrite coprod_rect_compute_2.
          rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) k). (* Didn't we just do this ? *)
          -- rewrite (stn_eq_or_neq_right k_neq_l).
             rewrite coprod_rect_compute_2.
             rewrite (stn_neq_or_neq_refl).
             rewrite coprod_rect_compute_1.
             rewrite rigmultx0. apply idpath.
          -- unfold is_pulse_function.
             intros q k_neq_q.
             rewrite coprod_rect_compute_1.
             destruct (stn_eq_or_neq k q) as [k_eq_q | k_neq_q'].
             ++ rewrite k_eq_q in k_neq_q.
                apply isirrefl_natneq in k_neq_q.
                contradiction.
             ++ rewrite coprod_rect_compute_2.
                apply rigmult0x.
      + rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) k).
        * rewrite (stn_neq_or_neq_refl).
          rewrite (stn_eq_or_neq_right k_neq_i).
          rewrite coprod_rect_compute_1.
          do 2 rewrite coprod_rect_compute_2.
          destruct (stn_eq_or_neq k l).
          -- do 2 rewrite coprod_rect_compute_1.
             rewrite rigrunax2. apply idpath.
          -- do 2 rewrite coprod_rect_compute_2.
             rewrite rigmultx0. apply idpath.
        * unfold is_pulse_function.
          intros q k_neq_q.
          rewrite (stn_eq_or_neq_right k_neq_q). rewrite coprod_rect_compute_2.
          destruct (stn_eq_or_neq q l) as [q_eq_l | q_neq_l].
          -- apply rigmult0x.
          -- apply rigmult0x.
  Defined.


  Lemma add_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (r1_neq_r2 : r1 ≠ r2) ( s : F )
    (*(p : (s != 0)%hq)*) (p' : n > 0):
    @matrix_inverse F n (make_add_row_matrix r1 r2 s ).
  Proof.
    unfold matrix_inverse.
    unfold make_add_row_matrix.
    use tpair.
    {
      induction (stn_eq_or_neq r1 r2) as [? | ?].
      - exact (make_add_row_matrix r1 r2 (hqmultinv s)).
      - exact (make_add_row_matrix r1 r2 (- s)%hq).
    }
    unfold make_add_row_matrix, identity_matrix, pointwise.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    use tpair. (*TODO was there a quicker alternative ? *)
    - apply funextfun. intros k.
      apply funextfun. intros l.
      destruct (stn_eq_or_neq r1 r2) as [r1_eq_r2 | r1_neq_r2'].
      + rewrite r1_eq_r2 in r1_neq_r2.
        apply isirrefl_natneq in r1_neq_r2.
        contradiction.
      + simpl.
        destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2]
        ; destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l]; simpl.
        * rewrite (@two_pulse_function_sums_to_point_rig F n _ p' k r1).
          -- repeat rewrite stn_neq_or_neq_refl.
             repeat rewrite (stn_eq_or_neq_right r1_neq_r2).
             rewrite k_eq_l in *.
             rewrite k_eq_r2 in *.
             repeat rewrite (stn_eq_or_neq_right r1_neq_r2').
             simpl.
             rewrite (@rigmultx0 F).
             rewrite (@rigrunax1 F).
             rewrite (@riglunax2 F).
             rewrite stn_neq_or_neq_refl; simpl.
             rewrite stn_neq_or_neq_refl; simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2').
             rewrite (@rigmultx0 F).
             simpl.
             rewrite (@rigmultx0 F).
             do 2 rewrite (@rigrunax1 F).
             apply idpath.
          -- rewrite k_eq_r2.
             apply issymm_natneq in r1_neq_r2'.
             assumption.
          -- intros q q_neq_k q_neq_r1.
             rewrite k_eq_r2, k_eq_l in *.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             apply issymm_natneq in q_neq_k. (* TODO this is repeated quite often... *)
             rewrite (stn_eq_or_neq_right q_neq_k).
             apply issymm_natneq in q_neq_r1.
             rewrite (stn_eq_or_neq_right q_neq_r1).
             rewrite (@rigmultx0 F).
             apply idpath.
        *  rewrite (@two_pulse_function_sums_to_point_rig F n _ p' k r1).
           -- rewrite (stn_eq_or_neq_right r1_neq_r2); simpl.
              rewrite stn_neq_or_neq_refl. simpl.
              rewrite k_eq_r2 in *.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              rewrite stn_neq_or_neq_refl.
              simpl.
              rewrite (stn_eq_or_neq_right k_neq_l).
              repeat rewrite (@rigmultx0 F).
              rewrite (@rigrunax1 F).
              rewrite (@riglunax2 F).
              rewrite (@riglunax1 F).
              unfold const_vec.
              rewrite stn_neq_or_neq_refl.
              apply issymm_natneq in r1_neq_r2'.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              destruct (stn_eq_or_neq r1 l) as [r1_eq_l | r1_neq_l].
              ++ simpl.
                 do 3 rewrite (@rigrunax2 F).
                 rewrite (hqpluscomm _ s) . (* Only place we mention hq ? TODO don't? *)
                 rewrite hqplusr0.
                 rewrite hqlminus.
                 apply idpath.
              ++ repeat rewrite (@rigmultx0 F).
                 rewrite (@rigrunax1 F).
                 apply idpath.
           -- rewrite k_eq_r2.
              apply issymm_natneq.
              assumption.
           -- intros q q_neq_k q_neq_r1.
              rewrite k_eq_r2 in *.
              apply issymm_natneq in q_neq_k.
              rewrite (stn_eq_or_neq_right q_neq_k).
              unfold const_vec.
              apply issymm_natneq in q_neq_r1.
              rewrite (stn_eq_or_neq_right q_neq_r1).
              rewrite (@riglunax1 F).
              rewrite (@rigmultx0 F).
              rewrite (@rigmult0x F).
              apply idpath.
        * rewrite k_eq_l in *.
          set (cl := setquot _ ).
          rewrite (@pulse_function_sums_to_point_rig''  hq n _  p' l).
          -- rewrite (stn_neq_or_neq_refl); simpl.
             rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
             rewrite (@riglunax2 hq).
             rewrite (stn_neq_or_neq_refl); simpl.
             apply idpath.
          -- intros q l_neq_q; simpl.
             rewrite (stn_eq_or_neq_right l_neq_q); simpl.
             apply (@rigmult0x hq).
        *  rewrite (@pulse_function_sums_to_point_rig''  hq n _  p' l).
           { rewrite (stn_eq_or_neq_right k_neq_l); simpl. apply (@rigmult0x hq). }
           intros q q_neq_j.
           destruct (stn_eq_or_neq k q) as [k_eq_q | k_neq_q]; simpl.
           -- rewrite k_eq_q in *.
              rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
              rewrite (stn_eq_or_neq_right k_neq_l); simpl.
              apply (@rigmultx0 hq).
           -- apply (@rigmult0x hq).
   (* Part two, which is identical except for using riglunax1 instead of rigrunax1.
      Can we reduce verbosity? *)
    - apply funextfun. intros k.
      apply funextfun. intros l.
      rewrite matrix_mult_eq; unfold matrix_mult_unf.
      destruct (stn_eq_or_neq r1 r2) as [r1_eq_r2 | r1_neq_r2'].
      + rewrite r1_eq_r2 in r1_neq_r2.
        apply isirrefl_natneq in r1_neq_r2.
        contradiction.
      + simpl.
        destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2]
        ; destruct (stn_eq_or_neq k l) as [k_eq_l | k_neq_l]; simpl.
        * rewrite (@two_pulse_function_sums_to_point_rig F n _ p' k r1).
          -- repeat rewrite stn_neq_or_neq_refl.
             repeat rewrite (stn_eq_or_neq_right r1_neq_r2).
             rewrite k_eq_l in *.
             rewrite k_eq_r2 in *.
             repeat rewrite (stn_eq_or_neq_right r1_neq_r2').
             simpl.
             rewrite (@rigmultx0 F).
             rewrite (@rigrunax1 F).
             rewrite (@riglunax2 F).
             rewrite stn_neq_or_neq_refl; simpl.
             rewrite stn_neq_or_neq_refl; simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2').
             rewrite (@rigmultx0 F).
             simpl.
             rewrite (@rigmultx0 F).
             do 2 rewrite (@rigrunax1 F).
             apply idpath.
          -- rewrite k_eq_r2.
             apply issymm_natneq in r1_neq_r2'.
             assumption.
          -- intros q q_neq_k q_neq_r1.
             rewrite k_eq_r2, k_eq_l in *.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             apply issymm_natneq in q_neq_k. (* TODO this is repeated quite often... *)
             rewrite (stn_eq_or_neq_right q_neq_k).
             apply issymm_natneq in q_neq_r1.
             rewrite (stn_eq_or_neq_right q_neq_r1).
             rewrite (@rigmultx0 F).
             apply idpath.
        *  rewrite (@two_pulse_function_sums_to_point_rig F n _ p' k r1).
           -- rewrite (stn_eq_or_neq_right r1_neq_r2); simpl.
              rewrite stn_neq_or_neq_refl. simpl.
              rewrite k_eq_r2 in *.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              rewrite stn_neq_or_neq_refl.
              simpl.
              rewrite (stn_eq_or_neq_right k_neq_l).
              repeat rewrite (@rigmultx0 F).
              rewrite (@rigrunax1 F).
              rewrite (@riglunax2 F).
              rewrite (@riglunax1 F).
              unfold const_vec.
              rewrite stn_neq_or_neq_refl.
              apply issymm_natneq in r1_neq_r2'.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              destruct (stn_eq_or_neq r1 l) as [r1_eq_l | r1_neq_l].
              ++ simpl.
                 do 3 rewrite (@rigrunax2 F).
                 rewrite (@rigcomm1 F).
                 rewrite (@riglunax1 F).
                 rewrite hqlminus. (* use ring props instead ?*)
                 apply idpath.
              ++ repeat rewrite (@rigmultx0 F).
                 rewrite (@rigrunax1 F).
                 apply idpath.
           -- rewrite k_eq_r2.
              apply issymm_natneq.
              assumption.
           -- intros q q_neq_k q_neq_r1.
              rewrite k_eq_r2 in *.
              apply issymm_natneq in q_neq_k.
              rewrite (stn_eq_or_neq_right q_neq_k).
              unfold const_vec.
              apply issymm_natneq in q_neq_r1.
              rewrite (stn_eq_or_neq_right q_neq_r1).
              rewrite (@riglunax1 F).
              rewrite (@rigmultx0 F).
              rewrite (@rigmult0x F).
              apply idpath.
        * rewrite k_eq_l in *.
          set (cl := setquot _ ).
          rewrite (@pulse_function_sums_to_point_rig''  hq n _  p' l).
          -- rewrite (stn_neq_or_neq_refl); simpl.
             rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
             rewrite (@riglunax2 hq).
             rewrite (stn_neq_or_neq_refl); simpl.
             apply idpath.
          -- intros q l_neq_q; simpl.
             rewrite (stn_eq_or_neq_right l_neq_q); simpl.
             apply (@rigmult0x hq).
        *  rewrite (@pulse_function_sums_to_point_rig''  hq n _  p' l).
           { rewrite (stn_eq_or_neq_right k_neq_l); simpl. apply (@rigmult0x hq). }
           intros q q_neq_j.
           destruct (stn_eq_or_neq k q) as [k_eq_q | k_neq_q]; simpl.
           -- rewrite k_eq_q in *.
              rewrite (stn_eq_or_neq_right k_neq_r2); simpl.
              rewrite (stn_eq_or_neq_right k_neq_l); simpl.
              apply (@rigmultx0 hq).
           -- apply (@rigmult0x hq).
  Defined. (* Second part, this is all very verbose. Could we do it concisely ? *)

  Lemma switch_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) ( s : F ) (*( ne : hqneq s 0%hq )*) :
    @matrix_inverse F n (make_gauss_switch_row_matrix n r1 r2).
  Proof.
    (* intros. *)
    use tpair.
    { exact (make_gauss_switch_row_matrix n r1 r2). }
    set (lft := @stn_eq_or_neq_left n).
    set (rht := @stn_eq_or_neq_right n).
    set (irfl := @stn_neq_or_neq_refl n).
    set (cpl := coprod_rect_compute_1).
    set (cpr := coprod_rect_compute_2).
    assert (proof : ((make_gauss_switch_row_matrix n r1 r2) **
                    (make_gauss_switch_row_matrix n r1 r2)) = identity_matrix).
    - rewrite matrix_mult_eq; unfold matrix_mult_unf.
      unfold make_gauss_switch_row_matrix, identity_matrix.
      apply funextfun. intros i.
      apply funextfun. intros j.
      destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1];
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2];
      destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
      (* TODO some cases should be impossible, so shouldn’t need algebra? *)
      + rewrite i_eq_r1, i_eq_r2, i_eq_j.
        do 2 rewrite cpl.
        -- rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) i).
           ++ rewrite (lft _ _ i_eq_r1), cpl.
              rewrite i_eq_j in i_eq_r2.
              symmetry in i_eq_r2. (*TODO *)
              rewrite (lft _ _ i_eq_r2), cpl.
              rewrite <- i_eq_j in i_eq_r2.
              rewrite (lft _ _  i_eq_r2), cpl.
              rewrite (@rigrunax2 hq).
              apply idpath.
           ++ unfold is_pulse_function.
              intros q i_neq_q.
              rewrite i_eq_r1 in i_neq_q.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              rewrite <- i_eq_r1 in i_neq_q.
              rewrite i_eq_r2 in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              rewrite <- i_eq_j.
              rewrite i_eq_r2.
              rewrite (rht _ _ i_neq_q), cpr.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply rigmult0x.
      + rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) i).
        ++
          rewrite cpr.
          rewrite (lft _ _ i_eq_r1), cpl.
          rewrite cpl.
          rewrite <- i_eq_r2, (rht _ _ i_neq_j).
          rewrite coprod_rect_compute_2, stn_neq_or_neq_refl, cpl.
          apply (@rigmultx0 hq).
        ++ unfold is_pulse_function.
           intros q i_neq_q.
           rewrite <- i_eq_r1.
           apply issymm_natneq in i_neq_q.
           rewrite (rht _ _ i_neq_q), cpr.
           rewrite <- i_eq_r2.
           rewrite (rht _ _ i_neq_q), cpr.
           destruct (stn_eq_or_neq q j) as [q_eq_j | q_neq_j].
           ** do 2 rewrite cpl.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply rigmult0x.
           ** rewrite cpr, cpl.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply rigmult0x.
      + do 2 rewrite cpl.
        rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) r2).
        ** rewrite (stn_neq_or_neq_refl), cpl.
           rewrite <- i_eq_j.
           apply issymm_natneq in i_neq_r2.
           rewrite <- i_eq_r1.
           rewrite (rht _ _ i_neq_r2), cpr, cpl.
           rewrite stn_neq_or_neq_refl, cpl.
           apply (@riglunax2 hq).
        ** unfold is_pulse_function.
           intros q r2_neq_q.
           destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
           --- rewrite cpl.
               rewrite (rht _ _ r2_neq_q), cpr.
               apply rigmult0x.
           --- rewrite cpr.
               apply issymm_natneq in r2_neq_q.
               rewrite (rht _ _ r2_neq_q), cpr.
               rewrite <- i_eq_j, i_eq_r1.
               rewrite (rht _ _ q_neq_r1), cpr.
               apply rigmultx0.
      + do 2 rewrite cpr.
        rewrite cpl.
        apply (@zero_function_sums_to_zero hq).
        apply funextfun. intros q.
        destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
        --- rewrite cpl.
            apply issymm_natneq in i_neq_r2.
            destruct (stn_eq_or_neq r2 j) as [r2_eq_j | r2_neq_j].
            +++ rewrite cpl.
                rewrite r2_eq_j, q_eq_r1, <- i_eq_r1.
                apply issymm_natneq in i_neq_j.
                rewrite (rht _ _ i_neq_j), cpr.
                apply rigmult0x.
            +++ rewrite cpr.
                rewrite q_eq_r1, <- i_eq_r1.
                rewrite (rht _ _ i_neq_r2), cpr.
                apply rigmult0x.
        --- rewrite cpr.
            destruct (stn_eq_or_neq q r2) as [q_eq_r2 | q_neq_r2].
            +++ rewrite cpl.
                rewrite <- i_eq_r1.
                rewrite (rht _ _ i_neq_j), cpr.
                rewrite q_eq_r2.
                rewrite  stn_neq_or_neq_refl, cpl.
                apply rigmultx0.
            +++ rewrite cpr.
                apply issymm_natneq in q_neq_r2.
                rewrite (rht _ _ q_neq_r2), cpr.
                apply rigmult0x.
      + rewrite  i_eq_r2, i_eq_j.
        do 2 rewrite cpl.
        rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) r1).
        ++ rewrite <- i_eq_j, <- i_eq_r2.
           do 2 rewrite (stn_neq_or_neq_refl), cpl.
           rewrite cpr.
           rewrite (stn_neq_or_neq_refl), cpl.
           apply (@riglunax2 hq).
        ++ unfold is_pulse_function.
           intros q i_neq_q.
           apply issymm_natneq in i_neq_q.
           rewrite (rht _ _ i_neq_q), cpr, cpr.
           apply issymm_natneq in i_neq_q.
           rewrite (rht _ _ i_neq_q), cpr.
           apply rigmult0x.
      + rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) i).
        ++ do 2 rewrite cpr.
           rewrite (rht _ _ i_neq_r1), cpr.
           rewrite cpl.
           apply issymm_natneq in i_neq_r1.
           rewrite (rht _ _ i_neq_r1), cpr.
           apply (@rigmult0x hq).
        ++ unfold is_pulse_function.
           intros q i_neq_q.
           rewrite cpr, cpl.
           apply issymm_natneq in i_neq_r1.
           destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
           ** rewrite cpl.
              rewrite <- i_eq_r2.
              rewrite (rht _ _ i_neq_j), cpr.
              apply rigmultx0.
           ** rewrite cpr.
              rewrite <- i_eq_r2.
              apply issymm_natneq in i_neq_q.
              rewrite (rht _ _ i_neq_q), cpr.
              apply issymm_natneq in q_neq_r1.
              rewrite (rht _ _ q_neq_r1), cpr.
              apply rigmult0x.
      + (* Shouldn't this be zero function ? *)
        rewrite cpl.
        rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 i) i).
        ** rewrite (rht _ _ i_neq_r1).
           do 3 rewrite cpr.
           rewrite (stn_neq_or_neq_refl), cpl.
           rewrite (rht _ _ i_neq_r2), cpr.
           rewrite (lft _ _ i_eq_j), cpl.
           apply (@riglunax2 hq).
        ** unfold is_pulse_function.
           intros q r2_neq_q.
           destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
           --- rewrite cpl.
               rewrite <- i_eq_j, cpr, cpr.
               apply issymm_natneq in i_neq_r2.
               rewrite (rht _ _ i_neq_r2), cpr.
               apply rigmultx0.
           --- rewrite cpr.
               apply issymm_natneq in r2_neq_q.
               do 2 rewrite cpr.
               apply issymm_natneq in r2_neq_q.
               rewrite (rht _ _ r2_neq_q), cpr.
               apply rigmult0x.
      + do 2 rewrite cpr.
        rewrite cpr.
        apply (@zero_function_sums_to_zero hq).
        apply funextfun. intros q.
        destruct (stn_eq_or_neq q r1) as [q_eq_r1 | q_neq_r1].
        --- rewrite cpl.
            apply issymm_natneq in i_neq_r2.
            destruct (stn_eq_or_neq r2 j) as [r2_eq_j | r2_neq_j].
            +++ rewrite cpl.
                rewrite q_eq_r1.
                rewrite (rht _ _ i_neq_r1), cpr.
                apply rigmult0x.
            +++ rewrite cpr.
                apply rigmultx0.
        --- rewrite cpr.
            destruct (stn_eq_or_neq q r2) as [q_eq_r2 | q_neq_r2].
            +++ rewrite cpl.
                rewrite q_eq_r2.
                rewrite (rht _ _ i_neq_r2), cpr.
                apply rigmult0x.
            +++ rewrite cpr.
                apply issymm_natneq in q_neq_r2.
                destruct (stn_eq_or_neq q j) as [q_eq_j | q_neq_j].
                ---- rewrite cpl.
                     rewrite q_eq_j.
                     rewrite (rht _ _ i_neq_j), cpr.
                     apply rigmult0x.
                ---- rewrite cpr.
                     apply rigmultx0.
    - use tpair.
      + exact proof.
      + simpl.
        exact proof.
  Defined.

End GaussOps.


Section Gauss.

  Context {R : hq}.
  Local Notation Σ := (iterop_fun hqzero op1).
  Local Notation "A ** B" := (@matrix_mult hq _ _ A _ B) (at level 80).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

   Require Import UniMath.Combinatorics.Maybe.

  (*TODO remove one of these internal definitions and rename remaining to indicate it is internal *)

  (* Selecting the first non-zero element index ≥ k, otherwise nothing and a witness*)
  (* Might break style slightly as it's returning not only a pivot, but a proof k ≤ i ? *)
  Definition select_pivot_row_easy' {n : nat} (mat : Matrix hq n n)
    (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : maybe (∑ i: ⟦ n ⟧%stn, k ≤ i).
  Proof.
    destruct iter as [ idx pr2' ].
    induction idx.
    - exact nothing.
    - destruct (natlthorgeh idx k). {exact nothing. }
      assert (pr2'' : idx < n). {apply pr2'. }
      destruct (mat k (idx ,, pr2'')).
      assert (pr2''' : idx < S n). {apply natlthtolths. exact pr2'. }
      destruct ( isdeceqhq   (mat (idx,, pr2'') k) 0%hq).
      + exact (IHidx pr2''').
      + exact (just ((idx ,, pr2''),, h)). (* TODO not h - variable names*)
  Defined.


  (* Selecting the first non-zero element index ≥ k, otherwise nothing - without the witness. *)
  Definition select_pivot_row_easy {n : nat} (mat : Matrix hq n n)
    (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : maybe (⟦ n ⟧%stn).
  Proof.
    destruct (select_pivot_row_easy' mat k iter) as [some | none].
    - exact (just (pr1 some)).
    - exact nothing.
  Defined.

  (* Proving pivot selection does not fail to find a new pivot element, if it exists. *)
  Definition select_pivot_row_correct1 {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < iter -> k ≤ i -> (hqneq (mat i k) 0%hq) ->
      ((select_pivot_row_easy  mat k iter)) != nothing .
  Proof.
    intros i H2 H3 H4. (* TODO variable names*)
    unfold select_pivot_row_easy, select_pivot_row_easy'.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      apply negnatlthn0 in H2.
      contradiction.
    - rewrite nat_rect_step.
      destruct (natlthorgeh pr1_ k).
      (* TODO simplify *)
      + assert (k_lt_pr1_ : i ≤ pr1_).  {apply natlthsntoleh; assumption.  }
        assert (k_le_pr1_ : k ≤ pr1_ ). {apply (istransnatleh H3 k_lt_pr1_). }
        apply fromempty.
        apply  natlehneggth  in k_le_pr1_.
        contradiction.
      + destruct (isdeceqhq _ _). 2: {simpl. unfold just. apply negpathsii1ii2. }
        simpl.
        destruct (nat_eq_or_neq i (pr1_)).
        2: { simpl. apply IHpr1_.
             assert (k_lt_pr1_ : i ≤ pr1_).  {apply natlthsntoleh; assumption.  }
             apply (natleh_neq k_lt_pr1_ h0).
        }
        simpl in H4.
        simpl in p.
        apply fromempty.
        rewrite <- p in H4.
        assert (absurd : mat i k = mat (pr1_ ,, pr2_) k).
        { apply maponpaths_2.
          apply subtypePath_prop.
          apply p0.
        }
        rewrite absurd in H4.
        contradiction.
  Defined.


  (* Proving pivot selection returns no false positive. *)
  Definition select_pivot_row_correct2 {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : ((select_pivot_row_easy  mat k iter)) != nothing )
    : (∑ i : ⟦ n ⟧%stn, i < iter × k ≤ i × (hqneq (mat i k) 0%hq)).
  Proof.
    revert ne_nothing.
    unfold select_pivot_row_easy, select_pivot_row_easy'.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      intros.
      contradiction.
    - rewrite nat_rect_step.
      destruct (natlthorgeh pr1_ k).
      {intros; contradiction. }
      destruct (isdeceqhq _ _). (* TODO naming, and improve proof if possible *)
      2 : { intros ?. use tpair.
            { exact (pr1_ ,, pr2_). }
            use tpair.
            - apply (natgthsnn pr1_).
            - simpl.
              destruct (stntonat _ _).
              + use tpair. {apply idpath. }
                apply n0.
              + use tpair.
                {apply h. }
                apply n0.
      }
      intros H.
      rewrite <- p in *.
      apply IHpr1_ in H.
      destruct H as [pr1_' pr2_'].
      destruct pr2_' as [pr2_' H'].
      destruct H' as [H' ?].
      use tpair.
      {exact pr1_'. }
      use tpair.
      {apply (istransnatlth _ _ _  pr2_' (natgthsnn pr1_) ). }
      use tpair.
      {assumption. }
      assumption.
  Defined.

  (* "Brute force" proofs - but  3,4 feel like they should follow directly from hypotheses contradicting 1,2 ?*)
  Definition select_pivot_row_correct3 {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    (ne_nothing : ((select_pivot_row_easy  mat k iter)) = nothing )
    : ∏ i : ⟦ n ⟧%stn, i < iter -> k ≤ i -> mat i k = 0%hq.
  Proof.
    intros i i_lt_iter k_leh_i.
    revert ne_nothing.
    unfold select_pivot_row_easy, select_pivot_row_easy'.
    destruct iter as [iter pr2_].
    induction iter.
    - apply fromempty. apply negnatlthn0 in i_lt_iter; assumption.
    - rewrite nat_rect_step.
      assert (obv : iter < S n). {apply (istransnatlth _ _ _ (natgthsnn iter) pr2_). }
      destruct (natlthorgeh iter k ).
      { assert (t1 : i ≤ iter).
        { apply natlthsntoleh; assumption. }
        assert (t2 : k ≤ iter).
        { apply (istransnatleh k_leh_i t1). }
        apply natlehtonegnatgth in t2.
        contradiction.
      }
      destruct (isdeceqhq (mat (iter,, pr2_) k) 0%hq).
      2 : { simpl. unfold just.
            intros contr.
            apply negpathsii1ii2 in contr.
            apply fromempty; assumption.
      }
      destruct (natlehchoice i iter). {  apply natlthsntoleh; assumption. }
      + intros H.
        rewrite <- p in *.
        apply IHiter in H; try assumption.
      + intros ?.
        rewrite <- p.
        apply maponpaths_2.
        apply subtypePath_prop.
        apply p0.
  Defined.

  Definition select_pivot_row_correct4 {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : ( ∏ i : ⟦ n ⟧%stn, i < iter -> k ≤ i -> mat i k = 0%hq) -> (select_pivot_row_easy  mat k iter) = nothing.
  Proof.
    intros H.
    unfold select_pivot_row_easy, select_pivot_row_easy'.
    destruct iter as [iter p].
    induction iter.
    - apply idpath.
    - rewrite nat_rect_step.
      destruct (natlthorgeh iter k).
      { apply idpath. }
      assert (obv : iter < S n). {apply (istransnatgth _ _ _ (natgthsnn n) p ) . }
      destruct (isdeceqhq (mat (iter,, p) k) 0%hq).
      + apply IHiter.
        intros.
        apply H.  {apply (istransnatgth _ _ _ (natgthsnn iter) X ) . }
        assumption.
      + rewrite H in n0; try assumption.
        { contradiction. }
        apply (natgthsnn iter).
  Defined.

  Definition select_pivot_row_choice {n : nat} (mat : Matrix hq n n)
      (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) :
      coprod ((select_pivot_row_easy mat k iter) != nothing)
             ((select_pivot_row_easy mat k iter) = nothing).
  Proof.
    destruct (((select_pivot_row_easy  mat k iter))).
    - apply ii1. apply negpathsii1ii2.
    - apply ii2. rewrite u. exists.
  Defined.

  (* Selecting the first non-zero element index ≥ k and a proof mat idx k ≠ 0
     , or producing a witness of a cleared column segment.
     TODO naming. *)
  Definition select_pivot_row_easy'' {n : nat} (mat : Matrix hq n n)
    (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) :
    coprod ((∑ i: ⟦ n ⟧%stn, k ≤ i × (hqneq (mat i k) 0%hq))) (∏ i : ⟦ n ⟧%stn, i < iter -> k ≤ i -> mat i k = 0%hq ).
  Proof.
    destruct( select_pivot_row_choice mat k iter) as [nnone | none].
    - apply ii1. use tpair; apply (select_pivot_row_correct2 mat k iter); assumption.
    - apply ii2. apply select_pivot_row_correct3; assumption.
  Defined.



  (* I think this one might speed up a proof or too below - use it ? *)
  Definition gauss_clear_column_step' (n : nat) (k : (⟦ n ⟧%stn))
             (j : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct (natgthorleh j k) as [? | ?].
    - exact ((gauss_add_row mat k j (- ( (mat j k) * hqmultinv (mat k k)))%hq
           )).
    - exact mat.
  Defined.

  (* Refactored to include induction on natgthorleh j k*)
  Definition gauss_clear_column_step (n : nat) (k : (⟦ n ⟧%stn))
             (j : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct (natgthorleh j k) as [? | ?].
    - exact ((make_add_row_matrix k j (- ( (mat j k) * hqmultinv (mat k k)))%hq
      ** mat)).
    - exact mat.
  Defined.

  Lemma gauss_clear_column_step_eq (n : nat) (k : (⟦ n ⟧%stn))
             (j : (⟦ n ⟧%stn)) (mat : Matrix F n n):
    gauss_clear_column_step n k j mat = gauss_clear_column_step' n k j mat.
  Proof.
    unfold gauss_clear_column_step.
    unfold gauss_clear_column_step'.
    destruct (natgthorleh j k) as [? | ?].
    2 : {apply idpath. }
    rewrite add_row_mat_elementary.
    - apply idpath.
    - apply issymm_natneq.
      apply natgthtoneq.
      assumption.
  Defined.

  (*
  (* iter from n -> 1, 0 return as we start with n - k (might = n)*)
  (* assumes we have the non-zero pivot element at index [k, k] *)
  (* TODO deprecated; replace ith [gauss_clear_column'] *)
  (* [gauss_clear_column_old mat k p _]:
    clear column [k] in rows [p ≤ i < n] *)
  Definition gauss_clear_column_old'  { n : nat } (*(iter : ⟦ n ⟧%stn)*)
    (mat : Matrix F n n) (k : (⟦ n ⟧%stn)) (p : nat) (lt_p_n : p < n)
    : Matrix F n n.
  Proof.
    (*revert mat.*)
    (*destruct iter as [pr1_ pr2_].*)
    induction p as [ | m gauss_clear_column_IH ].
    {exact mat. }  (* not applying the step since surely 0 ≤ k *)
    set (piv := mat k k).
    set (pr1idx := S m).
    set (j := make_stn n (S m) lt_p_n).
    set (m_lt_n := istransnatlth m (S m) n (natlthnsn m) lt_p_n).
    (*exact (gauss_clear_column_IH m_lt_n
               ( gauss_clear_column_step' n k j mat)).*)   (* <--- this is the old, incorrect version *)
    exact (gauss_clear_column_step' n k j (gauss_clear_column_IH m_lt_n)).
  Defined.*)

  (* Equivalent and the right definition with iter as S n instead of n -> TODO is
     replacing uses of the other one with this one *)
  (* [gauss_clear_column' mat k p _]:
    clear column [k] in rows [0 ≤ i < p],
    from row 0 up to row p (though order doesn’t matter. *)
  (* TODO: rename to [gauss_clear_column_segment]
     TODO: refactor to use a chosen/given pivot, not always diagonal *)
  (* Temporarily renamed to old ! To try to make all lemmas work on this one. *)
  Definition gauss_clear_column_old { n : nat } (mat : Matrix F n n)
      (k : (⟦ n ⟧%stn)) (p : ⟦ S n ⟧%stn)
    : Matrix F n n.
  Proof.
    destruct p as [p lt_p].
    induction p as [ | p gauss_clear_column_IH ].
    { exact mat. }  (* not applying the step since surely 0 ≤ k *)
    refine (gauss_clear_column_step' n k (p,, lt_p) (gauss_clear_column_IH _)).
    apply (istransnatlth _ _ _ (natlthnsn p) lt_p).
  Defined.

  (* A third version that more closely follows the matrix construction -
     we break at iter ≤ k. This however is already done in gauss_clear_column_step. *)
  Definition gauss_clear_column'' { n : nat }
    (mat : Matrix F n n) (k : (⟦ n ⟧%stn))  (iter : ⟦ S n ⟧%stn) : Matrix F n n.
  Proof.
    (*revert mat.*)
    destruct iter as [pr1_ pr2_].
    induction pr1_ as [ | m gauss_clear_column_IH ].
    {exact mat. }  (* not applying the step since surely 0 ≤ k *)
    set (piv := mat k k).
    destruct (natgthorleh m k).
    2 : {exact mat. }
    assert (m_lt_n : m < S n). {  apply (istransnatlth _ _ _ (natlthnsn m) pr2_) . }
    exact (gauss_clear_column_step' n k (m,, pr2_) (gauss_clear_column_IH m_lt_n)).
  Defined.


  (* Clearing a column by only left multiplication by invertible matrices *)
  Lemma gauss_clear_column_as_left_matrix  { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k : (⟦ n ⟧%stn)) : Matrix hq n n.
  Proof.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - exact (*(@identity_matrix hq n)*) mat.
    - assert (pr2_' : pr1_ < n). { apply pr2_. }
      assert (pr2_'' : pr1_ < S n). { apply (istransnatlth _ _ _ (natlthnsn pr1_ ) pr2_ ). }
       destruct (natgthorleh pr1_ k).
      + exact (make_add_row_matrix k  (pr1_,, pr2_) (- ((mat (pr1_,,pr2_) k) * hqmultinv (mat k k)))%hq
              ** (IHpr1_ pr2_'')).
      + exact (@identity_matrix hq n ** (IHpr1_ pr2_'' )). (* TODO break completely? *)
  Defined.

  (* TODO generalize to rigs *)
  Lemma gauss_add_row_inv0 {n : nat} (mat : Matrix hq n n) (i j: ⟦ n ⟧%stn) (s : hq)
    : ∏ (k : ⟦ n ⟧%stn), j ≠ k -> gauss_add_row  mat i j s k = mat k.
  Proof.
    intros k j_ne_k.
    unfold gauss_add_row.
    destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j].
    - rewrite k_eq_j in j_ne_k.
      apply isirrefl_natneq in j_ne_k.
      apply fromempty; assumption.
    - simpl.
      reflexivity.
  Defined.


  (* Restating a similar lemma for the regular version of this operation, in order to prove their
     equivalence *)
  Lemma gauss_clear_column_as_left_matrix_inv0  { n : nat } (pr1_: nat) (pr2_ : pr1_ < S n)
        (mat : Matrix hq n n) (k : (⟦ n ⟧%stn)) (i : ⟦ n ⟧%stn): pr1_  ≤ i ->
        gauss_clear_column_as_left_matrix (pr1_,, pr2_) mat k i = mat i.
  Proof.
    induction pr1_.
    - simpl. reflexivity.
    - intros.
      unfold gauss_clear_column_as_left_matrix.
      rewrite nat_rect_step.
      destruct (natgthorleh pr1_ k).
      + unfold gauss_clear_column_as_left_matrix in IHpr1_.
        assert (pr2_': pr1_ < S n). {apply (istransnatlth _ _ _ (natgthsnn pr1_) pr2_). }
        ( rewrite <- (IHpr1_ pr2_')).
        2 : { apply natlehtolehs in X; assumption. }
        rewrite add_row_mat_elementary.
        2: {apply issymm_natneq.  apply natgthtoneq in h. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply snlehtotonlt in X.
            - apply issymm_natneq. apply natgthtoneq; assumption.
            - apply natneq0togth0.
              destruct (natchoice0 pr1_).
              + rewrite <- p in h.
                apply negnatgth0n in h.
                contradiction.
              + apply natgthtoneq.
                assumption.
        }

        apply maponpaths_2.
        apply proofirrelevance.
        apply propproperty.
      + rewrite matlunax2.
        assert (pr2_': pr1_ < S n). {apply (istransnatlth _ _ _ (natgthsnn pr1_) pr2_). }
        rewrite <- (IHpr1_ pr2_').
        2 : {apply (istransnatleh (natgehsnn pr1_) X). }
        unfold gauss_clear_column_as_left_matrix.
        apply maponpaths_2.
        apply proofirrelevance.
        apply propproperty.
  Defined.

  (*TODO why are pr1_ pr2_ separate ?  *)
  Lemma gauss_clear_column_as_left_matrix_inv1  { n : nat } (pr1_: nat) (pr2_ : pr1_ < S n)
        (mat : Matrix hq n n) (k : (⟦ n ⟧%stn)) (i : ⟦ n ⟧%stn) (i_leh_k : i ≤ k):
        gauss_clear_column_as_left_matrix (pr1_,, pr2_) mat k i = mat i.
  Proof.
    induction pr1_.
    - simpl. reflexivity.
    - intros.
      unfold gauss_clear_column_as_left_matrix.
      rewrite nat_rect_step.
      destruct (natgthorleh pr1_ k).
      + rewrite add_row_mat_elementary.
        2: {apply issymm_natneq. apply natgthtoneq. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply natgthtoneq. apply (natlehlthtrans _ _ _  i_leh_k h).  }
        unfold gauss_clear_column_as_left_matrix in IHpr1_.
        rewrite IHpr1_.
        reflexivity.
      + rewrite matlunax2.
        unfold gauss_clear_column_as_left_matrix in IHpr1_.
        rewrite   IHpr1_.
        reflexivity.
  Defined.

  Lemma clear_column_matrix_invertible  { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k : (⟦ n ⟧%stn))
        : (@matrix_inverse hq n mat)
        -> @matrix_inverse hq _ (gauss_clear_column_as_left_matrix  iter mat k).
  Proof.
    intros isinv.
    set (pre := gauss_clear_column_as_left_matrix iter mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - apply isinv.
    - unfold pre.
      rewrite nat_rect_step.
      destruct (natgthorleh pr1_ k) as [gt | ?].
      2: { apply inv_matrix_prod_is_inv.
           - apply identity_matrix_is_inv.
           - apply IHpr1_. }
      apply inv_matrix_prod_is_inv.
      { apply add_row_matrix_is_inv.
       - apply natlthtoneq; assumption.
       - apply (stn_implies_ngt0 k).
      }
      apply IHpr1_.
  Defined.

  (* Move all invs up here ? *)
  Lemma gauss_clear_column_step_inv4
     (n : nat) (k: (⟦ n ⟧%stn))
         (j : (⟦ n ⟧%stn)) (mat : Matrix F n n)
         (p : j ≤ k) : (gauss_clear_column_step n k j mat) = mat.
  Proof.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k) as [j_gt_k | j_leq_k].
    2: {apply idpath. }
    apply natgthtonegnatleh in j_gt_k.
    contradiction j_gt_k .
  Defined.


  (* [gauss_clear_columns_up_to k mat]:
   clear all columns [i] of [mat] for 0 ≤ i < k,
   from 0 up to k–1 *)
(* Problem: currently there is no pivot selection here.  ([gauss_iterate'] below does pivot selection, but has other issues)
   TODO: add pivot selection in this version, e.g. via making the step use a function like
  [gauss_clear_whole_column m k
   = gauss_clear_column_segment_with_given_pivot m k (select_pivot m k) ]

  and (if necessary) keep track of pivots through iteration, like in [gauss_iterate'];

  or else fix [gauss_iterate'] to iterate more cleanly, like this version
*)
  Definition gauss_clear_columns_up_to { n : nat } (p : n > 0) (* Remove p when gcc is refactored *)
             (k : (⟦ S n ⟧%stn))
             (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct k as [k lt_k_n].
    induction k as [ | k' gauss_clear_earlier_columns].
    - exact mat.
    - assert (lt : k' < S n). {apply (istransnatlth _ _ _ (natgthsnn k') lt_k_n ). }
      set (piv :=  select_pivot_row_easy'' (gauss_clear_earlier_columns lt) (k',, lt_k_n) (n,, natgthsnn n)).
      destruct piv as [piv | ?]. (* TODO make presentable *)
      2: { refine (gauss_clear_earlier_columns  (istransnatlth _ _ _ (natlthnsn k') lt_k_n) ). }
      refine (gauss_clear_column_old _   (k' ,, lt_k_n)  (*(pr1 piv)*)  (n ,, natlthnsn n ) ).
      refine (gauss_switch_row (gauss_clear_earlier_columns _ ) (k' ,, lt_k_n) (pr1 piv) ).
      exact lt.
  Defined.

  (* invertible matrix, such that left-multiplication by this
     corresponds to [gauss_clear_columns_up_to]  -
     NOT FINISHED, this version carries out multiplication on the input matrix -
     we return from this function A' ** mat,   but we'd like only A* *)
  Lemma clear_columns_up_to_as_left_matrix  { n : nat } (p : n > 0) (* Remove p when gcc is refactored *)
        (k : (⟦ S n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct k as [k lt_k_n].
    induction k as [ | k' gauss_clear_earlier_columns].
    - exact mat. (* (@identity_matrix hq n). *)
    - (*set (piv :=  select_pivot_row_easy'' mat (k',, lt_k_n) (n,, natgthsnn n)).*)
      assert (lt : k' < S n). {apply (istransnatlth _ _ _ (natgthsnn k') lt_k_n ). }
      set (piv :=  select_pivot_row_easy'' (gauss_clear_earlier_columns lt) (k',, lt_k_n) (n,, natgthsnn n)).
      destruct piv as [piv | ?].
      2: { refine (@identity_matrix hq n ** (gauss_clear_earlier_columns lt)). }
      refine (gauss_clear_column_as_left_matrix  (n,, natlthnsn n) _ (k' ,, lt_k_n)  ).
      refine (@matrix_mult hq _ _  _  _ (gauss_clear_earlier_columns _)).
      refine (make_gauss_switch_row_matrix _ (k' ,, lt_k_n) (pr1 piv)).
      apply (istransnatlth _ _ _ (natlthnsn k') lt_k_n) .
  Defined.

  (* the deining property of [clear_columns_up_to_as_left_matrix]
     - proven later, after the equivalence of clear columns procedure - TODO remove / move  *)
  Lemma clear_columns_up_to_as_left_matrix_eq {n : nat} (p : ⟦ S n ⟧%stn) (* Remove p when gcc is refactored *)
        (H : n > 0) (*TODO remove *) (k : (⟦ n ⟧%stn)) (mat : Matrix F n n)
    : (clear_columns_up_to_as_left_matrix H p mat) = (gauss_clear_columns_up_to H p mat ).
  Proof.
    intros.
    unfold clear_columns_up_to_as_left_matrix, gauss_clear_columns_up_to.
    destruct p as [p p_lt_sn].
    induction p.
    - simpl. apply idpath.
    - do 2 rewrite nat_rect_step.
      destruct (select_pivot_row_easy mat (p,, p_lt_sn) (n,, natgthsnn n)).
      +
  Abort. (* We need gcc as matrix = gcc here, but it's stated below. *)

  Lemma clear_columns_up_to_matrix_invertible {n : nat} (p : ⟦ S n ⟧%stn) (* Remove p when gcc is refactored *)
    (H : n > 0) (k : (⟦ n ⟧%stn)) (mat : Matrix F n n)
    : (@matrix_inverse hq _ mat) ->
       @matrix_inverse hq _  (clear_columns_up_to_as_left_matrix H p mat).
  Proof.
    intros isinv.
    set (pre := gauss_clear_column_as_left_matrix p mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct p as [pr1_ pr2_].
    induction pr1_.
    - exact isinv.
    - unfold clear_columns_up_to_as_left_matrix.
      rewrite nat_rect_step.
      destruct (select_pivot_row_easy'' _ _).
      + apply clear_column_matrix_invertible .
        refine (inv_matrix_prod_is_inv _ _ _ _ ).
        { apply switch_row_matrix_is_inv.
          exact (mat k k). } (* TODO hmm? What is this pointless argument ? *)
        apply IHpr1_.
      + refine (inv_matrix_prod_is_inv _ _ _ _ ).
        {apply identity_matrix_is_inv. } (* TODO make name clearer *)
        apply IHpr1_.
  Defined.

  (* Inputting a matrix and transforming it into an upper-triangular matrix by
     elementary matrix operations or equivalent *)
  Definition gauss_clear_all_column_segments { n : nat } (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct (natchoice0 n). {exact mat. }
    refine (gauss_clear_columns_up_to  _ (n,,_) mat).
    - assumption.
    - exact (natgthsnn n).
  Defined.


  (* TODO move up *)
  Require Import UniMath.NumberSystems.Integers.

  (* The clear column step operation does clear the target entry (mat (k j)) *)
  Lemma gauss_clear_column_step_inv1 (n : nat) (k : (⟦ n ⟧%stn))
        (j : (⟦ n ⟧%stn)) (mat : Matrix F n n)  (p' : mat k k != 0%hq)
        (p'' : j > k) (* (k_neq_j : k ≠ j) *) :
    (gauss_clear_column_step n k j mat) j k = 0%hq.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k) as [? | ?].
    2 : { apply natlehtonegnatgth in p''.
          - apply fromempty. assumption.
          - assumption. }
    unfold make_add_row_matrix.
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    assert (p''' : n > 0). { apply (stn_implies_ngt0 k). }   (* should be gt0 in name! TODO <- what this means?*)
    set (f := λ i, _).
    rewrite (@two_pulse_function_sums_to_points_rig' F n _ p''' k j). (*TODO fix ugly signature *)
    - unfold f.
      unfold identity_matrix, pointwise, const_vec.
      destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j].
      + rewrite stn_neq_or_neq_refl; simpl.
        symmetry in k_eq_j.
        rewrite (stn_eq_or_neq_left k_eq_j); simpl.
        do 2 rewrite (stn_neq_or_neq_refl); simpl.
        symmetry in k_eq_j.
        rewrite (stn_eq_or_neq_left k_eq_j); simpl.
        rewrite k_eq_j.
        rewrite (@rigrunax2 F); rewrite <- k_eq_j.
        rewrite (hqisrinvmultinv (mat k k)). 2 : {exact p'. }
        assert (∏ (x : hq), x + (-x) = x - x)%hq.
        {intros. rewrite hqrminus. rewrite hqpluscomm. apply hqlminus. }
        rewrite (@ringrinvax1 hq).
        rewrite (@rigmult0x hq).
        rewrite (@riglunax1 F).   (* TODO two things here. Use ring lemmas more, generalize field *)
        apply idpath.
      + do 2 rewrite stn_neq_or_neq_refl, coprod_rect_compute_1.
        apply issymm_natneq in k_neq_j.
        rewrite (stn_eq_or_neq_right k_neq_j), coprod_rect_compute_2.
        rewrite stn_neq_or_neq_refl. simpl.
        rewrite (@rigrunax2 F), (@riglunax1 F).
        apply issymm_natneq in k_neq_j.
        rewrite (stn_eq_or_neq_right k_neq_j). simpl.
        unfold const_vec.
        etrans. { apply maponpaths.  reflexivity. }
        rewrite (@rigmultx0 F).
        etrans.
          {apply maponpaths. rewrite (@rigrunax1 F).
          rewrite (@riglunax2 F). reflexivity. }
        etrans.
          { apply maponpaths_2.
            rewrite <- (@ringrmultminus hq).
            rewrite hqmultassoc.
            rewrite (@ringlmultminus hq).
            rewrite (hqmultcomm _ (mat k k) ).
            rewrite (hqisrinvmultinv (mat k k)).
            2 : {exact p'. }
            (*rewrite hqmultr1. *)
            rewrite hqmultcomm.
            rewrite (@ringlmultminus hq).
            rewrite (@riglunax2 hq).
           reflexivity. }
      apply hqlminus.
    - apply natlthtoneq. assumption.  (* TODO move earlier in signature of pf sums to p *)
    - intros i i_neq_k i_neq_j; unfold f.
      rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
      unfold identity_matrix, pointwise.
      apply issymm_natneq in i_neq_k.
      apply issymm_natneq in i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_k), coprod_rect_compute_2.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      etrans. {apply maponpaths_2. rewrite hqplusl0. reflexivity. }
      rewrite (rigmultx0 F (_)%hq).
      apply rigmult0x.
  Admitted.
  (*Defined.*) (* TOOD really slow proof! Replace admitted by defined when sped up. *)

    (* The clear column step operation only changes the target row*)
  Lemma gauss_clear_column_step_inv2 (n : nat) (k: (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix F n n) (j : ⟦ n ⟧%stn)
        (p : r ≠ j)  : (gauss_clear_column_step n k j mat) r = mat r.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k) as [? | ?].
    2 : {apply idpath. }
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_add_row_matrix, pointwise.
    assert (p'' : n > 0). { apply stn_implies_ngt0. assumption. }
    apply funextfun. intros q.
    destruct (stn_eq_or_neq r j ) as [r_eq_j | r_neq_j].
    { simpl. rewrite r_eq_j in p. apply isirrefl_natneq in p; contradiction. }
    simpl.
    rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 j ) r ).
    - rewrite (id_mat_ii).
      apply (@riglunax2 F).
    - unfold is_pulse_function. (* TODO use just one of these pulse defs *)
      intros x r_neq_x.
      change (_ * mat x q)%ring with (@identity_matrix hq n r x * mat x q)%hq. (*Why need  this and why slow? *)
      rewrite (id_mat_ij r x r_neq_x).
      apply rigmult0x.
   Defined.

  Lemma gauss_clear_column_step_inv2' (n : nat) (k: (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix F n n) (j j' : ⟦ n ⟧%stn)
        (p : r ≠ j) : (gauss_clear_column_step n k j mat) r j' = mat r j'.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k) as [h | ?].
    2 : {apply idpath. }
    rewrite matrix_mult_eq; unfold matrix_mult_unf.
    unfold make_add_row_matrix.
    assert (p' : n > 0). { apply stn_implies_ngt0. assumption. }
    set (f := λ i : (⟦ n ⟧%stn), _).
    (*TODO proof would be tightened up without this inline assert *)
    assert (b : (*Σ f*)   iterop_fun 0%rig op1  f = f r ). {
      apply (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 j) r).
      unfold is_pulse_function.
      intros q r_neq_k.
      unfold f.
      destruct (stn_eq_or_neq r j) as [r_eq_q | r_neq_q].
      - rewrite r_eq_q in p. (*TODO*)
        apply (isirrefl_natneq) in p.
        contradiction.
      - unfold identity_matrix.
        rewrite coprod_rect_compute_2.
        rewrite (stn_eq_or_neq_right r_neq_k), coprod_rect_compute_2.
        apply rigmult0x.
    }
    unfold pointwise.
    rewrite b.
    unfold f.
    rewrite (stn_eq_or_neq_right p), coprod_rect_compute_2.
    unfold identity_matrix.
    rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
    apply (@riglunax2 F).
  Defined.

  Lemma gauss_clear_column_step_inv3
     (n : nat) (k: (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix F n n) (j j' : ⟦ n ⟧%stn)
         (p : r < j) : (gauss_clear_column_step n k j mat) r j' = mat r j'.
  Proof.
    assert (p': r ≠ j). {apply issymm_natneq.  apply natgthtoneq. assumption. }
    rewrite (gauss_clear_column_step_inv2 n k r mat j  p').
    apply idpath.
  Defined.

  Lemma gauss_clear_column_step_inv3'
     (n : nat) (k: (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix F n n) (j j' : ⟦ n ⟧%stn)
         (p : j ≤ k) : (gauss_clear_column_step n k j mat) r j' = mat r j'.
  Proof.
    unfold gauss_clear_column_step.
    destruct (natgthorleh _ _) as [gt | leh].
    - apply natgthtonegnatleh in gt.
      contradiction.
    - apply idpath.
  Defined.

  Lemma gauss_clear_column_step_inv5
     (n : nat) (k: (⟦ n ⟧%stn))
         (j r : (⟦ n ⟧%stn)) (mat : Matrix F n n)
         (p : r ≤ k) : (gauss_clear_column_step n k j mat) r = mat r.
  Proof.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k) as [j_gt_k | j_leq_k].
    2: {apply idpath. }
    rewrite add_row_mat_elementary.
    2 : {apply issymm_natneq.
         apply natgthtoneq.
         assumption.
    }
    (* Might want to generalize this lemma - gauss_add_row j k mat r = mat r if  r ≠ k *)
    unfold gauss_add_row.
    destruct (stn_eq_or_neq r j) as [eq | neq].
    - apply natlehneggth in p.
      apply fromempty.
      rewrite <- eq in j_gt_k.
      exact (p j_gt_k).
    - simpl.
      reflexivity.
  Defined.


  (* Proving mat r  is unchanged after column clearance   if r > n'. *)
  Lemma gauss_clear_column_inv0'
        { n : nat } (k : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (mat : Matrix F n n) (r : ⟦ n ⟧%stn)
    (r_gt_n' : r ≥ iter) : (gauss_clear_column_old  mat k iter) r = mat r.
  Proof.
    destruct iter as [n' p].
    induction n'.
    - simpl.
      reflexivity.
    - set (sn' := make_stn n n' p).
      assert (q : n' < n). {apply p. }
      assert (q': r > n'). {apply r_gt_n'. }
      destruct (stn_eq_or_neq (make_stn n (n') p) k ).
      { unfold gauss_clear_column_old, gauss_clear_column_step.
        - rewrite nat_rect_step.
          rewrite <- gauss_clear_column_step_eq.
          rewrite gauss_clear_column_step_inv2.
          2 : { apply natgthtoneq in r_gt_n'.  apply r_gt_n'.  }
          unfold gauss_clear_column_old in IHn'.
          apply IHn'.
          apply natgthtogeh;assumption.
      }
      simpl.
      unfold gauss_clear_column_step'.
      destruct (natgthorleh (make_stn n (n') p ) k).
      + simpl.
        unfold make_add_row_matrix.
        unfold gauss_add_row.
        apply funextfun. intros x.
        simpl.
        assert (neq : r ≠ (n')).
        { apply (natgthtoneq _ _ r_gt_n'). }
        simpl.
        destruct (stn_eq_or_neq r (make_stn n (n') p)).
        * rewrite p0 in neq.
          apply isirrefl_natneq in neq.
          contradiction.
        * simpl.
          unfold gauss_clear_column_old in *.
          rewrite nat_rect_step.
          rewrite <- gauss_clear_column_step_eq.
          rewrite gauss_clear_column_step_inv2.
          2 : {assumption. }
          rewrite IHn'.
          {apply idpath. }
          refine (istransnatlth _ _ _ _ _).
          { exact (natlthnsn n'). }
          apply q'.
      + simpl.
        unfold gauss_clear_column_old in *.
        rewrite nat_rect_step.
        rewrite <- gauss_clear_column_step_eq.
        rewrite gauss_clear_column_step_inv2.
        2 : {apply (natgthtoneq _ _ q'). }
        rewrite IHn'.
        { apply idpath. }
        apply natgthtogeh.
        apply r_gt_n'.
  Defined.


  (* if the target row r ≤  the pivot row k,
     mat r is not changed by the clearing procedure. *)
  Lemma gauss_clear_column_inv3
        { n : nat } (k r : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (p' : r ≤ k)
        (mat : Matrix F n n) (*(kk_ne_0 : mat k k != 0%hq)*) :
    ((gauss_clear_column_old mat k iter) r = mat r).
  Proof.
    destruct iter as [n' p].
    induction n'.
    { unfold gauss_clear_column_old. simpl. reflexivity. }
    simpl.
    unfold gauss_clear_column_old.
    apply funextfun. intros q.
    rewrite nat_rect_step.
    rewrite <- gauss_clear_column_step_eq.
    rewrite gauss_clear_column_step_inv5.
    2 : {assumption. }
    unfold gauss_clear_column_old in IHn'.
    rewrite IHn'.
    reflexivity.
  Defined.

  (* (* It appears we ended up proving this inline and it could be removed from here *)
  Lemma gauss_clear_column_commute
    { n : nat } (mat : Matrix F n n) (j k r : ⟦ n ⟧%stn)
    (n' : nat) (p : n' < n) (p' : j > n') :  (* do we need p' ? *)
    gauss_clear_column_step n k j (gauss_clear_column_old mat k n' p) r
 =  gauss_clear_column_old (gauss_clear_column_step n k j mat) k n' p r.
  Proof.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k ).
    2 : { reflexivity.  }
    unfold make_add_row_matrix.
    apply funextfun. intros x.
    unfold "^", "**", "^", const_vec, col, row, transpose, flip.
    rewrite gauss_clear_column_inv0'.
  Abort. *)


  (* Proving the column clearing procedure works on one row at a time *)
  Lemma gauss_clear_column_inv0
        { n : nat } (k : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn) (mat : Matrix F n n) (*(p' : mat k k != 0%hq)*) : ∏ r : (⟦ n ⟧%stn),
    r < iter -> ((gauss_clear_column_old  mat k iter) r = (gauss_clear_column_step' n k r mat) r).
  Proof.
    destruct iter as [n' p].
    revert mat k (*p'*) p.
    induction n'.
    - intros mat k (*kk_ne_0*) p r (* ? *) r_le_0.
      unfold gauss_clear_column_old, gauss_clear_column_step'.
      simpl.
      destruct (natgthorleh r k) as [absurd | ?].
      + contradiction (negnatgth0n r r_le_0).
      + apply idpath.
    - intros mat k (*kk_ne_0*) p r r_le_sn.
      set (sn' := make_stn n (n') p).
      assert (p' : n' < S n). {apply (istransnatlth _ _ _ (natgthsnn n') p). }
      set (IHnp := IHn'  mat k (*kk_ne_0*) p').
      destruct (natlehchoice r (n')) as [? | eq]. {assumption. }
      +
        assert (follows : r ≤ n'). { apply natlthtoleh in h. assumption. }
        unfold gauss_clear_column_old.
        rewrite nat_rect_step.
        rewrite <- (IHnp r h).
        rewrite <- gauss_clear_column_step_eq.
        rewrite (gauss_clear_column_step_inv2).
        2 : { apply natgthtoneq in h. apply issymm_natneq. apply h. }
        etrans.
        { assert (eq : p' =  (istransnatlth n' (S n') (S n) (natlthnsn n') p)).
          apply proofirrelevance.
          apply propproperty.
          rewrite <- eq.
          apply idpath.
        }
        apply idpath.
      + rewrite <- gauss_clear_column_step_eq.
        rewrite gauss_clear_column_step_eq.
        simpl.
        (* *)
        unfold gauss_clear_column_old.
        rewrite nat_rect_step.
        do 2 rewrite <- gauss_clear_column_step_eq.
        set (sn'' := (make_stn n ( n') p)).
        set (p'' := istransnatlth _ _ _ _ _).
        replace   (gauss_clear_column_step n k sn'' _ r)
          with (gauss_clear_column_step n k sn'' mat r).
        { replace sn'' with r.
          { apply idpath. }
          rewrite (@subtypePath_prop _ _ r (n',, p)). {reflexivity. }
          apply eq.
        }
        assert (step1 : (gauss_clear_column_old mat k (n',, p'')) r = mat r).
        { rewrite gauss_clear_column_inv0'.
          - apply idpath.
          - rewrite eq.
            apply natlthnsn. }
         assert (commute :  gauss_clear_column_step n k sn'' (gauss_clear_column_old mat k  (n',, p'')) r
                           =  gauss_clear_column_old (gauss_clear_column_step n k sn'' mat) k (n',, p'')  r).
        (* The main challenge with this proof lies here *)
        (* Can we do better than unfolding and brute-forcing this proof ? *)
        { unfold gauss_clear_column_step.
          destruct (natgthorleh sn'' k).
          2 : { reflexivity.  }
          unfold make_add_row_matrix.
          apply funextfun. intros x.
          rewrite matrix_mult_eq; unfold matrix_mult_unf, pointwise.
          rewrite gauss_clear_column_inv0'.
          2 : { unfold sn''. apply (natlthnsn). }
          assert (eq' : r = sn'').
          { rewrite (@subtypePath_prop _ _ r (n',, p)). {reflexivity. } apply eq. }
          rewrite <- eq'.
          rewrite (stn_neq_or_neq_refl).
          simpl.
          apply pathsinv0.
          etrans.
          { rewrite (gauss_clear_column_inv0').
            - apply idpath.
            - rewrite eq.
              apply natlthnsn.
          }
          unfold pointwise.
          unfold const_vec, pointwise.
          rewrite matrix_mult_eq; unfold matrix_mult_unf.
          rewrite stn_neq_or_neq_refl; simpl.
          unfold const_vec, pointwise.
          apply maponpaths.
          apply funextfun. intros y.
          destruct (stn_eq_or_neq k y) as [eq'' | ?].
          - rewrite <- eq'' in *.
            rewrite id_mat_ii.
            do 2 rewrite (@rigrunax2 hq).
            rewrite gauss_clear_column_inv3.
            + apply idpath.
            + apply isreflnatleh.
            (*+ apply kk_ne_0.*)
             (* Need a lemma that states that (clear column mat ) pivot = mat pivot *)
          - unfold pointwise, const_vec.
            unfold identity_matrix.
            rewrite (stn_eq_or_neq_right h0); simpl.
            do 2 rewrite (@rigmultx0 hq); rewrite (@rigrunax1 hq).
            destruct (stn_eq_or_neq r y) as [eq'' | ?].
            * rewrite eq''. simpl.
              rewrite gauss_clear_column_inv0'.
              { apply idpath. }
              rewrite <- eq''.
              rewrite eq.
              apply natgthsnn.
            * simpl.
              do 2 rewrite (@rigmult0x hq).
              apply idpath.
        }
        unfold gauss_clear_column_old in commute.
        set (f := @gauss_clear_column_inv0'). (* Did I phrase this one wrongly? *)
        unfold gauss_clear_column_old in f.
        rewrite commute.
        rewrite gauss_clear_column_step_eq.
        rewrite <- gauss_clear_column_step_eq.
        rewrite <- (f n k ( n' ,, p'')). {reflexivity. }
        rewrite eq.
        apply isreflnatleh.
  Defined.


  (* Proving mat r  is unchanged after column clearance   if r > n'. *)
  Lemma gauss_clear_column_inv0''
        { n : nat } (k : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (mat : Matrix F n n) (r : ⟦ n ⟧%stn)
    (r_gt_n' : r ≥ iter) : (gauss_clear_column_old mat k iter) r = mat r.
  Proof.
    destruct iter as [n' p].
    induction n'.
    - simpl.
      reflexivity.
    - set (sn' := make_stn n n' p).
      assert (q : n' < n). { exact p. }
      assert (q': r > n'). {apply (natgehtogthsn _ _ r_gt_n'). }
      unfold gauss_clear_column_old in *.
      rewrite nat_rect_step.
      rewrite <- gauss_clear_column_step_eq.
      rewrite gauss_clear_column_step_inv2.
      2: { apply natgthtoneq. assumption. }
      rewrite IHn'.
      + reflexivity.
      + apply (natgthtogeh). assumption.
  Defined.


  (* Invariant stating that the clearing procedure does clear all the target entries (r, k) for r > k. *)
  Lemma gauss_clear_column_inv1
        { n : nat } (k : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn)  (mat : Matrix F n n) (p' : mat k k != 0%hq) :  ∏ r : (⟦ n ⟧%stn),
    r < iter -> r > k -> ((gauss_clear_column_old mat k iter) r k = 0%hq).
  Proof.
    destruct iter as [n' p].
    intros r r_le_n' r_gt_k.
    rewrite (gauss_clear_column_inv0  k (n' ,, p) mat (*p'*) r r_le_n').
    rewrite <- gauss_clear_column_step_eq.
    rewrite (gauss_clear_column_step_inv1 n k r mat).
    - reflexivity.
    - exact p'.
    - assumption.
  Defined.


  (* if the iterator n' ≤   the pivot index k,
     applying the clearing procedure leaves mat invariant. *)
  Lemma gauss_clear_column_inv2
        { n : nat } (k : (⟦ n ⟧%stn))
        (iter : ⟦ S n ⟧%stn) (p' : S iter ≤ k)
        (mat : Matrix F n n) (kk_ne_0 : mat k k != 0%hq) :
    ((gauss_clear_column_old mat k iter) = mat ).
  Proof.
    intros.
    destruct iter as [n' p].
    apply funextfun. intros i.
    intros.
    induction n' as [| m IHn].
    - simpl.
      reflexivity.
    - assert (p'': m < S n). { apply (istransnatgth _ _ _ p (natgthsnn m) ). }
      assert (p''' : S m ≤ k). { apply (istransnatgeh _ _ _ p' (natgehsnn (S m) )  ). }
      set (IHn' := IHn p'' p''').
      rewrite <- IHn'.
      unfold gauss_clear_column_old.
      rewrite nat_rect_step.
      rewrite <- gauss_clear_column_step_eq.
      rewrite ( gauss_clear_column_step_inv4 ).
      2: { apply (istransnatgeh _ _ _  p''' (natgehsnn m) ).  }
      destruct (natgthorleh i m) as [i_gt_m | i_leq_m].
      + set (f := @gauss_clear_column_inv0').
        unfold gauss_clear_column_old in f.
        apply maponpaths_2.
        apply propproperty.
      + apply maponpaths_2.
        apply propproperty.
        (*rewrite gauss_clear_column_inv0.
        2 : {assumption. }
        rewrite (gauss_clear_column_inv0).
        2 : {assumption. }
        reflexivity.
        assumption.
        assumption.*)
  Defined.


  (* Expresses the property that a matrix is partially upper triangular -
     in the process of being contructed upp triangular, at iteration k.
     mat =
     [ 1 0 0 1
       0 1 1 1
       0 0 1 1
       0 0 1 1]  - fulfills  gauss_columns_cleared mat (1,, 1 < 4). *)
  Definition gauss_columns_cleared { n : nat } (mat : Matrix F n n)
             (k : ⟦ n ⟧%stn) := ∏ i j : ⟦ n ⟧%stn,
              (*k < i*) j < k -> j < i -> mat i j = 0%hq.

  Definition diagonal_filled { n : nat } (mat : Matrix F n n) :=
    ∏ i : ⟦ n ⟧%stn, mat i i != 0%hq.

  (* Shows that gauss_clear_column(_segment) retains previously zeroed entries, e.g. fulfills
     [ 1 0 0 1          [ X X X X
       0 1 1 1            0 X X X
       0 0 1 1    ->      0 0 X X
       0 0 1 1]           0 0 X X ]

     for k = 2  and where X is arbitrary (1/0) *)
  (* TODO currently broken - inv4' (prime) is used *)
  (* Lemma gauss_clear_column_inv4_____unused

  Admitted. *)


  Lemma gauss_clear_column_inv4'
        { n : nat }  (mat : Matrix F n n) ( k  : (⟦ n ⟧%stn)) (iter : ⟦ S n ⟧%stn)
        (entries_zeroed : gauss_columns_cleared mat k) (k' : ⟦ n ⟧%stn) (p' : (*k' > k*) k ≤ k') :
        (mat k' k' != 0%hq) -> (* TODO this one shouldn't be necessary ? *)
        gauss_columns_cleared (gauss_clear_column_old mat k' iter) k. (* A bit weird,
                                                                   don't we need mat k' k' != 0 in gcc??*)
  Proof.
    intros.
    destruct iter as [n' p].
    unfold gauss_columns_cleared in *.
    intros  i j.
    intros  i_gt_k j_lt_k.
    destruct (natgthorleh i ( n')) as [i_gt_n' | i_leq_n'].
    - rewrite gauss_clear_column_inv0'.
      + apply (entries_zeroed i j); assumption.
      + apply natgthtogeh. assumption.
    - destruct (natlehchoice i ( n')). {assumption. }
      2: { rewrite gauss_clear_column_inv0'.
           - apply entries_zeroed; assumption.
           - rewrite p0.
             apply isreflnatgeh.
      }
      rewrite gauss_clear_column_inv0.
      (* : {assumption. }*)
      2 : {assumption. } (* rewrite ! *)
      unfold gauss_clear_column_step'.
      destruct (natgthorleh i k').
      2 : {apply entries_zeroed; assumption. }
      unfold gauss_add_row.
      rewrite stn_neq_or_neq_refl.
      simpl.
      rewrite (entries_zeroed i j i_gt_k j_lt_k), (@riglunax1 F).
      replace (mat k' j) with 0%hq.
      2 : { rewrite entries_zeroed. try reflexivity; try assumption.
            assumption.
            apply (natlthlehtrans _ _ _ i_gt_k  p'   ). (* TODO variable naming *)
      }
      rewrite hqmultcomm.

      rewrite (@rigmult0x hq).
      apply idpath.

  Defined.

  (* Currently not working as we have not selected a non-zero pivot. *)

  (* Proving that previously zeroed columns remain zero *)
  Lemma gauss_clear_columns_up_to_inv0
        ( n : nat ) (mat : Matrix F n n) (* (p : diagonal_filled mat) *) (p' : n > 0)
        (iter : ⟦ S n ⟧%stn)  :
        ∏ i j : ⟦ n ⟧%stn,
        j < i ->  S iter ≤ j -> (* TODO replace all inequalities by this probably (or gth - standardize) *)
        mat i j = 0%hq -> (@gauss_clear_columns_up_to n p' iter mat) i j = 0%hq.
  Proof.
    intros i j j_lt_i siter_leh_j matij_ne0.
    unfold gauss_clear_columns_up_to.
    destruct iter as [iter p].
    induction iter.
    {admit. }
    rewrite nat_rect_step.
    destruct (select_pivot_row_easy'' _ _) in *.
  Abort.

  Lemma gauss_clear_columns_up_to_inv0
        ( n : nat ) (mat : Matrix F n n) (p' : n > 0)
        (iter : ⟦ S n ⟧%stn)  :
        ∏ i j : ⟦ n ⟧%stn,
        j < i ->  j < iter ->
        (@gauss_clear_columns_up_to n p' iter mat) i j = 0%hq.
  Proof.
    destruct iter as [n' lt_n'_n].
    induction n'.
    { intros i j i_gt_j sn'_leq_j.
      apply fromempty.
      apply (negnatgth0n _ sn'_leq_j).
    }
    unfold gauss_clear_columns_up_to.
    intros i j i_gt_j sn'_gt_j.
    rewrite nat_rect_step.
    destruct (select_pivot_row_easy'' _ _) as [? | none].
    2: { destruct (natlehchoice j n'). { apply natlthsntoleh; assumption. }
         - unfold gauss_clear_columns_up_to in IHn'.
           rewrite IHn'; try reflexivity; assumption.
         - assert (obv : n' < S n). { apply (istransnatlth _ _ _ (natgthsnn n') lt_n'_n). }
           rewrite <- (none i); try assumption.
           3 : {rewrite p in i_gt_j. apply natlthtoleh. assumption. }
           2 : {apply (pr2 i). }
           apply maponpaths.
           clear sn'_gt_j. clear none. revert lt_n'_n.
           rewrite <- p.
           intros.
           apply subtypePath_prop.
           reflexivity.
    }
    destruct (natlehchoice j n'). { apply natlthsntoleh; assumption. }
    2 : {  clear sn'_gt_j. revert t.  revert lt_n'_n.
           assert (p'' : n' < n). { rewrite <- p. apply (pr2 j). }
           intros lt_n'_n.
           assert (eq: j = (n',,lt_n'_n)).
           { revert p''.  revert lt_n'_n. rewrite <- p. intros.
             apply subtypePath_prop.
             reflexivity. }
           rewrite eq.
           intros.
           rewrite gauss_clear_column_inv1.
           - apply idpath.
           - unfold gauss_switch_row.
             rewrite (stn_neq_or_neq_refl).
             destruct (stn_eq_or_neq _ _).
             + rewrite coprod_rect_compute_1. apply t.
             +  rewrite coprod_rect_compute_2.
                rewrite coprod_rect_compute_1.
                apply t.
           - exact (pr2 i).
           - rewrite eq in i_gt_j; assumption.
    }
    rewrite (gauss_clear_column_inv4' _ (n',, lt_n'_n)); try reflexivity; try assumption.
    2 : {apply isreflnatleh. }
    - unfold gauss_clear_columns_up_to in IHn'.
      unfold gauss_columns_cleared.
      intros.
      unfold gauss_switch_row.
      destruct (stn_eq_or_neq _ _); rewrite IHn'.
      + rewrite coprod_rect_compute_1.
        destruct (stn_eq_or_neq _ _).
        { rewrite coprod_rect_compute_1; apply idpath. }
        rewrite coprod_rect_compute_2.
        rewrite IHn'; try assumption; apply idpath.
      + rewrite p in *. assumption. (*TODO variable naming *)
      + assumption.
      + destruct (stn_eq_or_neq _ _).
        { rewrite coprod_rect_compute_1; apply idpath. }
        do 2 rewrite coprod_rect_compute_2.
        rewrite IHn'; try apply idpath; try assumption.
      + apply (natgehgthtrans _ _ _   (pr1 (pr2 t)) X).
      + assumption.
    - unfold gauss_switch_row. (* TODO generalize this since it's repeated multiple times*)
      rewrite (stn_neq_or_neq_refl).
      destruct (stn_eq_or_neq _ _).
      + rewrite coprod_rect_compute_1. apply t.
      +  rewrite coprod_rect_compute_2.
         rewrite coprod_rect_compute_1.
         apply t.
  Defined.

  Lemma gauss_clear_columns_up_to_inv1
        ( n : nat ) (mat : Matrix F n n) (p' : n > 0)
        (iter : ⟦ S n ⟧%stn)  :
        ∏ i : ⟦ n ⟧%stn,
        iter ≤ i ->
        (@gauss_clear_columns_up_to n p' iter mat) i = mat i.
  Proof.
    destruct iter as [iter p].
    induction iter.
    - reflexivity.
    - intros i siter_leh_i.
      unfold gauss_clear_columns_up_to.
      rewrite nat_rect_step.
      unfold gauss_clear_columns_up_to in IHiter.
      destruct ( select_pivot_row_easy'').
      + assert (obv :  iter < i). {admit. }
        assert (obv' : iter ≤ i). {admit. }
        assert (obv'' : iter < S n). {admit. }
        rewrite <- (IHiter obv'').
        2: {admit. }
        set (f := gauss_clear_columns_up_to_inv0).
        (* rewrite gauss_clear_column_inv4'. *)
  Abort.

  Lemma gauss_clear_columns_up_to_inv2
        ( n : nat ) (mat : Matrix F n n) (p' : n > 0)
        (iter1 iter2 : ⟦ S n ⟧%stn)  :
        iter1 < iter2 ->
        ∏ k : ⟦ n ⟧%stn, k ≤ iter2 ->
        (@gauss_clear_columns_up_to n p' iter1 mat) k k = 0%hq
     -> (@gauss_clear_columns_up_to n p' iter2 mat) k k = 0%hq.

  Proof.
    intros iter1_leh_iter2 k k_leh_siter2.
    destruct iter1 as [iter1 p1].
    destruct iter2 as [iter2 p2].
    induction iter2.
    {admit. }
    intros H.
    unfold gauss_clear_columns_up_to in *.
    rewrite nat_rect_step.
  Abort.

  Lemma gauss_inv_upper_triangular {n : nat} (mat : Matrix F n n) (p : diagonal_filled mat):
    @is_upper_triangular F n n (gauss_clear_all_column_segments mat ).
  Proof.
    intros i j i_gt_j.
    unfold gauss_clear_all_column_segments.
    destruct (natchoice0 n) as [n0 | n_gt_0].
    { simpl. clear i_gt_j. generalize i. rewrite <- n0 in i. apply (fromstn0 i). }
    simpl.
    rewrite gauss_clear_columns_up_to_inv0.
    - reflexivity.
    - assumption.
    - exact (pr2 j).
  Defined.



  (* Updating vec/b "in place"  *)
  Definition back_sub_step { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    set ( m := pr1 i ).
    destruct (nat_eq_or_neq iter i).
    2 : {exact (vec i). }
    destruct (natlehchoice (S (pr1 iter)) n) as [? | ?]. {apply iter. }
    - exact (((vec i) * hqmultinv (mat i i)) - ((Σ (mat i ^ vec)  - (vec i)* (mat i i))  * (hqmultinv (mat i i) )))%hq.
    (* clamp_f should be called something like clear vec segment *)
    - exact ((hqmultinv (mat i i)) * (vec i))%hq.
  Defined.

  Definition back_sub_step' { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    set ( m := pr1 i ).
    induction (natlehchoice (S (pr1 iter)) n) as [? | ?].
    - exact ( (vec i) * (hqmultinv (mat i i)) - (Σ (mat i ^ vec)) * hqmultinv (mat i i))%hq.
    - exact ((vec i) * (hqmultinv (mat i i)))%hq.
    - unfold stn in i.
      apply (pr2 iter).
  Defined.



  Require Import UniMath.PAdics.lemmas.
  (* TODO moderately large cleanup needed with less ad-hoc naming throughout proof *)
  Lemma back_sub_step_solves_eq' { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix F n n) (b : Vector F n) (vec : Vector F n)
        (p: @is_upper_triangular F n n mat)
        (p' : diagonal_filled mat):
    (((mat ** (col_vec (back_sub_step iter mat vec))) iter  = (col_vec vec) iter )).
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
    generalize iter mat  vec p' p.
    set (itersucc := (stn_inhabited_implies_succ iter)).
    destruct itersucc as [pr1_ pr2_].
    rewrite pr2_ in *.
    intros iter' mat' vec' filled' is_upper_t'.
    apply funextfun. intros x.
    rewrite (@rigsum_dni F (pr1_)  _ iter').
    rewrite nat_neq_or_neq_refl.
    - destruct (natlehchoice (S (Preamble.pr1 iter')) (S pr1_)).
        etrans. { apply maponpaths_2; apply maponpaths; reflexivity. }
        unfold funcomp.
        etrans.
        { apply maponpaths_2.
          apply maponpaths.
          apply funextfun. intros q.
          rewrite (nat_eq_or_neq_right (dni_neq_i iter' q)).
          reflexivity.
        }
        rewrite (@rigsum_dni F ( pr1_)  _ iter').
        unfold funcomp, dni, di ; simpl.
        set (f := λ q : (⟦ pr1_ ⟧%stn), _).
        set (a := mat' iter' iter').
        set (b' := vec' iter').
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
        {apply maponpaths.
         apply map_on_two_paths.
         rewrite <- (@rigassoc2 hq).
         rewrite hqisrinvmultinv.
         2: {unfold a.
             apply  filled'. }
             apply (@riglunax2 hq).
             apply maponpaths.
             rewrite <- (@rigassoc2 hq).
             rewrite hqisrinvmultinv. 2: { apply filled'. }
             apply (@riglunax2 hq).
        }
        set (sum := iterop_fun _ _ _).
          assert (eq: (sum + b'*a - b'*a)%hq = sum ).
          { replace (sum + b' * a - b' * a)%hq with (sum + b' * a + (- b' * a))%hq.
            - rewrite hqplusassoc.
              replace (b' * a + - b' * a)%hq with (b' * a  - b' * a)%hq.
              + rewrite hqrminus; apply (@rigrunax1 hq).
              + symmetry.
                rewrite hqpluscomm.
                rewrite hqrminus.
                change (- b' * a)%hq with ((- b') * a)%hq.
                replace  (- b' * a)%hq with (- (b' *a))%hq.
                * rewrite (hqlminus (b' * a)%hq).
                  reflexivity.
                * rewrite  (@ringlmultminus hq).
                  reflexivity.
            - symmetry.
              rewrite hqpluscomm.
              change (- b' * a)%hq with ((- b') * a)%hq.
              replace  (- b' * a)%hq with (- (b' *a))%hq.
              * reflexivity.
              * rewrite  (@ringlmultminus hq).
                reflexivity.
          }
        etrans.
        { do 3 apply maponpaths.
          rewrite (@rigcomm2 hq).
          replace _ with (sum + b' * a - b' * a)%hq. { reflexivity. }
          reflexivity.
        }
        rewrite (@rigcomm1 F).
        rewrite (@rigassoc1 hq).
        etrans.
        { apply maponpaths. apply maponpaths_2. apply maponpaths.
          rewrite eq.
          reflexivity.
        }
        rewrite hqlminus.
        apply (@rigrunax1 hq).
        rewrite (@zero_function_sums_to_zero hq).
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
          apply invmaponpathsS in p0.
          apply fromempty.
          assert (q_ge_iter' : q ≥ (pr1 iter')).
          { apply h. }
          rewrite p0 in q_ge_iter'.
          apply natgehtonegnatlth in q_ge_iter'.
          assert (q_le_iter_absurd : q < pr1_).
          { apply (pr2 q). }
          exact (q_ge_iter' q_le_iter_absurd).
        }
        rewrite (@rigmult0x hq).
        reflexivity.
  Defined.


  (* Now, three fixpoint definitions for three subroutines.
     Partial pivoting on "A", defining b according to pivots on A,
     then back-substitution. *)

  (* Gauss_iterate takes matrix mat to reduce
                       a target vector b
                       a set of pivots   (a permutation of rows)
             and returns x  Satisfying mat ** x = b
             or a matrix with one or more empty columns   (TODO better approach upon failure ? assumes square mtx?)
             if the matrix is singular. *)
 (* Definition gauss_iterate
     { n : nat } (it : ⟦ n ⟧%stn)
     (mat : Matrix F n n) (b : Vector F n) (pivots : Vector (⟦ n ⟧%stn) n)
     (p : is_permutation_fun pivots)  (* TODO actually we should make pivots/permutations a Sigma type akin to stn. *)
    : (Matrix F n n) × (Vector (⟦ n ⟧%stn) n).
  Proof.
    revert mat pivots p.
    assert (p': pr1 it < n). { exact (pr2 it). }
    induction (pr1 it) as [ | m gauss_iterate_IH ]; intros mat pivots ?.
    { exact (mat,,pivots). }  (* TODO should we retain a permutation invariant here in the retun type ? *)
    assert (p'': m < n). { apply natlthtoleh in p'. apply natlehsntolth in p'. exact p'. }
    set (current_idx := make_stn n m p''). (* TODO remove that decrement_stn superflous function completely *)
    set (mat_vec_tup := ((gauss_step current_idx mat))).
    set (mat' := pr1 mat_vec_tup).
    set (piv  := (pr2 mat_vec_tup)).
    set (pivots' := transpose_permutation_fun pivots current_idx piv).
    set (isp' := permutation_fun_closed_under_tranpose ( (pivots))
                                                   p current_idx piv).
    exact (gauss_iterate_IH p'' mat' pivots' isp').
  Defined.*)

  (* roughly a duplicate of [clear_columns_up_to] above, but with pivot selection*)
  (* [gauss_iterate' iter mat pivots]:
  intention: clear columns [0 ≤ i < iter], selecting pivots correctly *)
  (* Definition gauss_iterate'
     { n : nat } (iter : ⟦ S n ⟧%stn)
     (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n)
     (* (p : is_permutation_fun pivots) *)  (* TODO actually we should make pivots/permutations a Sigma type akin to stn. *)
    : (Matrix F n n).
  Proof.
    destruct (natchoice0 n) as [? | gt]. { exact (mat). } (* TODO remove this later when gcc is S n*)
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - exact (mat).
    - assert (pr2_' : pr1_ < n). { apply pr2_. }
      assert (pr2_'' : pr1_ < S n).  { apply (istransnatlth _ _ _ (pr2_') (natgthsnn n)). }
      set (piv :=  select_pivot_row_easy mat ( pr1_,, pr2_' ) (n,, natgthsnn n)).
      destruct piv as [piv' | ?].
      2: { exact (IHpr1_ pr2_''). } (* TOOD is this right ? *)
      exact (( gauss_clear_column_old
             (gauss_switch_row ((IHpr1_ pr2_'') ) (pr1_,, pr2_') (piv'))
             (pr1_,, pr2_') (n,, natgthsnn n))).
  Defined. *)


  (* Definition gauss_iterate_as_matrix  { n : nat } (iter : ⟦ S n ⟧%stn)
     (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n) : (Matrix F n n).
  Proof.
  (*destruct (natchoice0 n) as [? | gt]. { exact (@identity_matrix hq n). } (* TODO remove this later when gcc is S n*)*)
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - exact (@identity_matrix hq n).
    - assert (pr2_' : pr1_ < n). { apply pr2_. }
      assert (pr2_'' : pr1_ < S n). { apply (istransnatlth _ _ _ (pr2_') (natgthsnn n)). }
      set (piv :=  select_pivot_row_easy mat ( pr1_,, pr2_' ) (n,, natgthsnn n)).
      destruct piv as [piv' | ?].
      2: {exact (@identity_matrix hq n ** ( (IHpr1_ pr2_''))). }
      set (mat_after_switch := (make_gauss_switch_row_matrix n (pr1_,, pr2_') piv' ** ( (IHpr1_ pr2_'')))).
      set (clear_column_mat := gauss_clear_column_as_left_matrix (n ,, natlthnsn n) mat_after_switch (pr1_,, pr2_')).
      exact (clear_column_mat ** mat_after_switch).
  Defined.

  Definition gauss_iterate_as_matrix_eq { n : nat } (iter : ⟦ S n ⟧%stn)
     (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n)
    : ((gauss_iterate' iter mat pivots)) = (gauss_iterate_as_matrix iter mat pivots ** mat).
  Proof.

    destruct (natchoice0 n) as [eq | gt].
    - simpl.
      unfold gauss_iterate', gauss_iterate_as_matrix.
      unfold identity_matrix.
      apply funextfun. intros i.
      apply fromempty. rewrite <- eq in i.
      apply (fromstn0); assumption.
    - apply funextfun. intros i.
      apply funextfun. intros j.
      destruct iter as [pr1_ pr2_].
      induction pr1_.
      + simpl. unfold gauss_iterate', gauss_iterate_as_matrix. simpl.
        destruct natchoice0; rewrite matlunax2; reflexivity.
      + unfold gauss_iterate', gauss_iterate_as_matrix.
        (*destruct (natchoice0 n). {rewrite matlunax2; reflexivity. } *)

        (*unfold gauss_iterate', gauss_iterate_as_matrix in IHpr1_.*)
        destruct (natchoice0 n). {admit. }
        do 2 rewrite nat_rect_step.
        destruct (select_pivot_row_easy mat (pr1_,, pr2_) (n,, natgthsnn n)).
        * (* rewrite gauss_clear_column_eq_matrix_def.*) (* Need this one first *)
          (* Here we want gauss_clear_column as left matrix = gauss_clear_column (prime, prime ? *)
  Abort. *)


  (* TODO do this one for clear_column (no prime ?) *)
  Lemma clear_column_eq_matrix_def { n : nat } (iter : ⟦ S n ⟧%stn)
        (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) :
    ((gauss_clear_column_as_left_matrix iter mat k) (*** mat *)) = (*gauss_clear_column''*) gauss_clear_column_old mat k iter.
  Proof.
    intros.
    (* rewrite <- gauss_clear_column_eq'. *)
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      unfold gauss_clear_column_as_left_matrix.
      simpl.
      (* rewrite matlunax2. *) (* TODO  - really bad we can't use Matrix.identity_matrix here! *)
      unfold gauss_clear_column''.
      simpl.
      reflexivity.
    - rename IHpr1_ into IHpr1_'.
      remember IHpr1_' as IHpr1_.
      unfold gauss_clear_column_old.
      unfold gauss_clear_column_old in IHpr1_'.
      unfold gauss_clear_column_as_left_matrix.
      unfold gauss_clear_column_as_left_matrix in IHpr1_'.
      rewrite nat_rect_step.
      rewrite nat_rect_step.
      rewrite <- gauss_clear_column_step_eq.
      destruct (natgthorleh pr1_ k).
      2: { rewrite matlunax2.
           rewrite IHpr1_'.
           induction pr1_.
           - simpl. apply idpath.
           - rewrite nat_rect_step.
             destruct (natgthorleh pr1_ k).
             + apply natgehsntogth in h.
               apply fromempty. apply (isasymmnatgth _ _  h h0).
             + rewrite <- gauss_clear_column_step_eq.
               set (x := gauss_clear_column_step _ _ _ _).
               rewrite gauss_clear_column_step_inv4.
               {apply idpath. }
               assumption.
      }
      rewrite <- IHpr1_'.
      set (x := nat_rect _ _ _ _).
      rewrite gauss_clear_column_step_eq.
      unfold gauss_clear_column_step'.
      destruct (natgthorleh _ _).
      2 : {apply fromempty. apply neggth_logeq_leh in h; assumption. }
      rewrite add_row_mat_elementary.
      2 : {apply issymm_natneq. apply natgthtoneq. assumption. }
      apply pathsinv0.
      etrans.
      { apply maponpaths.
        unfold x.
        set (x' := ((nat_rect _ _ _ ) pr1_ )).
        set (x'' := x' (istransnatlth pr1_ (S pr1_) (S n) (natlthnsn pr1_) pr2_)).
        replace (hqmultinv (x'' k k)%hq) with (hqmultinv (mat k k)%hq).
        - reflexivity.
        - rename IHpr1_ into IHpr1_''. clear HeqIHpr1_ IHpr1_' (*IHpr1_*).
          induction pr1_.
          {apply fromempty. apply  negnatgth0n in h0; assumption. }
          unfold x'', x'.
          rewrite nat_rect_step.
          destruct (natgthorleh pr1_ _).
          2 : {rewrite matlunax2.
               set (f := @gauss_clear_column_as_left_matrix_inv0 n ).
               unfold gauss_clear_column_as_left_matrix  in f.
               rewrite f .
               - reflexivity.
               - assumption.
          }
          set (f := @gauss_clear_column_as_left_matrix_inv0 n ).
          unfold gauss_clear_column_as_left_matrix  in f.
          rewrite add_row_mat_elementary.
          rewrite gauss_add_row_inv0.
          3: { apply issymm_natneq. apply natgthtoneq. assumption. }
          2: { apply natgthtoneq. assumption. }
          unfold gauss_clear_column_as_left_matrix in IHpr1_''.
          rewrite nat_rect_step in IHpr1_''.
          set (f' := @gauss_clear_column_as_left_matrix_inv1 n ).
          unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
          rewrite f'; try reflexivity.
          apply isreflnatgeh.
      }
      do 2 apply maponpaths.
      apply maponpaths_2.
      induction pr1_.
      + {apply fromempty. apply negnatgth0n in h0. assumption. }
      + unfold x.
        rewrite nat_rect_step.
        destruct (natgthorleh _ _).
        2: {rewrite matlunax2.
          set (f' := @gauss_clear_column_as_left_matrix_inv0 n ).
          unfold gauss_clear_column_as_left_matrix  in f'; try reflexivity.
          rewrite f'; try reflexivity.
          apply natlehnsn.
        }
        rewrite add_row_mat_elementary.
        2: {apply natgthtoneq in h1. apply issymm_natneq. assumption. }
        rewrite gauss_add_row_inv0.
        2: {apply issymm_natneq.
            apply natgthtoneq.
            apply natgthsnn. }
        unfold x in IHpr1_0.
        set (f := @gauss_clear_column_as_left_matrix_inv0 n ).
        unfold gauss_clear_column_as_left_matrix  in f.
        rewrite f.
        2: {apply natlehnsn.  }
        apply idpath.
  Defined.


  (*Lemma gauss_iterate_as_matrix_invertible  { n : nat } (iter : ⟦ S n ⟧%stn)
    (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n) : @matrix_inverse
    hq _ (@gauss_iterate_as_matrix  n  iter  mat pivots).
  Proof.
    unfold gauss_iterate_as_matrix.
    (* destruct (natchoice0 n). {apply identity_is_inv. } *)
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl; apply identity_matrix_is_inv.
    - rewrite nat_rect_step.
      destruct (select_pivot_row_easy mat (pr1_,, pr2_) (n,, natgthsnn n)).
      2 :
        {refine ( inv_matrix_prod_is_inv _ _ _ _).
         - apply identity_matrix_is_inv.
         - apply IHpr1_.
      }
      refine ( inv_matrix_prod_is_inv _ _ _ _).
      + apply clear_column_matrix_invertible.
        apply inv_matrix_prod_is_inv.
        apply switch_row_matrix_is_inv. {exact (mat s s). } (* TODO ?? *)
        apply IHpr1_.
      + refine (inv_matrix_prod_is_inv _ _ _ _).
        * set (todo := (@select_pivot_row_correct2 n)). (* TODO use this or similar *)
          refine ( switch_row_matrix_is_inv _ _ _).
          exact (mat s s). (* TODO Huh ? *)
        * apply IHpr1_.
  Defined.*)

  (* (* Deprecated. We want to prove this for  gauss_clear_columns_up_to. *)
  Lemma gauss_iterate_as_matrix_eq  { n : nat } (iter : ⟦ S n ⟧%stn)
    (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n) :
    (@gauss_iterate_as_matrix  n  iter  mat pivots) = ( (gauss_iterate' iter mat pivots)).
  Proof.
    intros.
    set (x := 1).
    unfold gauss_iterate_as_matrix, gauss_iterate'.
    destruct (natchoice0 n).
    { apply funextfun. intros i. apply fromempty. rewrite <- p in i. apply fromstn0; assumption. }
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl. admit. (*Wrong! identity_matrix = mat. What went wrong? *)
    - do 2 rewrite nat_rect_step.
      rewrite IHpr1_.
      destruct (select_pivot_row_easy mat (pr1_,, pr2_) (n,, natgthsnn n)).
      + rewrite clear_column_eq_matrix_def .
        rewrite switch_row_mat_elementary. (*TODO rename*)
        (*rewrite <- gauss_clear_column_eq.*)
        admit.
      + rewrite matlunax2.
        reflexivity.
  Admitted. *)


  Lemma gauss_clear_columns_up_to_as_matrix_eq  { n : nat } (iter : ⟦ S n ⟧%stn)
    (mat : Matrix F n n) (p : n > 0) :
    (@clear_columns_up_to_as_left_matrix _ p iter mat) = (gauss_clear_columns_up_to p iter mat).
  Proof.
    intros.
    unfold clear_columns_up_to_as_left_matrix, gauss_clear_columns_up_to.
    destruct iter as [iter p'].
    induction iter. {apply idpath. }
    do 2 rewrite nat_rect_step.
    repeat rewrite IHiter.
    set (inner_expr := nat_rect _ _ _ _).
    destruct (select_pivot_row_easy'' _ _) as [? | ?].
    - rewrite clear_column_eq_matrix_def.
      rewrite switch_row_mat_elementary.
      reflexivity.
    - rewrite matlunax2.
      reflexivity.
  Defined.

  (* TODO fix signature *)
  Definition back_sub' { n : nat } (iter : nat) (p : iter < n)  (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    induction iter as [ | m IHn] .
    - exact vec. (* TODO finish *)
    - assert (p' : S m < n). { assumption. }
      assert (p'' : m < n). {apply natlehsntolth.  apply natlthtoleh in p. assumption. }
      exact (back_sub_step (make_stn n (S m) p') mat (IHn p'')).
  Defined.
  Definition back_sub { n : nat } (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros.
    destruct (natchoice0 n) as [n_eq_0 | n_gt_0].
    - exact vec.
    - assert (p: n - 1 < n).  {apply (natminus1lthn n n_gt_0). }
      exact (back_sub' (n - 1) p mat vec).
  Defined.

  Definition gaussian_elimination {n : nat} (A : Matrix hq n n) (b : Vector hq n): Matrix hq n n × Vector hq n.
  Proof.
    destruct (natchoice0 n) as [? | p]. (* TODO resolve *)
    { exact (A,, b). }
    (* TODO equivalent row operations on b *)
    set (A' := (gauss_clear_columns_up_to p (n,, natgthsnn n) A )).
    set (x := back_sub A' b).
    exact (A',, x).
  Defined.

  (* The full procedure returns A' s.t. A' upper triangular
     TODO assert A ' = (invertible matrix) ** A       *)
  Lemma gaussian_elimination_inv0 {n : nat} (A : Matrix hq n n) (b : Vector hq n)
    : @is_upper_triangular hq n n (((pr1 (gaussian_elimination A b)))).
  Proof.
  unfold is_upper_triangular,  gaussian_elimination.
  destruct (natchoice0 n) as [p | ?].
  - intros.
    apply fromempty.
    set (contr := stn_implies_ngt0 i).
    rewrite p in contr.
    apply isirreflnatgth in contr.
    assumption.
  - intros i j.
    intros j_lt_i.
    apply gauss_clear_columns_up_to_inv0.
    + assumption.
    + apply (pr2 j).
  Defined.

  (* The full procedure returns A', x s..t A' ** x = b   or a witness to A being not invertible. *)
  Lemma gaussian_elimination_inv1 {n : nat} (A : Matrix hq n n) (b : Vector hq n)
    : (@matrix_inverse hq n A) ->
      ((pr1 (gaussian_elimination A b)) ** (col_vec (pr2 (gaussian_elimination A b)))) = (col_vec b).
  Proof.

  Abort.

  (* Alternative : coprod (((pr1 (gaussian_elimination A b)) ** (col_vec (pr2 (gaussian_elimination A b)))) = (col_vec b)) (¬ (@matrix_inverse hq n A)). *)

End Gauss.



Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.
  Local Notation Σ := (iterop_fun 0%hz op1).


  Local Notation "A ** B" := (@matrix_mult hz _ _ A _ B) (at level 80).

  Definition mat_to_square_mat { m n : nat } (mat : Matrix I m n) : Matrix I (min m n) (min m n).
  Proof.
    intros.
    (* exact (λ i j : ⟦min m n⟧%stn, mat (minabstn_to_astn i) (minabstn_to_bstn j)). *)
  Abort.

  (* Such code might go intro Matrix.v *)
  Definition is_smithnf { m n : nat } (A : Matrix I m n) :
    ∑ (S : Matrix I m m), ∑ (T : Matrix I n n),
    @is_diagonal I m n (S ** A ** T) ×
    ∏ (i j : ⟦ min n m ⟧%stn), i < j ->
    hzdiv (A (minabstn_to_bstn i) (minabstn_to_astn i))
    (A (minabstn_to_bstn j) (minabstn_to_astn i)).
  Abort.

  Definition MinAij {m n : nat} (A : Matrix I m n) (s : nat) (p : s < min m n) : I.
  Proof.
  Abort.


End SmithNF.


Section SmithNFOps.

  (*   *)

End SmithNFOps.


Section SmithNFAlgs.


End SmithNFAlgs.
