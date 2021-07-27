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
Context { R : rig }.
Local Definition F := hq.
Opaque F.

(* The first few sections contain Definitions and Lemmas that
   should be moved further up the project tree *)

Local Notation "A ** B" := (matrix_mult A B) (at level 80).
Local Notation  Σ := (iterop_fun 0%hq op1).
Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).


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



End PrelStn.


Section Vectors.

  Context { R : rig }.

  Local Notation  Σ := (iterop_fun rigunel1 op1).

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




(* TODO: possibly write special case [v ∧ (pulse j a) = a * (v j)]. *)

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

  (* TODO: upstream - Vector equivalent of drop_el for "vecs"? *)
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
  Lemma minussn1 ( n : nat ) : ( S n ) - 1 ≥ n.
  Proof.
    intros. destruct n. apply idpath.
    assert (e : (S (S n)) > (S n)).
    { apply natgthsnn. }
    apply natgthtogehm1 in e. assumption.
  Defined.


  (* TODO : This proof is a shambles ! And should be covered by inhabited lemma above. Just remove? *)
  Definition drop_idx_vector { n : nat } ( i : ⟦ S n ⟧%stn ) ( drop : ⟦ S n ⟧%stn ) (p : n > 0) :
    ⟦ n ⟧%stn.
  Proof.
    intros.
    induction (natlthorgeh i drop) as [i_le_drop | i_geq_drop].
    - assert (e: drop ≤ n).
      { apply (pr2 drop). }
      assert (e': i < n). {
        apply (natlthlehtrans i drop (n) ).
        + assumption.
        + assumption. }
      exact (pr1 i,, e').
    -
      assert (e: (pr1 i) < S n). {exact (pr2 i). }
      assert ((pr1 i) - 1 < n). {
      apply natltminus1 in e.
      change (S n) with (1 + n) in e.
      replace (1 + n - 1) with (n + 1 - 1) in e.
      2: { rewrite plusminusnmm. rewrite natpluscomm.
           rewrite plusminusnmm. reflexivity.
      }
      rewrite plusminusnmm in e.
      assert ( e': (pr1 i < n + 1)).
      { intros.
        apply natlehtolthsn  in e.
        rewrite natpluscomm.
        change (1 + n) with (S n).
        assumption.
      }

      induction (natlthorgeh (pr1 i) n) as [i_le_n | i_geq_n].
      + apply natlthtolthm1 in i_le_n. assumption.
      +
      - apply natlthp1toleh  in e'.
        apply (isantisymmnatgeh) in e'.
        2 : {assumption. }
        symmetry in e'.
        rewrite e'.
        rewrite <- e'.
        apply natminuslthn.
        { assumption. }
        reflexivity.
      }
      exact (i - 1,, X).
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

  (* TODO Is that eq or weq? *)
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

    (* factored approach:
       lemma that ∑ (v1 ^ v2) = ∑ v1 + ∑ v2
       lemma for ∑ (a ^ v) = a * ∑ v
       lemma that ∑ (standard_basis_vector n i) = 1
     (where (standard_basis_vector n i) = (identity_matrix i)) *)
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

    (* Is n ≥ 1 necessary ? *)
  Definition vector_n_to_vector_snm1 { n : nat } (v : Vector R n) (p : n ≥ 1) : (Vector R (S ( n - 1 ))).
  Proof.
    unfold Vector in v.
    unfold Vector.
    change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
    rewrite minusplusnmm. 2 : {exact p. }
    exact v.
  Defined.

End Vectors.

Section Matrices.

  Context {R : rig}.
  Local Notation Σ := (iterop_fun rigunel1 op1).

  (* Hmm ... *)
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

  Lemma issymm_stnneq (A : UU) {n : nat} (i j : ⟦ n ⟧%stn) :
    (i ≠ j) -> (j ≠ i).
  Proof.
    intros i_neq_j.
  Abort.

  (* Should we call al these is_symmetric? *)
  Definition symmetric_matrix {X : UU} {n : nat} (mat : Matrix X n n) := mat = transpose mat.

  Lemma identity_matrix_symmetric  {n : nat} : @symmetric_matrix R n (identity_matrix ).
  Proof.
    unfold symmetric_matrix.
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

  (* TODO find a better name *)
  Lemma symmetric_rows_eq_cols {X : UU} {n : nat} (mat : Matrix X n n) (i : ⟦ n ⟧%stn) :
    symmetric_matrix mat -> row mat i = col mat i.
  Proof.
    intros issymm_mat. unfold col.
    rewrite <- issymm_mat. apply idpath.
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

  Lemma identity_matrix_i_i {n : nat} (i : ⟦ n ⟧%stn) : (@identity_matrix R n) i i = rigunel2.
  Proof.
    unfold identity_matrix.
    rewrite (stn_neq_or_neq_refl); simpl; apply idpath.
  Defined.

  Lemma identity_matrix_i_j {n : nat} (i j : ⟦ n ⟧%stn) : i ≠ j -> (@identity_matrix R n) i j = rigunel1.
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
    rewrite <- (symmetric_rows_eq_cols _ _ identity_matrix_symmetric); (* Non-descript name ?*)
    unfold pointwise, row.
    - rewrite identity_matrix_i_i, rigrunax2.
      apply idpath.
    - intros k j_neq_k.
      rewrite (identity_matrix_i_j _ _ j_neq_k), rigmultx0.
      apply idpath.
  Defined.

  (* TODO move identity matrices, vectors lemmas to appropriate sections *)
  Lemma idrow_sums_to_1 { n : nat } (i : ⟦ n ⟧%stn) :
    Σ ((@identity_matrix R n ) i) = 1%rig.
  Proof.
    rewrite (pulse_function_sums_to_point_rig'' _ (stn_implies_ngt0 i) i). (*TODO less versions of this, remove rig in name *)
    - unfold identity_matrix.
      rewrite stn_neq_or_neq_refl, coprod_rect_compute_1.
      apply idpath.
    - unfold identity_matrix.
      intros ? i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      apply idpath.
  Defined.

  (* Should be renamed isinvertible_matrix or something close to that *)
  Definition matrix_is_invertible {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix) × ((B ** A) = identity_matrix).

  (* TODO: name as e.g. [matrix_right_inverse] since gives choice of inverse? and similar vice versa below. *)
  Definition matrix_is_invertible_left {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((A ** B) = identity_matrix).

  Definition matrix_is_invertible_right {n : nat} (A : Matrix R n n) :=
    ∑ (B : Matrix R n n), ((B ** A) = identity_matrix).


  (* The product of two invertible matrices being invertible *)
  Lemma inv_matrix_prod_is_inv {n : nat} (A : Matrix R n n)
    (A' : Matrix R n n) (pa : matrix_is_invertible A) (pb : matrix_is_invertible A') :
    (matrix_is_invertible (A ** A')).
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

  (* Perhaps also prove that the product of n invertible matrices is invertible *)

  Lemma identity_is_inv { n : nat } : matrix_is_invertible (@identity_matrix _ n).
  Proof.
    unfold matrix_is_invertible.
    use tpair. { exact identity_matrix. }
    use tpair; apply matrunax2.
  Defined.


  Definition is_diagonal { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn) (j : ⟦ n ⟧%stn), (stntonat _ i ≠ (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_upper_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ),  (stntonat _ i > (stntonat _ j)) -> (mat i j) = 0%rig.

  Definition is_lower_triangular { m n : nat } (mat : Matrix R m n) :=
    ∏ (i : ⟦ m ⟧%stn ) (j : ⟦ n ⟧%stn ), (stntonat _ i < (stntonat _ j)) -> (mat i j) = 0%rig.

End Matrices.


Section MatricesF.

  Context { R : rig }.

  (* Not really a clamp but setting every element at low indices to zero.
     TODO Also should not be necessary with sensible selection of pivots *)
  Definition clamp_f {n : nat} (f : ⟦ n ⟧%stn -> hq) (cutoff : ⟦ n ⟧%stn) : (⟦ n ⟧%stn -> hq).
    intros i.
    induction (natlthorgeh i cutoff) as [LT | GTH].
    - exact 0%hq.
    - exact (f i).
  Defined.


  Definition zero_vector_hq (n : nat) : ⟦ n ⟧%stn -> hq :=
    λ i : ⟦ n ⟧%stn, 0%hq.

  Definition zero_vector_nat (n : nat) : ⟦ n ⟧%stn -> nat :=
    λ i : ⟦ n ⟧%stn, 0%nat.

  (* TODO not really a zero vector is it? *)
  Definition zero_vector_stn (n : nat) : ⟦ n ⟧%stn -> ⟦ n ⟧%stn.
  Proof.
    intros i.
    assumption.
  Defined.

  Lemma stn_eq_nat_eq { n : nat} (i j : ⟦ n ⟧%stn) : i = j <-> (pr1 i = pr1 j).
  Proof.
  Abort.

  Lemma stn_neq_nat_neq { n : nat} (i j : ⟦ n ⟧%stn) : i ≠ j <-> (pr1 i ≠ pr1 j).
  Proof.
  Abort.

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

  Definition tranposition_mat_rows_perm {X : UU} {m n : nat} (i j : ⟦ m ⟧%stn)
    : (Matrix X m n) ≃ Matrix X m n.
  Proof.
    (* This is just the switch_rows proof *)
  Abort.

    (* Defining permutations as stn -> stn . TODO What are the existing
     definitions for permutations ? *)

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


End MatricesF.


Section Unsorted.

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

  (* We can generalize this to a larger number of relations than magnitude over rationals... *)
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

  (* What is the canonical lemma for this ? *)
  Lemma natgt0_inhabited_implies_succ {n:nat} (p : n > 0)
    : ∑ m, n = S m.
  Proof.
    destruct n as [ | m].
    - contradiction (negnatgth0n 0 p).
    - use tpair.
      + exact m.
      + simpl.
        reflexivity.
  Defined.

  (* Definition foldleft_step {E} (e : E) (m : binop E) {n : nat} (x: (⟦ S n ⟧)%stn -> E) : ((⟦ n ⟧)%stn → E) → E.
  Proof.
    set(foldl := @foldleft E e m (S n)).
    (* unfold foldleft in foldl. *)
    destruct (natchoice0 n).
    - admit. (* ? *)
    - unfold foldleft in foldl. set (test := natgt0_inhabited_implies_succ h).
      destruct test.
      rewrite pr2 in *. *)

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
    (ei ei' : hq × (⟦ n ⟧%stn)): pr2 (max_hq_index_bounded k f ei ei') >= k.
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

  (* TODO at least rename
     it's in general not true if n = 0 (that's why we have k )*)
  Lemma some_lemma (m n : nat) (k : ⟦ n ⟧%stn) : n - 1 - m < n.
  Proof.
    { assert (p' : n - 1 < n).
      { apply natminuslthn.
        - destruct n.
          + destruct (weqstn0toempty k).
          + apply natgthsn0.
        - reflexivity.
      }
      destruct m.
      - rewrite minus0r. assumption.
      - apply (natlehlthtrans (n - 1 - S m) (n - 1) n ).
        + apply natminuslehn.
        + assumption.
    }
  Defined.

  (* ( i,, i < n) to (i-1,, i-1 < n *)
  (*
  Definition decrement_stn { n : nat } ( i : (⟦ n ⟧)%stn ) : ⟦ n ⟧%stn. (* (⟦ n ⟧)%stn.*)
  Proof.
    induction (natgtb (pr1 i) 0).
    (*- assert ( p : ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }*)
    - assert ( p :  ((pr1 i) - 1) < n). {  unfold stn in i. apply natlthtolthm1. apply i.  }
      exact ((pr1 i) - 1,, p).
    - exact i.
  Defined. *)


  Definition switch_vector_els { n : nat } (vec : Vector F n) (e1 e2 : ⟦ n ⟧%stn) : Vector F n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i e1).
    - exact (vec e2).
    - induction (stn_eq_or_neq i e2).
      + exact (vec e1).
      + exact (vec i).
  Defined.
End Unsorted.


Section Gauss.
  (* Gaussian elimination over the field of rationals *)

  (* TODO better (or any) comments for all these functions including assumptions*)

  (* TODO Carot operator is used similarly throughout the document, move out *)
  Local Notation Σ := (iterop_fun 0%hq op1).
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).

  Context { R : rig }.
  (* Gaussian elimination over the field of rationals *)


  Definition gauss_add_row { m n : nat } ( mat : Matrix F m n )
    ( r1 r2 : ⟦ m ⟧%stn )  ( s : F ) : ( Matrix F m n ).
  Proof.
    intros i j.
    induction (stn_eq_or_neq i r2).
    - exact ( op1 ( mat r2 j )  ( op2 s ( mat r1 j ))).
    - exact ( mat i j ).
  Defined.

  (* Is stating this as a Lemma more in the style of other UniMath work?*)
  Local Definition identity_matrix { n : nat } : ( Matrix F n n ).
  Proof.
    apply ( @identity_matrix hq ).
  Defined.


  (* Need again to restate several definitions to use the identity on rationals*)
  (*Local Notation Σ := (iterop_fun 0%hq op1).*)(*
  Local Notation "R1 ^ R2" := ((pointwise _ op2) R1 R2).*)

  (* TODO: replace with upstream version?
     Upstream has a slightly annoying order of arguments -
     provide an alternative in Matrix.v ? *)
  Local Definition matrix_mult {m n : nat} (mat1 : Matrix F m n)
    {p : nat} (mat2 : Matrix F n p) : (Matrix F m p) :=
    λ i j, Σ ((row mat1 i) ^ (col mat2 j)).

  (* (* TODO We should also consider the following alternative *)
  Definition matrix_mult' {m n : nat} (mat1 : Matrix F m n)
    {p : nat} (mat2 : Matrix F n p) : (Matrix F m p) :=
    λ i j, Σ (λ k, (mat1 i k * mat2 k j))%hq.

  Lemma matrix_mult_eq_unfolded_mult  {m n : nat} (mat1 : Matrix F m n)
        {p : nat} (mat2 : Matrix F n p) :
    matrix_mult mat1 mat2 = matrix_mult' mat1 mat2.
  Proof.
    apply idpath.
  Defined. *)

  Local Notation "A ** B" := (matrix_mult A B) (at level 80).

  Definition add_row_op { n : nat } (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧ %stn) (s : F) : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (mat r1) (mat r2)).
    - exact (mat i).
  Defined.

  (* Which by left multiplication corresponds to adding r1 to r2 *)
  (* TODO might want to induct on r1 = r2, that case is off-by-one by this formulation.
     (However is not used in any of the eliminations) *)
  Definition make_add_row_matrix { n : nat } (r1 r2 : ⟦ n ⟧%stn) (s : F)  : Matrix F n n.
  Proof.
    intros i.
    induction (stn_eq_or_neq i r2).
    - exact (pointwise n op1 (identity_matrix i) (const_vec s ^ identity_matrix r1)).
    - exact (identity_matrix i).
  Defined.

  Definition add_row_by_matmul { n m : nat } ( r1 r2 : ⟦ m ⟧%stn ) (mat : Matrix F m n) (s : F) : Matrix F m n :=
    @Matrix.matrix_mult hq m m (make_add_row_matrix r1 r2 s ) n mat.

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
    intros i j.
    induction (stn_eq_or_neq i j).
      - induction (stn_eq_or_neq i r).
        + exact s.
        + exact 1%hq.
      - exact 0%hq.
  Defined.

  (*   *)
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

  (* Invariant stating that switching rows only affects 2 rows.
     Helpful for later invariants on columns remaining cleared after
     various transformations.  *)
  Lemma gauss_switch_row_inv0 {m n : nat} (mat : Matrix hq n n)
        (r1 : ⟦ n ⟧%stn) (r2 : ⟦ n ⟧%stn) : ∏ (i : ⟦ n ⟧%stn), i ≠ r1 -> i ≠ r2
      -> (gauss_switch_row mat r1 r2 ) i =  mat i.
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

  Lemma id_mat_ii {n : nat} (i : ⟦ n ⟧%stn) : identity_matrix i i = 1%hq.
  Proof.
    unfold identity_matrix, Matrix.identity_matrix.
    rewrite stn_neq_or_neq_refl.
    simpl.
    reflexivity.
  Defined.

  Lemma id_mat_ij {n : nat} (i j: ⟦ n ⟧%stn) (i_neq_j : i ≠ j) : identity_matrix i j = 0%hq.
  Proof.
    unfold identity_matrix, Matrix.identity_matrix.
    rewrite (stn_eq_or_neq_right i_neq_j).
    simpl.
    reflexivity.
  Defined.


  (* The following three lemmata test the equivalence of multiplication by elementary matrices
     to swaps of indices. *)
  Lemma scalar_mult_mat_elementary {n : nat} (mat : Matrix F n n) (s : F) (r : ⟦ n ⟧%stn) :
    ((make_scalar_mult_row_matrix s r) ** mat) = gauss_scalar_mult_row mat s r.
  Proof.
    use funextfun. intros i.
    use funextfun. intros ?.
    unfold make_scalar_mult_row_matrix. unfold gauss_scalar_mult_row.
    unfold "**". unfold "^". unfold col. unfold transpose. unfold row. unfold flip.
    unfold identity_matrix.
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


  (* TODO prove over rigs *)
  Lemma id_pointwise_prod { n : nat } (v : Vector F n) (i : ⟦ n ⟧%stn) :
    (identity_matrix  i) ^ v = (@scalar_lmult_vec F (v i) n (identity_matrix i)).
  Proof.
    unfold "^", pointwise.
    unfold identity_matrix, const_vec, Matrix.identity_matrix.
    unfold scalar_lmult_vec, const_vec, "^".
    apply funextfun. intros k.
    destruct (stn_eq_or_neq i k) as [eq | neq].
    - simpl.
      rewrite (@riglunax2 F).
      rewrite (@rigrunax2 F).
      rewrite eq. (* TODO p ? *)
      reflexivity.
    - simpl.
      rewrite (@rigmultx0 F).
      rewrite (@rigmult0x F).
      apply idpath.
  Defined.

  Lemma sum_id_pointwise_prod { n : nat } (v : Vector F n) (i : ⟦ n ⟧%stn) :
    Σ ((identity_matrix i) ^ v) =  (v i).
  Proof.
    unfold identity_matrix, "^", Matrix.identity_matrix.
    assert (p: n > 0). {apply (stn_implies_ngt0 i). } (*TODO this should be gt0 *)
    rewrite (@pulse_function_sums_to_point_rig'' F n _ p i).
    - rewrite stn_neq_or_neq_refl.
      simpl.
      apply (@riglunax2 F).
    - intros j i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_j).
      simpl.
      apply (@rigmult0x F).
  Defined.

  (* TODO should this really be necessary *)
  Lemma sum_id_pointwise_prod_unf { n : nat } (v : Vector F n) (i : ⟦ n ⟧%stn) :
    Σ (λ j : ⟦ n ⟧%stn, (identity_matrix i j) * (v j))%rig =  (v i).
  Proof.
    apply sum_id_pointwise_prod.
  Defined.

  Lemma switch_row_mat_elementary { n : nat } (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧%stn) :
    ((make_gauss_switch_row_matrix n r1 r2) ** mat)  = gauss_switch_row mat r1 r2.
  Proof.
    unfold "**".
    unfold "^", col, row, transpose, flip.
    unfold make_gauss_switch_row_matrix, gauss_switch_row.
    apply funextfun. intros i.
    apply funextfun. intros ?.
    assert (p: n > 0).  { apply ( stn_implies_ngt0 r1).  }
    destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1].
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F n (λ i : (⟦ n ⟧%stn), identity_matrix r2 i * _)%ring p r2).
      + unfold identity_matrix, Matrix.identity_matrix.
        rewrite stn_neq_or_neq_refl.
        simpl.
        apply (@riglunax2 F).
      + intros k r2_neq_k.
        rewrite (id_mat_ij r2 k r2_neq_k).
        apply (@rigmult0x F).
    - simpl.
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2].
      + simpl.
        destruct (stn_eq_or_neq i r1) as [? | ?].
        * rewrite sum_id_pointwise_prod_unf.
          apply idpath.
        * rewrite sum_id_pointwise_prod_unf.
          apply idpath.
      + simpl.
        rewrite sum_id_pointwise_prod_unf.
        apply idpath.
  Defined.


  (* TODO fix mixed up signatures on add_row  / make_add_row_matrix *)
  Lemma add_row_mat_elementary { n : nat } (mat : Matrix F n n) (r1 r2 : ⟦ n ⟧%stn) (p : r1 ≠ r2) (s : F) :
    ((make_add_row_matrix  r1 r2 s) ** mat)  = (gauss_add_row mat r1 r2 s).
  Proof.
    intros.
    unfold make_add_row_matrix, gauss_add_row.
    unfold "**", "^", row, col, transpose, flip.
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
        rewrite (@pulse_function_sums_to_point_rig'' F n (λ i : (⟦ n ⟧%stn), identity_matrix k i * _)%ring p' k).
        * rewrite k_eq_r1 in *.
          rewrite id_mat_ii.
          rewrite (@riglunax2 F).
          apply idpath.
        * intros j k_neq_j.
          rewrite (id_mat_ij k j k_neq_j).
          apply (@rigmult0x F).
    - destruct (stn_eq_or_neq k r2) as [k_eq_r2 | k_neq_r2].
      + simpl.
        rewrite (@two_pulse_function_sums_to_point_rig F n (λ i : ( ⟦ n ⟧%stn), ((identity_matrix  _ _ + _ * _) * _ ))%rig p' k r1).
        * unfold const_vec, identity_matrix, Matrix.identity_matrix. (* TODO *)
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
          unfold identity_matrix, Matrix.identity_matrix. (* TODO *)
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
        rewrite sum_id_pointwise_prod_unf.
        apply idpath.
  Defined.

  (* TODO move to appropriate sections *)
  Lemma weqvec_rowvec
    : ∏ X : UU, ∏ n : nat,  Vector X n ≃ Matrix X 1 n.
  Proof.
    intros.
    apply weq_vector_1.
  Defined.

  Lemma weqvec_colwec
    : ∏ X : UU, ∏ n : nat,  weq (Vector X n) (Matrix X n 1).
  Proof.
    intros.
    apply weqffun.
    apply weq_vector_1.
  Defined.


  (* TODO : F should also be a general field, not short-hand for rationals specifically.
            This does not mandate any real change in any proofs ?*)
  Lemma scalar_mult_matrix_is_inv { n : nat } ( i : ⟦ n ⟧%stn ) ( s : F ) ( ne : hqneq s 0%hq ) :
    @matrix_is_invertible F n (make_scalar_mult_row_matrix s i ).
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
        unfold Matrix.matrix_mult.
        unfold row. unfold col. unfold transpose. unfold "^". unfold flip.
        unfold Matrix.identity_matrix.
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


  Lemma add_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) (r1_neq_r2 : r1 ≠ r2) ( s : F ) (p : (s != 0)%hq)
    (p' : n > 0):
    @matrix_is_invertible F n (make_add_row_matrix r1 r2 s ).
  Proof.
    unfold matrix_is_invertible.
    unfold make_add_row_matrix.
    use tpair.
    {
      induction (stn_eq_or_neq r1 r2) as [? | ?].
      - exact (make_add_row_matrix r1 r2 (hqmultinv s)).
      - exact (make_add_row_matrix r1 r2 (- s)%hq).
    }
    unfold make_add_row_matrix, identity_matrix, Matrix.identity_matrix.
    unfold matrix_mult, Matrix.matrix_mult, col, "^", transpose, flip, row.
    use tpair.
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
          -- simpl.
             repeat rewrite stn_neq_or_neq_refl.
             simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2).
             simpl.
             rewrite k_eq_l in *.
             rewrite k_eq_r2 in *.
             rewrite (stn_eq_or_neq_right r1_neq_r2').
             simpl.
             repeat rewrite (@rigmultx0 F).
             repeat rewrite (@rigrunax1 F).
             rewrite (@riglunax2 F).
             repeat rewrite stn_neq_or_neq_refl; simpl.
             rewrite stn_neq_or_neq_refl; simpl.
             rewrite (stn_eq_or_neq_right r1_neq_r2').
             simpl.
             rewrite (@rigmultx0 F).
             apply (@rigrunax1 F).
          -- rewrite k_eq_r2.
             apply issymm_natneq in r1_neq_r2'.
             assumption.
          -- intros q q_neq_k q_neq_r1.
             rewrite k_eq_r2, k_eq_l in *.
             simpl.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             rewrite (stn_eq_or_neq_right q_neq_k); simpl.
             apply issymm_natneq in q_neq_k. (* TODO this is repeated quite often... *)
             rewrite (stn_eq_or_neq_right q_neq_k).
             simpl.
             apply issymm_natneq in q_neq_r1.
             rewrite (stn_eq_or_neq_right q_neq_r1).
             simpl.
             rewrite (@rigmultx0 F).
             apply idpath.
        *  rewrite (@two_pulse_function_sums_to_point_rig F n _ p' k r1).
           -- simpl.
              rewrite (stn_eq_or_neq_right r1_neq_r2); simpl.
              rewrite stn_neq_or_neq_refl. simpl.
              rewrite k_eq_r2 in *.
              simpl.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              simpl.
              rewrite stn_neq_or_neq_refl.
              simpl.
              rewrite (stn_eq_or_neq_right k_neq_l).
              simpl.
              repeat rewrite (@rigmultx0 F).
              rewrite (@rigrunax1 F).
              rewrite (@riglunax2 F).

              rewrite (@riglunax1 F).
              unfold const_vec.
              rewrite stn_neq_or_neq_refl.
              simpl.
              apply issymm_natneq in r1_neq_r2'.
              rewrite (stn_eq_or_neq_right r1_neq_r2').
              simpl.
              destruct (stn_eq_or_neq r1 l) as [r1_eq_l | r1_neq_l].
              ++ simpl.
                 do 3 rewrite (@rigrunax2 F).
                 rewrite (hqpluscomm _ s) . (* Only place we mention hq ? TODO don't? *)
                 rewrite hqplusr0.
                 rewrite hqlminus.
                 apply idpath.
              ++ simpl.
                 repeat rewrite (@rigmultx0 F).
                 rewrite (@rigrunax1 F).
                 apply idpath.
           -- rewrite k_eq_r2.
              apply issymm_natneq.
              assumption.
           -- intros q q_neq_k q_neq_r1.
              simpl.
              rewrite k_eq_r2 in *.
              simpl.
              apply issymm_natneq in q_neq_k.
              rewrite (stn_eq_or_neq_right q_neq_k).
              simpl.
              unfold const_vec.
              apply issymm_natneq in q_neq_r1.
              rewrite (stn_eq_or_neq_right q_neq_r1).
              simpl.
              rewrite (@riglunax1 F).
              rewrite (@rigmultx0 F).
              rewrite (@rigmult0x F).
              apply idpath.
        * rewrite k_eq_l in *.
          simpl.
          set (cl := setquot _ ).
          (* This is not the target row! *)

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
    - simpl.
  Admitted. (* Second part, this is all very verbose. Could we do it concisely ? *)

  Lemma switch_row_matrix_is_inv { n : nat } ( r1 r2 : ⟦ n ⟧%stn ) ( s : F ) ( ne : hqneq s 0%hq ) :
    @matrix_is_invertible F n (make_gauss_switch_row_matrix n r1 r2).
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
    - unfold make_gauss_switch_row_matrix, identity_matrix, Matrix.identity_matrix.
      unfold matrix_mult, Matrix.matrix_mult, row, col, "^", transpose, flip.
      apply funextfun. intros i.
      apply funextfun. intros j.
      destruct (stn_eq_or_neq i r1) as [i_eq_r1 | i_neq_r1];
      destruct (stn_eq_or_neq i r2) as [i_eq_r2 | i_neq_r2];
      destruct (stn_eq_or_neq i j) as [i_eq_j | i_neq_j].
      (* some cases should be impossible, so shouldn’t need algebra? *)
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
      +
        do 2 rewrite cpl.

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

  (* TODO this should be used in place of the manual proof at many places ? *)
  Lemma natminus1lthn (n : nat) : n > 0 -> n - 1 < n.
  Proof.
    intros n_gt_0.
    apply natminuslthn.      (* TODO as usual, refactor *)
    - assumption.
    - reflexivity.
  Defined.

  (* TODO: make R paramater/local section variable so that this can be stated *)

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



  (* Is it sufficient to prove this point, we might not need to verify the index corresponds to
     the maximum value ? *)
  (* We ultimately don't want rigs but a set with a decrel *)
  (* ~ point of interest ~. How do we prove properties over folds ? *)

  Lemma max_argmax_stnhq_bounded_ne_0  { n : nat } (vec : Vector F n) (pn : n > 0 ) (i k : ⟦ n ⟧%stn) : vec i != 0%hq -> pr1 (max_argmax_stnhq_bounded vec pn k) != 0%hq.
  Proof.
    intros vec_i_ne_0.
    unfold max_argmax_stnhq_bounded.
    unfold foldleft.
    induction n.
    - apply fromstn0; assumption. (* fromstn0 *)
    -
  Abort.


  Definition max_argmax_stnhq_bounded_geq_k  { n : nat } (vec : Vector F n) (pn : n > 0 ) (k : ⟦ n ⟧%stn) : pr2 (max_argmax_stnhq_bounded vec pn k) ≥ k.
  Proof.
    intros.
    unfold max_argmax_stnhq_bounded.
    unfold max_hq_index_bounded.
    unfold foldleft.
    simpl.
    destruct (stntonat n k).
    - apply idpath.
    - simpl.
      etrans.
  Abort.

  (* TODO : bound twice ?   -  what does this mean?  *)
  Definition select_pivot_row {n : nat} (mat : Matrix F n n) ( k : ⟦ n ⟧%stn )
    (pn : n > 0) : ⟦ n ⟧%stn.
   Proof.
     exact (pr2 (max_argmax_stnhq_bounded ((transpose mat) k ) pn k)).
   Defined.

  Require Import UniMath.Combinatorics.Maybe.
  (* Selecting the first non-zero element index ≥ k, otherwise 0.*)
  Definition select_pivot_row_easy {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : maybe (⟦ n ⟧)%stn.
  Proof.
    destruct iter as [ idx pr2' ].
    induction idx.
    - exact nothing.
    - destruct (natlthorgeh idx k). {exact nothing. }
      assert (pr2'' : idx < n). {apply pr2'. }
      destruct (mat k (idx ,, pr2'')).
      assert (pr2''' : idx < S n). {apply natlthtolths. exact pr2'. }
      destruct ( isdeceqhq   (mat k (idx,, pr2'')) 0%hq).
      + exact (IHidx pr2''').
      + exact (just (idx ,, pr2'')).
  Defined.

  (* Am I breaking convention here (more so than usually) ?*)
  Definition is_just {X : UU} (m : maybe X) : bool.
  Proof.
    destruct m.
    - exact true.
    - exact false.
  Defined.

  Definition from_just {X : UU} {m : maybe X} (p : is_just m = true) : X.
  Proof.
    destruct m.
    - exact x.
    - exact (fromempty (nopathsfalsetotrue p)).
  Defined.

  Definition select_pivot_row_correct1 {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : ∏ (i : ⟦ n ⟧%stn), i < iter -> k ≤ i -> (hqneq (mat k i) 0%hq) ->
      is_just ((select_pivot_row_easy  mat k iter)) = true.
  Proof.
    intros i i_gt_k ? mat_ki_neq_0.
    unfold select_pivot_row_easy.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl.
      apply negnatlthn0 in i_gt_k.
      contradiction.
    - rewrite nat_rect_step.
      destruct (natlthorgeh pr1_ k).
      (* TODO simplify *)
      + assert (k_lt_pr1_ : i ≤ pr1_).  {apply natlthsntoleh; assumption.  }
        assert (k_le_pr1_ : k ≤ pr1_ ). {apply (istransnatleh X k_lt_pr1_). }
        apply fromempty.
        apply  natlehneggth  in k_le_pr1_.
        contradiction.
      + destruct (isdeceqhq _ _). 2: {apply idpath. }
        simpl.
        destruct (nat_eq_or_neq i (pr1_)).
        2: { simpl. apply IHpr1_.
             assert (k_lt_pr1_ : i ≤ pr1_).  {apply natlthsntoleh; assumption.  }
             apply (natleh_neq k_lt_pr1_ h0).
        }
        simpl in mat_ki_neq_0.
        simpl in p.
        apply fromempty.
        rewrite <- p in mat_ki_neq_0.
        assert (absurd : mat k i = mat k (pr1_ ,, pr2_)).
        { apply maponpaths.
          apply subtypePath_prop.
          apply p0.
        }
        contradiction.
  Defined.

  Definition select_pivot_row_correct2 {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    (piv:  (is_just (select_pivot_row_easy  mat k iter)) = true)
    : (* ∏ (i : ⟦ n ⟧%stn), i < iter -> k ≤ i -> *) hqneq (mat k (from_just piv)) 0%hq.
  Proof.
    (* intros i i_ge_k is_just'. *)
    revert piv.
    unfold select_pivot_row_easy.
    unfold is_just.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - simpl. {intros; apply fromempty; apply nopathsfalsetotrue; assumption. }
    - rewrite nat_rect_step.
      destruct (natlthorgeh pr1_ k).
      { simpl; intros; apply fromempty; apply nopathsfalsetotrue; assumption. }
      destruct (isdeceqhq (mat k (pr1_,, pr2_)) 0%hq).
      2: { simpl. intros ?. assumption. }
      apply IHpr1_.
  Defined.

  Definition select_pivot_row' {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : hq × ⟦ n ⟧%stn.
  Proof.
    (* assert (x : iter ≥ 0). admit. *)
    destruct iter as [ idx pr2_ ].
    induction idx.
    - use tpair.
      + exact 0%hq.
      + assert (obv : 0 < n). { destruct (natchoice0 n); try apply (stn_implies_ngt0 k); assumption; contradiction. }
        exact (make_stn n 0 obv). (* Just a placeholder *)
    - assert (obv : idx < S n). { apply (istransnatlth _ _ _  (natlthnsn idx) pr2_  ).  }
      assert (obv''' : idx < n). {apply pr2_. }
      set (idx' := make_stn n idx obv''').
      destruct (natgthorleh idx' k).
      + destruct (hqgthorleh (abs_hq (mat idx' k )) (abs_hq (pr1 (IHidx obv)))); use tpair.
        * exact (mat idx' k ).
        * exact idx'.
        * exact (pr1 (IHidx obv)).
        * exact (pr2 (IHidx obv)).
      + use tpair. (* This is essentially 0%hq *)
        * exact (pr1 (IHidx obv)).
        * exact (pr2 (IHidx obv)).
  Defined.

  Definition select_pivot_row'_increasing { n : nat } (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn)
    : hqleh
      (abs_hq (pr1 (select_pivot_row' mat k iter)))
      (abs_hq ((pr1 (select_pivot_row' mat k ( n,, natlthnsn n ))))).
  Proof.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - replace   (abs_hq (pr1 (select_pivot_row' mat k (0,, pr2_)))) with 0%hq.
      + apply abs_ge_0_hq.
      + simpl.
        unfold abs_hq.
        destruct (hqgthorleh _ _).
        { reflexivity. }
        rewrite <- hqplusl0.
        rewrite hqpluscomm.
  Abort.

  Definition select_pivot_row'_idx_ge_pivot {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn)  (iter : ⟦ S n ⟧%stn) : pr2 (select_pivot_row' mat k (n,, natlthnsn n )) ≥ (pr1 k).
  Proof.
    (* unfold select_pivot_row'. *)
    destruct k as [ind pr2_ ].
    induction ind.
    - cbn. apply idpath.
    - unfold select_pivot_row'.
      unfold select_pivot_row' in IHind.
  Abort.

  Definition select_pivot_row'_idx_ge_pivot' {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn)  (iter : ⟦ S n ⟧%stn) : pr2 (select_pivot_row' mat k (n,, natlthnsn n )  ) ≥ (pr1 k).
  Proof.
    intros.
    destruct k as [k' k'_le_n].
    (* induction k'. { simpl; apply idpath. } (* reflexivity. } *) *)
    unfold select_pivot_row'.
    induction k'.
    - simpl. apply idpath.
    - induction n.
      + simpl. (* admit. (* contr *)
      + rewrite nat_rect_step. *)
  Abort.

  Definition select_pivot_row'_selects_max_el {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : ∏ i : ⟦ n ⟧%stn, hqleh (mat i k) (pr1 (select_pivot_row' mat k (n,, natlthnsn n ))).
  Proof.
    intros i.
    destruct k as [pr1_ pr2].
    induction pr1_.
    - unfold select_pivot_row'.
  Abort.

  Definition select_pivot_row'_selects_max_idx {n : nat} (mat : Matrix hq n n) (k : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : hq × ⟦ n ⟧%stn.
  Abort.

  Definition select_pivot_row'_nonzero {n : nat} (mat : Matrix hq n n) (k  : ⟦ n ⟧%stn) (iter : ⟦ S n ⟧%stn) : hq × ⟦ n ⟧%stn.
  Abort.


        (* Having an index variable k  0 .. n - 1,
     we want to certify that the selected pivot is >= k. *)
  Lemma pivot_idx_geq_k {n : nat} (mat : Matrix F n n) ( k : ⟦ n ⟧%stn )
    (pn : n > 0) : pr1 ( select_pivot_row mat k pn ) >= k.
  Proof.
    unfold select_pivot_row.
    unfold max_argmax_stnhq.
    (* unfold truncate_pr1. *)
    (* apply (max_argmax_stnhq_bounded_geq_k). *)
  Abort.


  (* Stepwise Gaussian Elimination definitions *)



  (* Refactored to include induction on natgthorleh j k*)
  Definition gauss_clear_column_step (n : nat) (k : (⟦ n ⟧%stn))
             (j : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct (natgthorleh j k) as [? | ?].
    - exact ((make_add_row_matrix k j (- ( (mat j k) * hqmultinv (mat k k)))%hq
      ** mat)).
    - exact mat.
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

  (* iter from n -> 1, 0 return as we start with n - k (might = n)*)
  (* assumes we have the non-zero pivot element at index [k, k] *)
  (* TODO rename as clear column _segment_ *)
  Definition gauss_clear_column  { n : nat } (*(iter : ⟦ n ⟧%stn)*)
             (pr1_ : nat) (pr2_ : pr1_ < n) (k : (⟦ n ⟧%stn))
             (mat : Matrix F n n) : Matrix F n n.
  Proof.
    (*revert mat.*)
    (*destruct iter as [pr1_ pr2_].*)
    induction pr1_ as [ | m gauss_clear_column_IH ].
    {exact mat. }  (* not applying the step since surely 0 ≤ k *)
    set (piv := mat k k).
    set (pr1idx := S m).
    set (j := make_stn n (S m) pr2_).
    set (m_lt_n := istransnatlth m (S m) n (natlthnsn m) pr2_).
    (*exact (gauss_clear_column_IH m_lt_n
               ( gauss_clear_column_step' n k j mat)).*)   (* <--- this is the old, incorrect version *)
    exact (gauss_clear_column_step' n k j (gauss_clear_column_IH m_lt_n)).
  Defined.

  (* Equivalent and the right definition with iter as S n instead of n -> TODO is
     replacing uses of the other one with this one *)
  Definition gauss_clear_column'  { n : nat } (iter : ⟦ S n ⟧%stn)
             (k : (⟦ n ⟧%stn))
             (mat : Matrix F n n) : Matrix F n n.
  Proof.
    (*revert mat.*)
    destruct iter as [pr1_ pr2_].
    induction pr1_ as [ | m gauss_clear_column_IH ].
    {exact mat. }  (* not applying the step since surely 0 ≤ k *)
    set (piv := mat k k).
    assert (m_lt_n : m < S n). {  apply (istransnatlth _ _ _ (natlthnsn m) pr2_) . }
    (*exact (gauss_clear_column_IH m_lt_n
               ( gauss_clear_column_step' n k j mat)).*)   (* <--- this is the old, incorrect version *)
    exact (gauss_clear_column_step' n k (m,, pr2_) (gauss_clear_column_IH m_lt_n)).
  Defined.

  (* Constructing the matrix corresponding to repeated applications of
     gauss_clear_column_step when the target matrix is thereby left-multiplied. *)
  Lemma gauss_clear_column_as_left_matrix { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k : (⟦ n ⟧%stn))  : Matrix hq n n.
  Proof.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - exact (identity_matrix).
    - assert (pr2_' : pr1_ < n). { apply pr2_. }
     exact (make_add_row_matrix (pr1_ ,, pr2_) (pr1_,, pr2_) (- ((mat (pr1_,,pr2_) k) * hqmultinv (mat k k)))%hq
        ** (IHpr1_ ( istransnatlth _ _ _ pr2_ (natlthnsn (S n))  ))).
  Defined.

  Lemma clear_column_matrix_invertible  { n : nat } (iter : ⟦ S n ⟧%stn)
        (mat : Matrix hq n n) (k : (⟦ n ⟧%stn))
        : @matrix_is_invertible hq _ (gauss_clear_column_as_left_matrix  iter mat k).
  Proof.
    set (pre := gauss_clear_column_as_left_matrix iter mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    -  simpl in pre.
       apply identity_is_inv.
    - unfold pre.
      rewrite nat_rect_step.
      refine (inv_matrix_prod_is_inv _ _ _ _ ).
      + (* matrix_is_invertible (make_add_row_matrix) *) admit. (* ... *)
      + apply IHpr1_.
  Admitted.

  Lemma clear_column_eq_matrix_def { n : nat } (iter : ⟦ S n ⟧%stn)
        (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) :
    ((gauss_clear_column_as_left_matrix iter mat k) ** mat) = gauss_clear_column' iter k mat.
  Proof.
  Abort.


  (* Need to think of a proper naming for this *)
  (* And actually this one needs to iterate from 0 -> n ? *)
  (* DEPRECATED — uses wrong order of iteration. TODO: remove. *)
  (* [gauss_clear_multiple_column_segments n k mat]:
     clear all columns of [mat] from [n-1] backwards to [k] ,
     return the result *)
  Definition gauss_clear_multiple_column_segments_backwards { n : nat }
             (k : (⟦ n ⟧%stn))
             (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct k as [k lt_k_n].
    destruct (natchoice0 n) as [? | gt].
    (* case n = 0 *)  { exact mat. }
    (* case 0 < n *)
    assert (pr2' : n - 1 < n). { apply (natminus1lthn _ gt) . }
    induction k as [ | m gauss_call_IH].
    - assert (pr2_0 : 0 < n). { exact lt_k_n. }
      set (k := make_stn n 0 lt_k_n).
      exact (gauss_clear_column (n - 1) pr2'  k mat).
    - assert (pr2_sm: S m < n). { assumption. }
      assert (pr2_m: m < n). { apply natlehsntolth. apply natlthtoleh.  assumption. }
      set (k' := make_stn n (S m) lt_k_n).
      exact (gauss_clear_column (n - 1) pr2' k' (gauss_call_IH  pr2_m)).
  (* In the current formulation, we should be using S m ?
     The use should be standardized. *)
  Defined.


  (* [gauss_clear_multiple_column_segments n k mat]:
     clear all columns of [mat] from [n-1] backwards to [n-k],
     return the result *)
  (* TODO: should go forwards not backwards!  fix or replace *)
  Definition gauss_clear_multiple_column_segments'  { n : nat }
             (k : (⟦ n ⟧%stn))
             (mat : Matrix F n n) : Matrix F n n.
  Proof.
    assert (gt_n_0 : 0 < n ). { apply stn_implies_ngt0; assumption. }
    assert (pr2' : n - 1 < n). { apply natminus1lthn; assumption. }
    destruct k as [k lt_k_n].
    induction k as [ | m gauss_call_IH].
    - exact mat.
    -(*
      destruct (natlehchoice (n - pr1_k) n) as [leq | eq] .
      + apply natminuslehn. *)
      (* + *)
      assert (obv : n - (S m) < n). { apply natminuslthn; try reflexivity; assumption. }
      set (k' := make_stn n (n - (S m)) obv).

        assert (follows : m < n). {apply natlehsntolth.  apply natlthtoleh in lt_k_n. assumption. }
      exact (gauss_clear_column (n - 1)  pr2'  k' (gauss_call_IH follows )).
  Defined.
  (*  with
  gcmcs (S m) mat = gcc (n-1) (n - (S k)) (gcmcs k mat),
    gives roughly:
  gcmcs 0 mat == mat'
  gcmcs 1 mat == gcc (n–1) (n–1) (gcmcs 0 mat)
              == gcc (n-1) (n-1) mat
  gcmcs 2 mat == gcc (n–1) (n–2) (gcmcs 1 mat)
              == gcc (n-1) (n-2) $ gcc (n-1) (n-1) mat
  gcmcs 3 mat == gcc (n–1) (n–3) (gcmcs 2 mat)
              == gcc (n-1) (n-3) $ gcc (n-1) (n-2) $ gcc (n-1) (n-1) mat

fixes:

  keep “intention” that [gmcs k mat] clears from [n–k] forwards to [n–1],
  and define the successor case as
  gcmcs (S m) mat = gcmcs k (gcc (n-1) (n - (S k)) mat)

  alternative ([gauss_clear_columns_up_to] below):
  change “intention” to: [gcmcs k mat] clears columns from [0] up to (below) [k]
  and define successor step as
  gcmcs (S m) mat = gcc (n-1) m (gcmcs k mat),

   *)

  (* [gauss_clear_columns_up_to k mat]:
clear all columns [i] of [mat] for 0 ≤ i < k;
return the result *)
  Definition gauss_clear_columns_up_to { n : nat } (p : n > 0) (* Remove p when gcc is refactored *)
             (k : (⟦ S n ⟧%stn))
             (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct k as [k lt_k_n].
    induction k as [ | k' gauss_clear_earlier_columns].
    - exact mat.
    -
      refine (gauss_clear_column (n - 1) (natminus1lthn n p) (k' ,, lt_k_n)  (gauss_clear_earlier_columns _)).
      (*+ apply (natminus1lthn _ p). (*tofix! *)*)
      apply (istransnatlth _ _ _ (natlthnsn k') lt_k_n) .
      (* + assert (intm : k' < n). {apply lt_k_n. }
                                apply (istransnatlth _ _ _ lt_k_n (natlthnsn (S n))  ). *)
  Defined.

  Lemma clear_columns_up_to_as_left_matrix  { n : nat } (p : n > 0) (* Remove p when gcc is refactored *)
        (k : (⟦ S n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct k as [k lt_k_n].
    induction k as [ | k' gauss_clear_earlier_columns].
    - exact identity_matrix.
    - refine (matrix_mult (gauss_clear_column_as_left_matrix (n,, natlthnsn n) mat  (k' ,, lt_k_n))   (gauss_clear_earlier_columns _)).
      (*+ apply (natminus1lthn _ p). (*tofix! *)*)
      apply (istransnatlth _ _ _ (natlthnsn k') lt_k_n) .
  Defined.

  Lemma clear_columns_up_to_as_left_matrix_eq {n : nat} (iter : ⟦ S n ⟧%stn) (* Remove p when gcc is refactored *)
        (p : n > 0) (*TODO remove *) (k : (⟦ n ⟧%stn)) (mat : Matrix F n n)
    : (clear_columns_up_to_as_left_matrix p iter mat) = (gauss_clear_columns_up_to p iter mat ).
  Proof.
  Abort.

  Lemma clear_columns_up_to_matrix_invertible {n : nat} (iter : ⟦ S n ⟧%stn) (* Remove p when gcc is refactored *)
        (p : n > 0) (*TODO remove *) (k : (⟦ n ⟧%stn)) (mat : Matrix F n n)
    : @matrix_is_invertible hq _  (clear_columns_up_to_as_left_matrix p iter mat).
  Proof.
    set (pre := gauss_clear_column_as_left_matrix iter mat k).
    unfold gauss_clear_column_as_left_matrix in pre.
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    -  simpl in pre.
       apply identity_is_inv.
    - unfold clear_columns_up_to_as_left_matrix.
      rewrite nat_rect_step.
      refine (inv_matrix_prod_is_inv _ _ _ _ ).
      + apply clear_column_matrix_invertible .
      + apply IHpr1_.
  Defined.

  Definition gauss_clear_all_column_segments' { n : nat } (mat : Matrix F n n) : Matrix F n n.
  Proof.
    destruct (natchoice0 n). {exact mat. }
    refine (gauss_clear_columns_up_to  _ (n,,_) mat).
    - assumption.
    - exact (natgthsnn n).
  Defined.


  (* Inputting a matrix and transforming it int o an upper-triangular matrix by
     elementary matrix operations or equivalent *)
  (* TODO: redefine to use [gauss_clear_columns_up_to], or replace with [gauss_clear_all_columns] above *)
  Definition gauss_clear_all_column_segments { n : nat } (mat : Matrix F n n) : Matrix F n n.
  Proof.
    induction (natchoice0 n) as [n_eq_0 | n_gt_0].
    - exact mat.
    - exact (gauss_clear_multiple_column_segments' (n - 1,, natminus1lthn n n_gt_0) mat).
  Defined.


  (* TODO this is wrong but currently should be unsued *)
  Definition gauss_step  { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) : Matrix F n n × ⟦ n ⟧%stn.
  Proof.
    assert (pn : (n > 0)). { exact (stn_implies_ngt0 k). }
    set (ik := (select_pivot_row mat k pn)). (* ≥ k *)
    use tpair. 2: {exact ik. }
    intros i j. (* lth S i ? *)
    destruct (natlthorgeh i (S k)) as [LT | GTH]. {exact ((mat i j)). }   (* TODO this is wrong - *)
    set (mat' := gauss_switch_row mat k ik).
    set (mat'' := gauss_scalar_mult_row mat' ((- 1%hq)%hq * (hqmultinv ( mat' k k )))%hq i).
    (* assert (pr2idx : n - 1 < n). (* TOOD refactor *)
      {apply (nminus1_lt_n (stn_implies_ngt0 k)). } *)
    destruct (natlthorgeh j (S k)).
    - exact (mat'' i j).
    - exact (((mat'' i j) + (mat'' i k) * (mat'' k j))%hq).  (* mat'' or mat ?
                                                             This should be elementary row op ! *)
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

  (* TODO move up *)
  Require Import UniMath.NumberSystems.Integers.

  (* hqlditr not used and available in real numbers module already. *)
  (* Lemma hqldistr (x y z : hq) : paths (z * (x + y))%hq (z * x + z * y)%hq.
  Proof.
    intros.
    apply (rigldistr F x y z).
  Defined. *)


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
    unfold make_add_row_matrix, "**". (* TODO unfold matrix mult *)
    unfold row, col, transpose, flip, "^".
    assert (p''' : n > 0). { apply (stn_implies_ngt0 k). }   (* should be gt0 in name! TODO *)
    set (f := λ i, _).
    rewrite (@two_pulse_function_sums_to_points_rig' F n _ p''' k j). (*TODO fix ugly signature *)
    - unfold f.
      unfold identity_matrix, Matrix.identity_matrix. (*TODO*)
      destruct (stn_eq_or_neq k j) as [k_eq_j | k_neq_j].
      + rewrite stn_neq_or_neq_refl.
        simpl.
        symmetry in k_eq_j.
        rewrite (stn_eq_or_neq_left k_eq_j).
        simpl.
        do 2 rewrite (stn_neq_or_neq_refl).
        simpl.
        symmetry in k_eq_j.
        rewrite (stn_eq_or_neq_left k_eq_j).
        simpl.
        unfold const_vec.
        rewrite k_eq_j.
        rewrite (@rigrunax2 F).
        rewrite <- k_eq_j.
        rewrite (hqisrinvmultinv (mat k k)).
        2 : {exact p'. }
        assert (∏ (x : hq), x + (- x) = x - x)%hq.
        { intros.
          rewrite hqrminus.
          rewrite hqpluscomm.
          rewrite hqlminus.
          apply idpath.
        }
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
            (* replace ((x * - y)%hq = (- x * y)%hq. *)
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
    - (*  intros.
       reflexivity.
       apply pulse_function_sums_to_point_rig''. *)
      (*revert f. *)
      intros i i_neq_k i_neq_j.
      unfold f.
      rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
      unfold identity_matrix, Matrix.identity_matrix. (*TODO *)
      apply issymm_natneq in i_neq_k.
      apply issymm_natneq in i_neq_j.
      rewrite (stn_eq_or_neq_right i_neq_k), coprod_rect_compute_2.
      rewrite (stn_eq_or_neq_right i_neq_j), coprod_rect_compute_2.
      etrans. {apply maponpaths_2.
        rewrite hqplusl0. reflexivity. }
      unfold const_vec.
      rewrite (rigmultx0 F (_)%hq).
      apply rigmult0x.
  Defined.

    (* The clear column step operation only changes the target row*)
  Lemma gauss_clear_column_step_inv2 (n : nat) (k: (⟦ n ⟧%stn))
         (r : (⟦ n ⟧%stn)) (mat : Matrix F n n) (j : ⟦ n ⟧%stn)
        (p : r ≠ j)  : (gauss_clear_column_step n k j mat) r = mat r.
  Proof.
    intros.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k) as [? | ?].
    2 : {apply idpath. }
    unfold make_add_row_matrix, "**".
    unfold "^", col, row, transpose, flip.
    assert (p'' : n > 0). { apply stn_implies_ngt0. assumption. } (* TODO rename stnnge0 *)
    apply funextfun. intros q.
    destruct (stn_eq_or_neq r j ) as [r_eq_j | r_neq_j].
    - simpl.
      rewrite r_eq_j in p.
      apply isirrefl_natneq in p; contradiction.
    - simpl.
      rewrite (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 j ) r ).
      + rewrite (id_mat_ii).
        apply (@riglunax2 F).
      + unfold is_pulse_function. (* TODO use just one of these pulse defs *)
        intros x r_neq_x.
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
    unfold make_add_row_matrix, "**".
    unfold "^", col, row, transpose, flip.
    assert (p' : n > 0). { apply stn_implies_ngt0. assumption. }
    set (f := λ i : (⟦ n ⟧%stn), _).
    assert (b : Σ f = f r ). {
      apply (@pulse_function_sums_to_point_rig'' F n _ (stn_implies_ngt0 j) r).
      unfold is_pulse_function.
      intros q r_neq_k.
      unfold f.
      destruct (stn_eq_or_neq r j) as [r_eq_q | r_neq_q].
      - rewrite r_eq_q in p. (*TODO*)
        apply (isirrefl_natneq) in p.
        contradiction.
      - unfold identity_matrix, Matrix.identity_matrix. (* TODO *)
        rewrite coprod_rect_compute_2.
        rewrite (stn_eq_or_neq_right r_neq_k), coprod_rect_compute_2.
        apply rigmult0x.
    }
    rewrite b.
    unfold f.
    rewrite (stn_eq_or_neq_right p), coprod_rect_compute_2.
    unfold identity_matrix, Matrix.identity_matrix.
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

  (* Lemma gauss_clear_column_inv0 { m n : nat} (p : n = S m) (p' : m < n) (k : (⟦ n ⟧%stn))
        (mat : Matrix F n n) :
    gauss_clear_column m p' k mat = gauss_clear_column_rowwise k mat.
  Proof.
    unfold gauss_clear_column_rowwise.
    apply funextfun. intros i.
    destruct (natgthorleh i k) as [? | ?].
    - simpl.
  Abort. *)

  (* Sure but this is uninteresting ? *)
  Lemma snchoice0 (n : nat) : (0 = n) ⨿ (0 < S n).
  Proof.
    induction n as [ | n].
    use ii1. apply idpath.
    use ii2. apply natgthsn0.
  Defined.



  (* TODO do we actually need a separate lemma for this ? Naming ? *)
  Lemma stn_succ_inhabited_implies_pred : ∏ n : nat, (⟦ S n ⟧)%stn → ∑ m : nat, m = S n.
  Proof.
    intros n sn.
    use tpair.
    - exact (n + 1).
    - simpl.
      rewrite <- plus_n_Sm, natplusr0.
      apply idpath.
  Defined.



  (* Proving mat r  is unchanged after column clearance   if r > n'. *)
  Lemma gauss_clear_column_inv0'
        { n : nat } (k : (⟦ n ⟧%stn))
        (n' : nat) (p : n' < n)  (mat : Matrix F n n) (r : ⟦ n ⟧%stn)
    (r_gt_n' : r > n') : (gauss_clear_column n' p k mat) r = mat r.
  Proof.
    induction n'.
    - simpl.
      reflexivity.
    - set (sn' := make_stn n (S n')  p).
      assert (q : n' < n). { set (n'_lt_r := (istransnatlth n' (S n') r (natlthnsn n')  r_gt_n' )).
                             apply (istransnatlth n' r n n'_lt_r (pr2 r) ). }
      assert (q': r > n'). {apply (istransnatlth n' (S n') r (natlthnsn n' ) r_gt_n'). }
      destruct (stn_eq_or_neq (make_stn n (S n') p) k ).
      { unfold gauss_clear_column, gauss_clear_column_step.
        - simpl.
          rewrite <- gauss_clear_column_step_eq.
          rewrite gauss_clear_column_step_inv2.
          2 : { apply natgthtoneq in r_gt_n'.  apply r_gt_n'.  }
          unfold gauss_clear_column in IHn'.
          apply IHn'; assumption.
      }
      simpl.
      unfold gauss_clear_column_step'.
      destruct (natgthorleh (make_stn n (S n') p ) k).
      + simpl.
        unfold make_add_row_matrix.
        unfold gauss_add_row.
        apply funextfun. intros x.
        simpl.
        assert (obvious : r ≠ (S n')).
        { apply (natgthtoneq _ _ r_gt_n'). }
        simpl.
        (* set (hmm := coprod_rect _ _). *)
        destruct (stn_eq_or_neq r (make_stn n (S n') p)).
        * rewrite p0 in obvious.
          apply isirrefl_natneq in obvious.
          contradiction.
        * simpl.
          rewrite IHn'.
          { apply idpath. }
          assumption.
      + rewrite IHn'.
        { apply idpath. }
        assumption.
  Defined.


  (* if the target row r ≤  the pivot row k,
     mat r is not changed by the clearing procedure. *)
  Lemma gauss_clear_column_inv3
        { n : nat } (k r : (⟦ n ⟧%stn))
        (n' : nat) (p : n' < n)  (p' : r ≤ k)
        (mat : Matrix F n n) (kk_ne_0 : mat k k != 0%hq) :
    ((gauss_clear_column (*(n',, p)*) n' p k mat) r = mat r).
  Proof.
    (*destruct n' as [pr1_
    destruct (n' ,, p) as [pr1_ pr2_].*)
    (*destruct iter as [pr1_ pr2_]. *)
    induction n'.
    { unfold gauss_clear_column.
      simpl.
      reflexivity. }
    simpl.
    unfold gauss_clear_column.
    simpl.

    apply funextfun. intros q.
    rewrite <- gauss_clear_column_step_eq.
    rewrite gauss_clear_column_step_inv5.
    2 : {assumption. }
    unfold gauss_clear_column in IHn'.
    rewrite IHn'.
    reflexivity.
  Defined.

  Lemma gauss_clear_column_commute
    { n : nat } (mat : Matrix F n n) (j k r : ⟦ n ⟧%stn)
    (n' : nat) (p : n' < n) (p' : j > n') :  (* do we need p' ? *)
    gauss_clear_column_step n k j (gauss_clear_column n' p k mat) r
 =  gauss_clear_column n' p k (gauss_clear_column_step n k j mat) r.
  Proof.
    unfold gauss_clear_column_step.
    destruct (natgthorleh j k ).
    2 : { reflexivity.  }
    unfold make_add_row_matrix.
    apply funextfun. intros x.
    unfold "^", "**", "^", const_vec, col, row, transpose, flip.
    rewrite gauss_clear_column_inv0'.
  Abort.


  (* Proving the column clearing procedure works on one row at a time *)
  Lemma gauss_clear_column_inv0
        { n : nat } (k : (⟦ n ⟧%stn))
        (n' : nat) (p : n' < n) (mat : Matrix F n n) (p' : mat k k != 0%hq) : ∏ r : (⟦ n ⟧%stn),
    r <= n' -> ((gauss_clear_column n' p k mat) r = (gauss_clear_column_step' n k r mat) r).
  Proof.
    revert mat k p' p.
    induction n'.
    - intros mat k kk_ne_0 p r (* ? *) r_le_0.
      unfold gauss_clear_column, gauss_clear_column_step'.
      simpl.
      destruct (natgthorleh r k) as [absurd | ?].
      + apply  natleh0tois0 in r_le_0.
        rewrite r_le_0 in absurd.
        contradiction (negnatgth0n n absurd).
      + apply idpath.
    - intros mat k kk_ne_0 p r r_le_sn. (* simpl. *)
      assert (q : n' < n). {apply (istransnatlth n' (S n') n (natlthnsn n' ) p) . }
      set (sn' := make_stn n (S n') p).

      (* unfold gauss_clear_column. *)
      (* rewrite nat_rect_step. *)
      set (IHnp := IHn'  mat k kk_ne_0 q).
      destruct (natlehchoice r (S n')) as [? | eq].
      + assumption.
      + assert (follows : r ≤ n'). { apply natlthsntoleh in h; assumption. }
        rewrite <- (IHnp r follows).
        simpl.
        rewrite <- gauss_clear_column_step_eq.
        rewrite (gauss_clear_column_step_inv2).
        2 : { apply natgthtoneq in h.
              apply issymm_natneq. apply h.
        }
        etrans. {(* apply maponpaths_2.*)
                assert (eq : q =  ( (istransnatlth n' (S n') n (natlthnsn n') )) p).
                apply proofirrelevance.
                apply propproperty.
                rewrite <- eq.
                apply idpath.
        }
       apply idpath.
      + (* simpl.
        simpl. *)
        rewrite <- gauss_clear_column_step_eq.
        (* simpl. *)
        rewrite gauss_clear_column_step_eq.
        simpl.
        do 2 rewrite <- gauss_clear_column_step_eq.
        set (sn'' := (make_stn n (S n') p)).
        set (p'' := istransnatlth _ _ _ _ _).
        replace   (gauss_clear_column_step n k sn'' (gauss_clear_column n' p'' k mat) r)
          with (gauss_clear_column_step n k sn'' mat r).
        { replace sn'' with r.
          { apply idpath. }
          rewrite (@subtypePath_prop _ _ r (S n',, p)). {reflexivity. }
          apply eq.
        }
        assert (step1 : (gauss_clear_column n' p'' k mat) r = mat r).
        { rewrite gauss_clear_column_inv0'.
          - apply idpath.
          - rewrite eq.
            apply natlthnsn. }
        assert (commute :  gauss_clear_column_step n k sn'' (gauss_clear_column n' p'' k mat) r
                           =  gauss_clear_column n' p'' k (gauss_clear_column_step n k sn'' mat) r).
        (* The main challenge with this proof lies here *)
        (* Can we do better than unfolding and brute-forcing this proof ? *)
        { unfold gauss_clear_column_step.
          destruct (natgthorleh sn'' k).
          2 : { reflexivity.  }
          unfold make_add_row_matrix.
          apply funextfun. intros x.
          unfold "^", "**", "^", const_vec, col, row, transpose, flip.
          rewrite gauss_clear_column_inv0'.
          2 : { unfold sn''. apply (natlthnsn). }
          assert (eq' : r = sn'').
          { rewrite (@subtypePath_prop _ _ r (S n',, p)). {reflexivity. }
            apply eq.
          }
          rewrite <- eq'.
          set (obviously := idpath r).
          rewrite (stn_neq_or_neq_refl).
          simpl.
          apply pathsinv0.
          etrans. { rewrite (gauss_clear_column_inv0').
                    2 : { rewrite eq.
                          apply natlthnsn.
                    }
                    apply idpath.
          }
          rewrite stn_neq_or_neq_refl.
          simpl.
          apply maponpaths.
          apply funextfun. intros y.
          destruct (stn_eq_or_neq k y) as [eq'' | ?].
          -  rewrite <- eq'' in *.
             rewrite id_mat_ii.
             do 2 rewrite (@rigrunax2 hq).
             rewrite gauss_clear_column_inv3.
             + apply idpath.
             + apply isreflnatleh.
             + apply kk_ne_0.
             (* Need a lemma that states that (clear column mat ) pivot = mat pivot *)
          - rewrite (id_mat_ij k y).
            2 : {exact h0. }
            do 2 rewrite (@rigmultx0 hq); rewrite (@rigrunax1 hq).
            destruct (stn_eq_or_neq r y).
            * rewrite p0.
              rewrite gauss_clear_column_inv0'.
              { apply idpath. }
              rewrite <- p0.
              rewrite eq.
              apply natgthsnn.
            * rewrite (id_mat_ij r y).
              { do 2 rewrite (@rigmult0x hq).
                apply idpath.
              }
              assumption.
        }
        rewrite commute.
        rewrite gauss_clear_column_inv0'.
        2 : { rewrite eq.
              apply natgthsnn.
        }
        reflexivity.
  Defined.


  (* Proving mat r  is unchanged after column clearance   if r > n'. *)
  Lemma gauss_clear_column_inv0''
        { n : nat } (k : (⟦ n ⟧%stn))
        (n' : nat) (p : n' < n)  (mat : Matrix F n n) (r : ⟦ n ⟧%stn)
    (r_gt_n' : r > n') : (gauss_clear_column n' p k mat) r = mat r.
  Proof.
    induction n'.
    - simpl.
      reflexivity.
    - set (sn' := make_stn n (S n')  p).
      assert (q : n' < n).
      { exact  (istransnatlth n' r n (istransnatlth n' (S n') r (natlthnsn n')  r_gt_n' ) (pr2 r) ). }
      assert (q': r > n'). {apply (istransnatlth n' (S n') r (natlthnsn n' ) r_gt_n'). }
      simpl.
      rewrite <- gauss_clear_column_step_eq.
      rewrite gauss_clear_column_step_inv2.
      2: { exact (natgthtoneq r (S n') r_gt_n'). }
      rewrite IHn'.
      + reflexivity.
      + assumption.
  Defined.


  (* Invariant stating that the clearing procedure does clear all the target entries (r, k) for r > k. *)
  Lemma gauss_clear_column_inv1
        { n : nat } (k : (⟦ n ⟧%stn))
        (n' : nat) (p : n' < n)  (mat : Matrix F n n) (p' : mat k k != 0%hq) :  ∏ r : (⟦ n ⟧%stn),
    r <= n' -> r > k ->((gauss_clear_column n' p k mat) r k = 0%hq).
  Proof.
    intros r r_le_n' r_gt_k.
    rewrite (gauss_clear_column_inv0  k n' p mat p' r r_le_n').
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
        (n' : nat) (p : n' < n) (p': n' ≤ k)
        (mat : Matrix F n n) (kk_ne_0 : mat k k != 0%hq) :
    ((gauss_clear_column n' p k mat) = mat ).
  Proof.
    intros.
    apply funextfun. intros i.
    intros.
    induction n' as [| m IHn].
    - simpl.
      reflexivity.
    - assert (p'': m < n). { apply (istransnatlth m (S m) n  (natlthnsn m) p). }
      assert (p''' : m ≤ k). { apply (istransnatleh (natlehnsn m) p'). }
      set (IHn' := IHn p'' p''').
      rewrite <- IHn'.
      simpl.
      rewrite <- gauss_clear_column_step_eq.
      rewrite ( gauss_clear_column_step_inv4 ).
      2: {assumption. }
      destruct (natgthorleh i m) as [i_gt_m | i_leq_m].
      + rewrite (gauss_clear_column_inv0').
        2 : {assumption. }
        rewrite (gauss_clear_column_inv0').
        2 : {assumption. }
        reflexivity.
      + rewrite gauss_clear_column_inv0.
        2 : {assumption. }
        rewrite (gauss_clear_column_inv0).
        2 : {assumption. }
        reflexivity.
        assumption.
        assumption.
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
              i > k -> j < i -> mat i j = 0%hq.

  Definition diagonal_filled { n : nat } (mat : Matrix F n n) :=
    ∏ i : ⟦ n ⟧%stn, mat i i != 0%hq.

  (* Shows that gauss_clear_column(_segment) retains previously zeroed entries, e.g. fulfills
     [ 1 0 0 1          [ X 0 X X
       0 1 1 1            0 X X X
       0 0 1 1    ->      0 0 X X
       0 0 1 1]           0 0 X X ]

     for k = 2  and where X is arbitrary (1/0) *)
  Lemma gauss_clear_column_inv4
        { n : nat }  (mat : Matrix F n n) (n' k  : (⟦ n ⟧%stn)) (p : mat k k != 0%hq)
        (entry_zeroed : gauss_columns_cleared mat k) (kks_ne_0 : diagonal_filled mat):
        ∏ k' : (⟦ n ⟧%stn), k' > k ->
        gauss_columns_cleared (gauss_clear_column (pr1 n') (pr2 n') k' mat) k.
  Proof.
    intros k' k'_gt_k.
    unfold gauss_columns_cleared in *.
    intros i j.
    intros i_gt_k j_lt_k.
    destruct (natgthorleh i n').
    - rewrite gauss_clear_column_inv0'.
      + apply (entry_zeroed i j); assumption.
      + assumption.
    - rewrite gauss_clear_column_inv0.
      3 : {assumption. }
      2 : {apply kks_ne_0. }
      + unfold gauss_clear_column_step'.
        destruct (natgthorleh i k').
        2 : {apply entry_zeroed; assumption. }
        unfold gauss_add_row.
        rewrite stn_neq_or_neq_refl.
        simpl.
        rewrite (entry_zeroed i j i_gt_k j_lt_k), (@riglunax1 F).
        rewrite (entry_zeroed i k' i_gt_k  h0).
        rewrite hqmultcomm.
        etrans. { apply maponpaths. apply maponpaths. rewrite (@rigmult0x hq). reflexivity. }
        rewrite hqmultcomm.
        rewrite (@ringlmultminus  hq).
        rewrite (@rigmult0x F).
        change 0%rig with (@ringunel1 hq).
        rewrite (@ringinvunel1 hq).
        reflexivity.
  Defined.

  (* Same but without n' as stn and a bit differently stated*)
  Lemma gauss_clear_column_inv4'
        { n : nat }  (mat : Matrix F n n) ( k  : (⟦ n ⟧%stn)) (n' : nat) (p : n' < n)
        (entries_zeroed : gauss_columns_cleared mat k) (k' : ⟦ n ⟧%stn) (p' : (*k' > k*) k ≤ k') :
        (mat k' k' != 0%hq) ->
        gauss_columns_cleared (gauss_clear_column n' p k' mat) k. (* A bit weird,
                                                                   don't we need mat k' k' != 0 in gcc??*)
  Proof.
    intros.
    unfold gauss_columns_cleared in *.
    intros  i j.
    intros  i_gt_k j_lt_k.
    destruct (natgthorleh i n') as [i_gt_n' | i_leq_n'].
    - rewrite gauss_clear_column_inv0'.
      + apply (entries_zeroed i j); assumption.
      + assumption.
    - rewrite gauss_clear_column_inv0.
      3 : {assumption. }
      2 : {apply X. } (* rewrite ! *)
      + unfold gauss_clear_column_step'.
        destruct (natgthorleh i k').
        2 : {apply entries_zeroed; assumption. }
        unfold gauss_add_row.
        rewrite stn_neq_or_neq_refl.
        simpl.
        rewrite (entries_zeroed i j i_gt_k j_lt_k), (@riglunax1 F).
        replace (mat i k') with 0%hq.
        2 : { rewrite entries_zeroed; try assumption; reflexivity. }
        etrans. { apply maponpaths_2.
                  apply maponpaths.
                  rewrite (@rigmult0x hq).
                  reflexivity. }
        etrans. { apply maponpaths_2.
                  replace ((- (@rigunel1 hq))%hq) with (@rigunel1 hq).
                  - reflexivity.
                  - change (0%rig) with (@ringunel1 hq) at 2.
                    change (- 0%hq)%hq with 0%hq.
                    replace (- 0%ring)%hq with (@ringunel1 hq)%hq.
                    reflexivity.
                    replace (- 0%ring)%hq with (- 0%hq)%hq.
                    + rewrite <- (@ringinvunel1 hq).
                      reflexivity.
                    + reflexivity.
        }
        rewrite (@rigmult0x hq).
        reflexivity.
  Defined.
  (* Opaque gauss_clear_column. *)

  Lemma gauss_clear_multiple_column_segments_inv0
        ( n : nat ) (mat : Matrix F n n) (p : diagonal_filled mat) (p' : n > 0)
        (n' : ⟦ S n ⟧%stn)  :
        ∏ i j : ⟦ n ⟧%stn,
        i > j ->   n' > j ->
        (@gauss_clear_columns_up_to n p' n' mat) i j = 0%hq.
  Proof.
    unfold gauss_clear_columns_up_to.
    destruct n' as [n' lt_n'_n]. induction n'.
    { intros i j i_gt_j z_ge_j.
      simpl.
      admit. } (* Messed up base ? *)
    intros i j i_gt_j sn'_leq_j.
    rewrite nat_rect_step.
    destruct (natlehchoice j n' ).
    { admit. }
    2 : {  admit.  }
    rewrite (gauss_clear_column_inv4' _ j).
    - apply idpath.
    - unfold gauss_columns_cleared.
      intros i' j'.
      intros i'_gt_k' j'_lt_k'.
      apply IHn'.
      + assumption.
      +  admit.
    - assumption.
    - admit. (* Has to be added as an invariant for clearing a column *)
    - assumption.
    - assumption.
  Admitted.


  Lemma gauss_inv_upper_triangular {n : nat} (mat : Matrix F n n) (p : diagonal_filled mat):
    @is_upper_triangular F n n (gauss_clear_all_column_segments' mat ).
  Proof.
    intros i j i_gt_j.
    unfold gauss_clear_all_column_segments'.
    destruct (natchoice0 n) as [n0 | n_gt_0].
    { simpl. clear i_gt_j. generalize i. rewrite <- n0 in i. apply (fromstn0 i). }
    simpl.
    assert (p' : n - 1 < n). { apply (natminus1lthn n n_gt_0). }
    rewrite gauss_clear_multiple_column_segments_inv0.
    - reflexivity.
    - exact p.
    - assumption.
    - exact (istransnatlth _ _ _ i_gt_j (pr2 i)).
  Defined.


  (* Showing that a zeroed column segment remains zeroed while
     performing this operation in another column*)
  Lemma gauss_step_upper_rows_invariant { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n):
    ∏ (k' : (⟦ n ⟧%stn)), k' < k -> (mat k') = (pr1 (gauss_step k mat) k').
  Proof.
    intros k' k'_lt_k.
    unfold gauss_step.
    apply pathsinv0.
    set (mat' := λ i j : (⟦ n ⟧%stn), _).
    assert (p : mat k' = mat' k').
    { unfold mat'.
      apply funextfun. intros q.
      destruct (natlthorgeh k' (S k)) as [k_lt_sk | k_ge_sk].
      - reflexivity.
      - apply pathsinv0.
        destruct (natlthorgeh q (S k)) as [sq_lt_sk | q_ge_sk].
        + clear mat'.
          apply natgehsntogth  in k_ge_sk.
          apply isasymmnatgth in k'_lt_k. 2 : {assumption. }
          contradiction.
        + clear mat'.
          apply natgehsntogth in k_ge_sk.
          apply isasymmnatgth in k'_lt_k. 2 : {assumption. }
          contradiction.
    }
    rewrite p.
    apply funextfun. intros q.
    reflexivity.
  Defined.

  Lemma gauss_step_clears_diagonal { n : nat } (k : (⟦ n ⟧%stn)) (mat : Matrix F n n) :
    ∏ j : ⟦ n ⟧%stn, (j > k) -> (pr1 (gauss_step k mat)) j k = 0%hq.
  Proof.
    (*intros i j i_geq_k nmk_geq_j mat_ik_eq_0 i' j' i'_geq_k nmk_geq_j'.*)
    intros j j_gt_k.
    unfold gauss_step. simpl.
    destruct (natlthorgeh j (S k)) as [j_lt_sk | j_geh_sk].
    - apply natgthsntogeh in j_lt_sk.
      apply natgehtonegnatlth in j_lt_sk.
      contradicts j_gt_k j_lt_sk.
    - destruct (natlthorgeh k (S k)) as [k_lt_sk | k_geh_sk].
      + clear j_geh_sk. clear k_lt_sk.
        unfold gauss_scalar_mult_row, gauss_switch_row.
        do 2 rewrite (stn_neq_or_neq_refl), coprod_rect_compute_1.
        assert (p: j ≠ k). { apply (natgthtoneq j k j_gt_k).  } (*trivial *)
        rewrite (stn_eq_or_neq_right p), coprod_rect_compute_2.
        destruct (stn_eq_or_neq j (select_pivot_row mat k _)).
        * rewrite coprod_rect_compute_1.
          set (piv := select_pivot_row _ _ _).
          (* Not true !  *)

  Abort. (* We want to show that the pivot selection selects a pivot >= k
            And pivot selection needs to be correct in general ... *)


  (* k  : 1 -> n - 1 *)
  Definition vec_row_ops_step { n : nat } (k pivot_ik: ⟦ n ⟧%stn)  (mat : Matrix F n n) (vec : Vector F n) : Vector F n.
  Proof.
    intros i.
    induction (natlthorgeh i k). 2 : {exact (vec i). }
    set (vec' := switch_vector_els vec pivot_ik k).
    exact (  ((((vec' i)) + ((vec' k)) * (mat i k))%hq)).  (* TODO is this right?*)
  Defined.


  (*   TODOs here are a few sub-proofs.

       1. forall i : [[ n ]], i < j -> vec i = 0 ->  Σ vec = sum_right vec j.
       2. sum_right vec i  = vec i + sum_right vec (S i).
  *)

  Definition splitf { n m' n': nat } (vec : Vector R n) (p : m' + n' = n) :  Vector R (m' + n').
  Proof.
    unfold Vector.
    rewrite p.
    exact vec.
  Defined.



  (* Kind of pointless ? *)
  Definition splitstn {n : nat} (i : ⟦ n ⟧%stn) : ∑ (j : nat), ( ∑ (stn : ⟦ i + j ⟧%stn), i + j = n ).
  Proof.
    assert (eq: (n - i) + i = n).
    { apply minusplusnmm.
      exact (natgthtogeh n (pr1 i) (pr2 i)).
    }
    use tpair.
    { exact (n - i). }
    use tpair.
    set (j := n - i).
    - assert (pr2 : i < j + i ).
      { unfold j.
        rewrite eq.
        exact (pr2 i). }
      rewrite natpluscomm in pr2.
      set (i' := make_stn (i + j) i (pr2)).
      exact i'.
    - simpl.
      rewrite natpluscomm in  eq.
      exact eq.
  Defined.


  (* TODO also standardize use of n, m in all of these - n or m comes first?*)
  Lemma snlehtotonlt (m n : nat) : n > 0 -> (S n ≤ m) -> n < m.
  Proof.
    intros ngt0 snltm.
    assert (n_lt_sn : n < S n).
      { apply natlthnsn. }
    apply natlehsntolth.
      assumption.
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
    (* clamp_f should be called something like clear vec segment *)
    - exact ((vec i) * (hqmultinv (mat i i)))%hq.
    - unfold stn in i.
      apply (pr2 iter).
  Defined.



  (* TODO why can't I phrase this in terms of regular Rigs in back_sub_step_solves_eqs ? *)
  (* TODO also upstream (at least up this file ) *)
  Definition diagonalsq { n : nat } (mat : Matrix F n n) : Vector F n := λ i : ⟦ n ⟧%stn, mat i i.

  Definition vectorize_1 ( X : UU ) : X -> Vector X 1.
  Proof.
    apply weq_vector_1.
  Defined.

  Definition matn1_to_vector { X : UU } { n : nat }  : Matrix X n 1 -> Vector X n.
  Proof.
    intros.
    unfold Matrix in X0.
    set (thing := Vector X 1).
    apply weqvec_rowvec in X0. (* This isn't quite working ? *)
  Abort.

  (* This should be the naming convention throughout the file. *)
  Lemma stnmn_to_stn0n { X : UU } {n : nat} (i : ⟦ n ⟧%stn) : ⟦ n ⟧%stn.
  Proof.
    destruct n.
    - apply weqstn0toempty in i. contradiction.
    - exact(make_stn (S n) 0 (natgthsn0 0)).
  Defined.

  Lemma stnmn_to_stn01 { X : UU } {n : nat} (i : ⟦ n ⟧%stn) : ⟦ 1 ⟧%stn.
  Proof.
    destruct n.
    - apply weqstn0toempty in i. contradiction.
    - exact(make_stn (S 0) 0 (natgthsn0 0)).
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



  Require Import UniMath.PAdics.lemmas.
  Lemma back_sub_step_solves_eq' { n : nat } ( iter : ⟦ n ⟧%stn ) (mat : Matrix F n n) (b : Vector F n) (vec : Vector F n)
        (p: @is_upper_triangular F n n mat)
        (p' : diagonal_filled mat):
    (((mat ** (col_vec (back_sub_step iter mat vec))) iter  = (col_vec vec) iter )).
  Proof.
    intros.
    unfold back_sub_step.
    unfold col_vec.
    unfold "**", "^", row, col, transpose, flip.
    set (m := n - (S iter)).
    assert (spliteq : n = (S iter) + m ).
    { unfold m.
      rewrite natpluscomm.
      rewrite minusplusnmm.
      - apply idpath.
      - simpl. exact (pr2 iter).
    }
    generalize iter mat (* b *) vec p' p.
    set (itersucc := (stn_inhabited_implies_succ iter)).
    destruct itersucc as [pr1_ pr2_].
    rewrite pr2_ in *.
    intros iter' mat' vec' (*vec''*) filled' is_upper_t'.
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
        unfold funcomp, dni, di.
        simpl.
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
          assert (the_obvious: (sum + b'*a - b'*a)%hq = sum ).
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
          assert (the_obvious'''''': (sum + b'*a - b'*a)%hq = sum ).
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
          reflexivity.
        }
        rewrite (@rigcomm1 F).
        rewrite (@rigassoc1 hq).
        etrans.
        { apply maponpaths. apply maponpaths_2. apply maponpaths.
          rewrite the_obvious.
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
          unfold dni, di.
          simpl.
          destruct (natlthorgeh q iter') as [gt | ?].
          { apply gt. }
          apply invmaponpathsS in p0.
          apply fromempty.
          assert (q_ge_iter' : q ≥ (Preamble.pr1 iter')).
          { apply h. }
          rewrite p0 in q_ge_iter'.
          apply natgehtonegnatlth in q_ge_iter'.
          unfold "¬"  in q_ge_iter'.
          assert (q_le_iter_absurd : q < pr1_).
          { apply (Preamble.pr2 q). }
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
  Definition gauss_iterate
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
  Defined.


  Definition gauss_iterate'
     { n : nat } (iter : ⟦ S n ⟧%stn)
     (mat : Matrix F n n) (pivots : Vector (⟦ n ⟧%stn) n)
     (* (p : is_permutation_fun pivots) *)  (* TODO actually we should make pivots/permutations a Sigma type akin to stn. *)
    : (Matrix F n n) × ((Vector (⟦ n ⟧%stn) n)).
  Proof.
    destruct (natchoice0 n) as [? | gt]. { exact (mat ,, pivots). } (* TODO remove this later when gcc is S n*)
    destruct iter as [pr1_ pr2_].
    induction pr1_.
    - exact (mat,, pivots).
    - assert (pr2_' : pr1_ < n). { apply pr2_. }
      assert (pr2_'' : pr1_ < S n).  { apply (istransnatlth _ _ _ (pr2_') (natgthsnn n)). }
      set (piv :=  select_pivot_row_easy mat ( pr1_,, pr2_' ) (n,, natgthsnn n)).
      destruct piv as [piv' | ?].
      2: {exact (mat,, pivots). }
      (* assert piv ≥ n - pr1 *)
      exact (( gauss_clear_column (n - 1) (natminus1lthn _ gt) (pr1_,, pr2_')
              (gauss_switch_row (pr1 (IHpr1_ pr2_'') ) (pr1_,, pr2_') (piv')) )
          ,, (transpose_permutation_fun (pr2 (IHpr1_ pr2_'')) (pr1_,, pr2_')  (piv')  )).
  Defined.


  (*
  Fixpoint vec_ops_iterate ( iter : nat ) { n : nat }  ( start_idx : ⟦ n ⟧%stn) (b : Vector F n) ( pivots : Vector (⟦ n ⟧%stn) n) (mat : Matrix F n n) { struct iter }: Vector F n :=
    let current_idx := decrement_stn_by_m start_idx (n - iter)  in
    match iter with
    | 0 => b
    | S m => vec_ops_iterate m start_idx (vec_row_ops_step current_idx (pivots current_idx) mat b) pivots mat
    end. *)

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
    - assert (p: n - 1 < n).  {  apply (natminus1lthn n n_gt_0). }
      exact (back_sub' (n - 1) p mat vec).
  Defined.

  Definition gaussian_elimination {n : nat} (A : Matrix hq n n) (b : Vector hq n): Matrix hq n n × Vector hq n.
  Proof.
    set (A' := pr1 (gauss_iterate' (n,, natgthsnn n) A (id_permutation_fun n))).
    set (x := back_sub A' b).
    exact (A' ,, x).
  Defined.



  (* The main definition using above Fixpoints, which in turn use stepwise definitions.*)
  (* Definition gaussian_elimination { n : nat } (mat : Matrix F n n) (b : Vector F n) : Matrix F n n × Vector F n.
  Proof.
    induction (natchoice0 n).
    { exact (mat ,, b). }
    set (pr1m := n - 1). assert (pr2m : pr1m < n). {admit. }
    set (m := make_stn n pr1m pr2m).
    set (A_and_pivots := gauss_iterate m mat b (id_permutation_fun n) (idp_is_permutation_fun)). (* TODO better permutations *)
    set (A  := pr1 A_and_pivots).
    set (pv := pr2 A_and_pivots).
    (* TODO these should be redone *)
    (*set (b'  := vec_ops_iterate 0 (0,,pn) b pv A).
    set (b'' := back_sub_iterate n (0,, pn) b' pv A).*)
    set (b'' := b). (* dummy *)
    exact (A,, b'').
  Admitted. *)

  Definition gauss_solution_invar : True.
  Proof.
  Abort.

  (* Some properties on the above procedure which we would like to prove. *)


  (*
  Lemma A_is_upper_triangular { n : nat} ( temp_proof_0_lt_n : 0 < n ) (mat : Matrix F n n) :
    is_upper_triangular (pr1 (gauss_iterate 0 (0,, temp_proof_0_lt_n) mat (zero_vector_stn n))).
  Proof.
    intros.
  Abort. *)


  (* Reliance on pn, coercing matrices could be done away with. *)
  (*
  Lemma sol_is_invariant_under_gauss  {n : nat} (A : Matrix F n n) (x : Matrix F n 1) (b : Matrix F 1 n)  (pn : n > 0) (pn' : 1 > 0) :
    (A ** x) = (transpose b) -> ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** A ** x)  = ((pr1 (gaussian_elimination A (b (0,, pn')) pn)) ** (transpose b)).
  Proof.
    intros.
  Abort. *)





  (* Determinants, minors, minor expansions ... *)


  Definition ij_minor {n : nat} ( i j : ⟦ S n ⟧%stn )  (mat : Matrix R (S n) (S n)) : Matrix R n n.
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

End Gauss.








Section SmithNF.
 (* Generalized elimination over the ring of integers *)

  Local Definition I := hz.

  Local Notation Σ := (iterop_fun 0%hz op1).

  (* Does feel wasteful having to redefine this constantly - TODO coercions *)
  (* TODO standardize use of the following unfolded definition or use
     rows / cols here too *)
  Local Definition matrix_mult_hz {m n : nat} (mat1 : Matrix I m n)
    {p : nat} (mat2 : Matrix I n p) : (Matrix I m p) :=
    λ i j, Σ (λ k, (mat1 i k * mat2 k j))%hz.

  Local Notation "A ** B" := (matrix_mult_hz A B) (at level 80).


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
