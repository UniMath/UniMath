(** * Additive categories. *)
(** * Contents
- Definition of additive categories
- Quotient of an additive category is additive
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Monoids.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.Opp.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.

Local Open Scope cat.

(** * Definition of additive categories *)
Section def_additive.

  (** A preadditive category has an additive structure if it is given a zero object and a binary direct sum operation. *)
  Definition AdditiveStructure (PA : PreAdditive) : UU := (Zero PA) × (BinDirectSums PA).

  Definition make_AdditiveStructure (PA : PreAdditive) (H1 : Zero PA) (H2 : BinDirectSums PA) :
    AdditiveStructure PA.
  Proof.
    exact (H1,,H2).
  Defined.

  (** Definition of categories with an additive structure *)
  Definition CategoryWithAdditiveStructure : UU := ∑ PA : PreAdditive, AdditiveStructure PA.

  Definition Additive_PreAdditive (A : CategoryWithAdditiveStructure) : PreAdditive := pr1 A.
  Coercion Additive_PreAdditive : CategoryWithAdditiveStructure >-> PreAdditive.

  Definition make_Additive (PA : PreAdditive) (H : AdditiveStructure PA) : CategoryWithAdditiveStructure.
  Proof.
    exact (tpair _ PA H).
  Defined.

  (** A preadditive category is additive if it has a zero object and binary direct sums. *)
  Definition isAdditive (PA : PreAdditive) : hProp := hasZero PA ∧ hasBinDirectSums PA.

  Definition make_isAdditive (PA : PreAdditive) (H1 : hasZero PA) (H2 : hasBinDirectSums PA) : isAdditive PA := H1,,H2.

  (** Definition of additive categories *)

  Definition AdditiveCategory : UU := ∑ PA : PreAdditive, isAdditive PA.

  Coercion Additive_to_PreAdditive (A : AdditiveCategory) : PreAdditive := pr1 A.

  (** Accessor functions. *)
  Definition to_AdditiveStructure (A : CategoryWithAdditiveStructure) : AdditiveStructure A := pr2 A.

  Definition to_Zero (A : CategoryWithAdditiveStructure) : Zero A := dirprod_pr1 (to_AdditiveStructure A).

  Definition to_BinDirectSums (A : CategoryWithAdditiveStructure) : BinDirectSums A := dirprod_pr2 (to_AdditiveStructure A).

  Definition to_BinCoproducts (A : CategoryWithAdditiveStructure) : BinCoproducts A.
  Proof.
    intros X Y.
    exact (BinDirectSum_BinCoproduct A (to_BinDirectSums A X Y)).
  Defined.

  Definition to_BinProducts (A : CategoryWithAdditiveStructure) : BinProducts A.
  Proof.
    intros X Y.
    exact (BinDirectSum_BinProduct A (to_BinDirectSums A X Y)).
  Defined.


  Lemma to_Unel1' {A : CategoryWithAdditiveStructure} {a b : A} (BS : BinDirectSum a b) :
    to_In1 BS · to_Pr2 BS = ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite (to_Unel1 BS). apply PreAdditive_unel_zero.
  Qed.

  Lemma to_Unel2' {A : CategoryWithAdditiveStructure} {a b : A} (BS : BinDirectSum a b) :
    to_In2 BS · to_Pr1 BS = ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite (to_Unel2 BS). apply PreAdditive_unel_zero.
  Qed.

  Definition to_hasZero (A : AdditiveCategory) : hasZero A := pr1 (pr2 A).

  Definition to_hasBinDirectSums {A : AdditiveCategory} : hasBinDirectSums A := pr2 (pr2 A).

  Definition AdditiveZeroArrow {A : CategoryWithAdditiveStructure} (x y : ob A) : A⟦x, y⟧ :=
    ZeroArrow (to_Zero A) x y.

  Definition oppositeAdditiveCategory : AdditiveCategory -> AdditiveCategory.
  Proof.
    intros M.
    exists (oppositePreAdditive M). split.
    - use (hinhfun _ (to_hasZero M)). exact (λ Z, pr1 Z,, pr2 (pr2 Z),, pr1 (pr2 Z)).
    - intros A B. exact (hinhfun oppositeBinDirectSum (to_hasBinDirectSums A B)).
  Defined.

  Definition sums_lift (M:AdditiveCategory) {X:Type} (j : X -> ob M) : hProp :=
    zero_lifts M j ∧
    ∀ a b (S : BinDirectSum (j a) (j b)), ∃ x, z_iso (j x) (BinDirectSumOb S).

  Definition opp_sums_lift (M:AdditiveCategory) {X:Type} (j : X -> ob M) :
    sums_lift M j -> sums_lift (oppositeAdditiveCategory M) j.
  Proof.
    intros [hz su]. exists (opp_zero_lifts j hz).
    intros a b S. generalize (su a b (oppositeBinDirectSum S)). apply hinhfun.
    intros [s t]. exists s. exact (z_iso_inv (opp_z_iso t)).
  Defined.

  Definition induced_Additive (M : AdditiveCategory)
             {X:Type} (j : X -> ob M) (sum : sums_lift M j) : AdditiveCategory.
  Proof.
    exists (induced_PreAdditive M j). induction sum as [hz sum]. split.
    - use (hinhfun _ hz). intros [z iz]. exists z. split.
      + intros a. apply iz.
      + intros b. apply iz.
    - clear hz. intros a b. apply (squash_to_hProp (to_hasBinDirectSums (j a) (j b))); intros S.
      use (hinhfun _ (sum a b S)); intros [c t]; clear sum. set (S' := replaceSum S t).
      use tpair.
      + exists c. exact (pr21 S').
      + cbn. exact (pr2 S').
  Defined.


  Lemma induced_opposite_Additive {M:AdditiveCategory}
        {X:Type} (j : X -> ob M) (su : sums_lift M j) :
    oppositeAdditiveCategory (induced_Additive M j su) =
    induced_Additive (oppositeAdditiveCategory M) j (opp_sums_lift M j su).
  Proof.
    intros.
    apply (total2_paths2_f (induced_opposite_PreAdditive j)).
    apply propproperty.
  Defined.
*)
End def_additive.


(** * Quotient is additive
    We show that quotient of an additive category by certain subgroups is additive. In particular,
    this is used to show that the naive homotopy category of the category of chain complexes is an
    CategoryWithAdditiveStructure precategory. *)
Section additive_quot_additive.

  Variable A : CategoryWithAdditiveStructure.
  Hypothesis PAS : PreAdditiveSubabgrs A.
  Hypothesis PAC : PreAdditiveComps A PAS.

  Definition Quotcategory_Additive : CategoryWithAdditiveStructure.
  Proof.
    use make_Additive.
    - exact (Quotcategory_PreAdditive A PAS PAC).
    - use make_AdditiveStructure.
      + exact (Quotcategory_Zero A PAS PAC (to_Zero A)).
      + exact (Quotcategory_BinDirectSums A (to_BinDirectSums A) PAS PAC).
  Defined.

End additive_quot_additive.


(** * Kernels, Equalizers, Cokernels, and Coequalizers in CategoryWithAdditiveStructure categories *)
(** ** Introduction
Let f g : X --> Y be morphisms in an additive category. In this section we show that a
Cokernel of f - g is the Coequalizer of f and g, and vice versa. Similarly for Kernels
and equalizers.
 *)
Section additive_kernel_equalizers.

  Variable A : CategoryWithAdditiveStructure.

  Lemma AdditiveKernelToEqualizer_eq1 {x y : ob A} (f g : x --> y)
        (K : Kernel (to_Zero A) (to_binop _ _ f (to_inv g))) :
    KernelArrow K · f = KernelArrow K · g.
  Proof.
    use (to_rcan A (KernelArrow K · (to_inv g))).
    rewrite <- to_premor_linear'. rewrite <- to_premor_linear'.
    rewrite KernelCompZero.
    rewrite (@to_rinvax' A (to_Zero A)). rewrite ZeroArrow_comp_right.
    apply idpath.
  Qed.

  Lemma AdditiveKernelToEqualizer_isEqualizer {x y : ob A} (f g : x --> y)
             (K : Kernel (to_Zero A) (to_binop _ _ f (to_inv g))) :
    isEqualizer (*C:= categoryWithAbgrops_category _ *)f g (KernelArrow K) (AdditiveKernelToEqualizer_eq1 f g K).
  Proof.
    use make_isEqualizer.
    intros w h H'.
    use unique_exists.
    - use KernelIn.
      + exact h.
      + set (X := @to_premor_linear' A).
        rewrite X.
        etrans.
        { apply maponpaths_2.
          apply H'. }

        rewrite <- to_premor_linear'.
        rewrite (@to_rinvax' A (to_Zero A)). apply ZeroArrow_comp_right.
    - cbn. use KernelCommutes.
    - intros y0. apply to_has_homsets.
    - intros y0 X. cbn in X.
      use (KernelArrowisMonic _ K).
      etrans.
        2 : { apply pathsinv0. apply KernelCommutes.
        }
        exact X.
  Qed.

  Definition AdditiveKernelToEqualizer {x y : ob A} (f g : x --> y)
             (K : Kernel (to_Zero A) (to_binop _ _ f (to_inv g))) : Equalizer f g.
  Proof.
    use make_Equalizer.
    - exact K.
    - use (KernelArrow K).
    - exact (AdditiveKernelToEqualizer_eq1 f g K).
    - exact (AdditiveKernelToEqualizer_isEqualizer f g K).
  Defined.

  Lemma AdditiveEqualizerToKernel_eq1 {x y : ob A} (f g : x --> y) (E : Equalizer f g) :
    EqualizerArrow E · to_binop x y f (to_inv g) = ZeroArrow (to_Zero A) E y.
  Proof.
    set (X:= @to_premor_linear' A).
    rewrite X.
    use (to_rcan A (EqualizerArrow E · g)). rewrite to_assoc.
    rewrite to_lunax''. rewrite <- to_premor_linear'. rewrite (@to_linvax' A (to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite to_runax''. apply (EqualizerEqAr E).
  Qed.

  Lemma AdditiveEqualizerToKernel_isKernel {x y : ob A} (f g : x --> y) (E : Equalizer f g) :
    isKernel (to_Zero A) (EqualizerArrow E) (to_binop x y f (to_inv g))
             (AdditiveEqualizerToKernel_eq1 f g E).
  Proof.
    use make_isKernel.
    - intros w h H'.
      use unique_exists.
      + use (EqualizerIn E).
        * exact h.
        * use (to_rcan A (h · to_inv g)). rewrite <- to_premor_linear'.
          rewrite <- to_premor_linear'. rewrite (@to_rinvax' A (to_Zero A)).
          rewrite ZeroArrow_comp_right. exact H'.
      + cbn. use EqualizerCommutes.
      + intros y0. apply to_has_homsets.
      + intros y0 X. cbn in X.
        use (EqualizerArrowisMonic E).
        rewrite EqualizerCommutes.
        exact X.
  Qed.

  Definition AdditiveEqualizerToKernel {x y : ob A} (f g : x --> y) (E : Equalizer f g) :
    Kernel (to_Zero A) (to_binop _ _ f (to_inv g)).
  Proof.
    use make_Kernel.
    - exact E.
    - use (EqualizerArrow E).
    - exact (AdditiveEqualizerToKernel_eq1 f g E).
    - exact (AdditiveEqualizerToKernel_isKernel f g E).
  Defined.

  (** ** Correspondence between Cokernels and Coeqalizers *)

  Lemma AdditiveCokernelToCoequalizer_eq1 {x y : ob A} (f g : x --> y)
             (CK : Cokernel (to_Zero A) (to_binop _ _ f (to_inv g))) :
    f · CokernelArrow CK = g · CokernelArrow CK.
  Proof.
    use to_rcan.
    - exact (to_inv g · CokernelArrow CK).
    - rewrite <- to_postmor_linear'. rewrite <- to_postmor_linear'.
      rewrite (CokernelCompZero (to_Zero A) CK). apply pathsinv0.
      rewrite (@to_rinvax' A (to_Zero A)). apply ZeroArrow_comp_left.
  Qed.

  Lemma AdditiveCokernelToCoequalizer_isCoequalizer {x y : ob A} (f g : x --> y)
             (CK : Cokernel (to_Zero A) (to_binop _ _ f (to_inv g))) :
    isCoequalizer f g (CokernelArrow CK) (AdditiveCokernelToCoequalizer_eq1 f g CK).
  Proof.
    use make_isCoequalizer.
    intros w0 h H'.
    use unique_exists.
    - use CokernelOut.
      + exact h.
      + use to_rcan.
        * exact (g · h).
        * rewrite to_lunax''. rewrite <- to_postmor_linear'. rewrite to_assoc.
          rewrite (@to_linvax' A (to_Zero A)). rewrite to_runax''. apply H'.
    - cbn. use CokernelCommutes.
    - intros y0. apply to_has_homsets.
    - intros y0 X. cbn in X. cbn.
      use (CokernelArrowisEpi _ CK).
      rewrite CokernelCommutes.
      exact X.
  Qed.

  Definition AdditiveCokernelToCoequalizer {x y : ob A} (f g : x --> y)
             (CK : Cokernel (to_Zero A) (to_binop _ _ f (to_inv g))) : Coequalizer f g.
  Proof.
    use make_Coequalizer.
    - exact CK.
    - use (CokernelArrow CK).
    - exact (AdditiveCokernelToCoequalizer_eq1 f g CK).
    - exact (AdditiveCokernelToCoequalizer_isCoequalizer f g CK).
  Defined.

  Lemma AdditiveCoequalizerToCokernel_eq1 {x y : ob A} (f g : x --> y)
             (CE : Coequalizer f g) :
    to_binop x y f (to_inv g) · CoequalizerArrow CE = ZeroArrow (to_Zero A) x CE.
  Proof.
    rewrite to_postmor_linear'. rewrite CoequalizerEqAr. rewrite <- to_postmor_linear'.
    rewrite (@to_rinvax' A (to_Zero A)). apply ZeroArrow_comp_left.
  Qed.

  Lemma AdditiveCoequalizerToCokernel_isCokernel {x y : ob A} (f g : x --> y)
        (CE : Coequalizer f g) :
    isCokernel (to_Zero A) (to_binop x y f (to_inv g)) (CoequalizerArrow CE)
               (AdditiveCoequalizerToCokernel_eq1 f g CE).
  Proof.
    use make_isCokernel.
    - intros w h H'.
      use unique_exists.
      + use CoequalizerOut.
        * exact h.
        * use (to_rcan A (to_inv g · h)). rewrite <- to_postmor_linear'.
          rewrite <- to_postmor_linear'. rewrite (@to_rinvax' A (to_Zero A)).
          rewrite ZeroArrow_comp_left. exact H'.
      + cbn. use CoequalizerCommutes.
      + intros y0. apply to_has_homsets.
      + intros y0 X. cbn in X.
        use (CoequalizerArrowisEpi CE).
        rewrite CoequalizerCommutes.
        exact X.
  Qed.

  Definition AdditiveCoequalizerToCokernel {x y : ob A} (f g : x --> y)
             (CE : Coequalizer f g) : Cokernel (to_Zero A) (to_binop _ _ f (to_inv g)).
  Proof.
    use make_Cokernel.
    - exact CE.
    - use CoequalizerArrow.
    - exact (AdditiveCoequalizerToCokernel_eq1 f g CE).
    - exact (AdditiveCoequalizerToCokernel_isCokernel f g CE).
  Defined.

End additive_kernel_equalizers.


(** * Sum and in to BinDirectSum is Monic *)
Section additive_minus_monic.

  Variable A : CategoryWithAdditiveStructure.


  Lemma isMonic_to_binop_BinDirectSum1 {x y z : A} (f : Monic A x y) (g : x --> z)
        (DS : BinDirectSum y z) :
    isMonic (to_binop _ _ (f · to_In1 DS) (g · to_In2 DS)).
  Proof.
    use make_isMonic.
    intros x0 g0 h X.
    assert (e : g0 · to_binop x DS (f · to_In1 DS) (g · to_In2 DS) · to_Pr1 DS =
                h · to_binop x DS (f · to_In1 DS) (g · to_In2 DS) · to_Pr1 DS).
    {
      etrans. apply maponpaths_2.
      apply X.
      apply idpath.
    }
    rewrite <- assoc in e. rewrite <- assoc in e.
    set (XX:= @to_postmor_linear' A).
    rewrite XX in e.
    rewrite <- assoc in e. rewrite <- assoc in e.
    set (XXX := @to_IdIn1 A).



    rewrite (to_IdIn1 DS) in e.
    rewrite (to_Unel2' DS) in e. rewrite ZeroArrow_comp_right in e.
    rewrite id_right in e. use (MonicisMonic A f).
    rewrite to_runax'' in e. exact e.
  Qed.




  (** This version is used in AbelianPushoutPullback *)
  Lemma isMonic_to_binop_BinDirectSum1' {x y z : A} (f : Monic A x y) (g : x --> z)
        (DS : BinDirectSum y z) :
    isMonic (to_binop _ _ (f · to_In1 DS) (to_inv (g · to_In2 DS))).
  Proof.
    rewrite PreAdditive_invlcomp. use isMonic_to_binop_BinDirectSum1.
  Qed.


  Lemma isMonic_to_binop_BinDirectSum2 {x y z : A} (f : x --> y) (g : Monic A x z)
        (DS : BinDirectSum y z) :
    isMonic (to_binop _ _ (f · to_In1 DS) (g · to_In2 DS)).
  Proof.
    use make_isMonic.
    intros x0 g0 h X.
    assert (e : g0 · to_binop x DS (f · to_In1 DS) (g · to_In2 DS) · to_Pr2 DS =
                h · to_binop x DS (f · to_In1 DS) (g · to_In2 DS) · to_Pr2 DS).
    {
      rewrite X. apply idpath.
    }
    rewrite <- assoc in e. rewrite <- assoc in e.
    rewrite (@to_postmor_linear' A) in e.
    rewrite <- assoc in e. rewrite <- assoc in e. rewrite (@to_IdIn2 A _ _ _ _ _ _ _ DS) in e.
    rewrite (to_Unel1' DS) in e. rewrite ZeroArrow_comp_right in e.
    rewrite id_right in e. use (MonicisMonic A g).
    rewrite to_lunax'' in e. exact e.
  Qed.


  Lemma isEpi_to_binop_BinDirectSum1 {x y z : A} (f : Epi A y x) (g : z --> x)
        (DS : BinDirectSum y z) :
    isEpi (to_binop _ _ (to_Pr1 DS · f) (to_Pr2 DS · g)).
  Proof.
    use make_isEpi.
    intros z0 g0 h X.
    use (EpiisEpi A f).
    assert (e : to_In1 DS · to_binop DS x (to_Pr1 DS · f) (to_Pr2 DS · g) · g0 =
                to_In1 DS · to_binop DS x (to_Pr1 DS · f) (to_Pr2 DS · g) · h).
    {
      rewrite <- assoc. rewrite <- assoc. rewrite X. apply idpath.
    }
    rewrite to_premor_linear' in e. rewrite assoc in e. rewrite assoc in e.
    rewrite to_Unel1' in e. rewrite ZeroArrow_comp_left in e. rewrite to_runax'' in e.
    rewrite (to_IdIn1 DS) in e. rewrite id_left in e. apply e.
  Qed.

  (** This version is used in AbelianPushoutPullback *)
  Lemma isEpi_to_binop_BinDirectSum1' {x y z : A} (f : Epi A x z) (g : y --> z)
        (DS : BinDirectSum x y) :
    isEpi (to_binop _ _ (to_Pr1 DS · f) (to_inv (to_Pr2 DS · g))).
  Proof.
    rewrite PreAdditive_invrcomp. use isEpi_to_binop_BinDirectSum1.
  Qed.

  Lemma isEpi_to_binop_BinDirectSum2 {x y z : A} (f : y --> x) (g : Epi A z x)
        (DS : BinDirectSum y z) :
    isEpi (to_binop _ _ (to_Pr1 DS · f) (to_Pr2 DS · g)).
  Proof.
    use make_isEpi.
    intros z0 g0 h X.
    use (EpiisEpi A g).
    assert (e : to_In2 DS · to_binop DS x (to_Pr1 DS · f) (to_Pr2 DS · g) · g0 =
                to_In2 DS · to_binop DS x (to_Pr1 DS · f) (to_Pr2 DS · g) · h).
    {
      rewrite <- assoc. rewrite <- assoc. rewrite X. apply idpath.
    }
    rewrite to_premor_linear' in e. rewrite assoc in e. rewrite assoc in e.
    rewrite to_Unel2' in e. rewrite ZeroArrow_comp_left in e. rewrite to_lunax'' in e.
    rewrite (to_IdIn2 DS) in e. rewrite id_left in e. apply e.
  Qed.

End additive_minus_monic.


(** Kernels and cokernels in PreAdditive *)
Section monics_and_epis_in_additive.

  Variable A : CategoryWithAdditiveStructure.

  Lemma to_isMonic {x y : ob A} (f : x --> y)
        (H : ∏ (z : ob A) (g : z --> x) (H : g · f = ZeroArrow (to_Zero A) _ _),
             g = ZeroArrow (to_Zero A) _ _ ) : isMonic f.
  Proof.
    use make_isMonic.
    intros x0 g h X.
    set (tmp := H x0 (to_binop _ _ g (to_inv h))).
    use (to_rcan A (to_inv h)). rewrite (@to_rinvax' A (to_Zero A)). apply tmp. clear tmp.
    rewrite to_postmor_linear'.
    use (to_rcan A (h · f)). rewrite to_assoc. rewrite <- to_postmor_linear'.
    rewrite (@to_linvax' A (to_Zero A)). rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite to_lunax''. exact X.
  Qed.

  Lemma to_isEpi {x y : ob A} (f : x --> y)
        (H : ∏ (z : ob A) (g : y --> z) (H : f · g = ZeroArrow (to_Zero A) _ _),
             g = ZeroArrow (to_Zero A) _ _ ) : isEpi f.
  Proof.
    use make_isEpi.
    intros x0 g h X.
    set (tmp := H x0 (to_binop _ _ g (to_inv h))).
    use (to_rcan A (to_inv h)). rewrite (@to_rinvax' A (to_Zero A)). apply tmp. clear tmp.
    rewrite to_premor_linear'.
    use (to_rcan A (f · h)). rewrite to_assoc. rewrite <- to_premor_linear'.
    rewrite (@to_linvax' A (to_Zero A)). rewrite ZeroArrow_comp_right.
    rewrite to_runax''. rewrite to_lunax''. exact X.
  Qed.

End monics_and_epis_in_additive.
