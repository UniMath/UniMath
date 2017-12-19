(** * Additive categories. *)
(** * Contents
- Definition of additive categories
- Quotient of an additive category is additive
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.

Require Import UniMath.CategoryTheory.limits.zero.
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

  (** A preadditive category is additive if it has a zero object and binary direct sums. *)
  Definition isAdditive (PA : PreAdditive) : UU := (Zero PA) × (BinDirectSums PA).

  Definition mk_isAdditive (PA : PreAdditive) (H1 : Zero PA) (H2 : BinDirectSums PA) :
    isAdditive PA.
  Proof.
    exact (H1,,H2).
  Defined.

  (** Definition of additive categories *)
  Definition Additive : UU := ∑ PA : PreAdditive, isAdditive PA.

  Definition Additive_PreAdditive (A : Additive) : PreAdditive := pr1 A.
  Coercion Additive_PreAdditive : Additive >-> PreAdditive.

  Definition mk_Additive (PA : PreAdditive) (H : isAdditive PA) : Additive.
  Proof.
    exact (tpair _ PA H).
  Defined.

  (** Accessor functions. *)
  Definition to_isAdditive (A : Additive) : isAdditive A := pr2 A.

  Definition to_Zero (A : Additive) : Zero A := dirprod_pr1 (to_isAdditive A).

  Definition to_BinDirectSums (A : Additive) : BinDirectSums A := dirprod_pr2 (to_isAdditive A).

  Definition to_BinCoproducts (A : Additive) : BinCoproducts A.
  Proof.
    intros X Y.
    exact (BinDirectSum_BinCoproduct A (to_BinDirectSums A X Y)).
  Defined.

  Definition to_BinProducts (A : Additive) : BinProducts A.
  Proof.
    intros X Y.
    exact (BinDirectSum_BinProduct A (to_BinDirectSums A X Y)).
  Defined.


  Lemma to_Unel1' {A : Additive} {a b : A} (BS : BinDirectSum A a b) :
    to_In1 A BS · to_Pr2 A BS = ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite (to_Unel1 A BS). apply PreAdditive_unel_zero.
  Qed.

  Lemma to_Unel2' {A : Additive} {a b : A} (BS : BinDirectSum A a b) :
    to_In2 A BS · to_Pr1 A BS = ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite (to_Unel2 A BS). apply PreAdditive_unel_zero.
  Qed.

  Definition AdditiveZeroArrow {A : Additive} (x y : ob A) : A⟦x, y⟧ :=
    ZeroArrow (to_Zero A) x y.

End def_additive.


(** * Quotient is additive
    We show that quotient of an additive category by certain subgroups is additive. In particular,
    this is used to show that the naive homotopy category of the category of chain complexes is an
    Additive precategory. *)
Section additive_quot_additive.

  Variable A : Additive.
  Hypothesis PAS : PreAdditiveSubabgrs A.
  Hypothesis PAC : PreAdditiveComps A PAS.

  Definition Quotcategory_Additive : Additive.
  Proof.
    use mk_Additive.
    - exact (Quotcategory_PreAdditive A PAS PAC).
    - use mk_isAdditive.
      + exact (Quotcategory_Zero A PAS PAC (to_Zero A)).
      + exact (Quotcategory_BinDirectSums A (to_BinDirectSums A) PAS PAC).
  Defined.

End additive_quot_additive.


(** * Kernels, Equalizers, Cokernels, and Coequalizers in Additive categories *)
(** ** Introduction
Let f g : X --> Y be morphisms in an additive category. In this section we show that a
Cokernel of f - g is the Coequalizer of f and g, and vice versa. Similarly for Kernels
and equalizers.
 *)
Section additive_kernel_equalizers.

  Variable A : Additive.

  Lemma AdditiveKernelToEqualizer_eq1 {x y : ob A} (f g : x --> y)
        (K : Kernel (to_Zero A) (to_binop _ _ f (to_inv g))) :
    KernelArrow K · f = KernelArrow K · g.
  Proof.
    use (to_rcan A (KernelArrow K · (to_inv g))).
    rewrite <- to_premor_linear'. rewrite <- to_premor_linear'.
    rewrite KernelCompZero. rewrite (@to_rinvax' A (to_Zero A)). rewrite ZeroArrow_comp_right.
    apply idpath.
  Qed.

  Lemma AdditiveKernelToEqualizer_isEqualizer {x y : ob A} (f g : x --> y)
             (K : Kernel (to_Zero A) (to_binop _ _ f (to_inv g))) :
    isEqualizer f g (KernelArrow K) (AdditiveKernelToEqualizer_eq1 f g K).
  Proof.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.
    - use KernelIn.
      + exact h.
      + rewrite to_premor_linear'. rewrite H'. rewrite <- to_premor_linear'.
        rewrite (@to_rinvax' A (to_Zero A)). apply ZeroArrow_comp_right.
    - cbn. use KernelCommutes.
    - intros y0. apply to_has_homsets.
    - intros y0 X. cbn in X.
      use (KernelArrowisMonic _ K). rewrite KernelCommutes. exact X.
  Qed.

  Definition AdditiveKernelToEqualizer {x y : ob A} (f g : x --> y)
             (K : Kernel (to_Zero A) (to_binop _ _ f (to_inv g))) : Equalizer f g.
  Proof.
    use mk_Equalizer.
    - exact K.
    - use (KernelArrow K).
    - exact (AdditiveKernelToEqualizer_eq1 f g K).
    - exact (AdditiveKernelToEqualizer_isEqualizer f g K).
  Defined.

  Lemma AdditiveEqualizerToKernel_eq1 {x y : ob A} (f g : x --> y) (E : Equalizer f g) :
    EqualizerArrow E · to_binop x y f (to_inv g) = ZeroArrow (to_Zero A) E y.
  Proof.
    rewrite to_premor_linear'.
    use (to_rcan A (EqualizerArrow E · g)). rewrite to_assoc.
    rewrite to_lunax''. rewrite <- to_premor_linear'. rewrite (@to_linvax' A (to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite to_runax''. apply (EqualizerEqAr E).
  Qed.

  Lemma AdditiveEqualizerToKernel_isKernel {x y : ob A} (f g : x --> y) (E : Equalizer f g) :
    isKernel (to_Zero A) (EqualizerArrow E) (to_binop x y f (to_inv g))
             (AdditiveEqualizerToKernel_eq1 f g E).
  Proof.
    use mk_isKernel.
    - apply to_has_homsets.
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
    use mk_Kernel.
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
    use mk_isCoequalizer.
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
    use mk_Coequalizer.
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
    use mk_isCokernel.
    - apply to_has_homsets.
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
    use mk_Cokernel.
    - exact CE.
    - use CoequalizerArrow.
    - exact (AdditiveCoequalizerToCokernel_eq1 f g CE).
    - exact (AdditiveCoequalizerToCokernel_isCokernel f g CE).
  Defined.

End additive_kernel_equalizers.


(** * Sum and in to BinDirectSum is Monic *)
Section additive_minus_monic.

  Variable A : Additive.

  Lemma isMonic_to_binop_BinDirectSum1 {x y z : A} (f : Monic A x y) (g : x --> z)
        (DS : BinDirectSum A y z) :
    isMonic (to_binop _ _ (f · to_In1 _ DS) (g · to_In2 _ DS)).
  Proof.
    use mk_isMonic.
    intros x0 g0 h X.
    assert (e : g0 · to_binop x DS (f · to_In1 A DS) (g · to_In2 A DS) · to_Pr1 A DS =
                h · to_binop x DS (f · to_In1 A DS) (g · to_In2 A DS) · to_Pr1 A DS).
    {
      rewrite X. apply idpath.
    }
    rewrite <- assoc in e. rewrite <- assoc in e. rewrite to_postmor_linear' in e.
    rewrite <- assoc in e. rewrite <- assoc in e. rewrite (to_IdIn1 A DS) in e.
    rewrite (to_Unel2' DS) in e. rewrite ZeroArrow_comp_right in e.
    rewrite id_right in e. use (MonicisMonic A f).
    rewrite to_runax'' in e. exact e.
  Qed.

  (** This version is used in AbelianPushoutPullback *)
  Lemma isMonic_to_binop_BinDirectSum1' {x y z : A} (f : Monic A x y) (g : x --> z)
        (DS : BinDirectSum A y z) :
    isMonic (to_binop _ _ (f · to_In1 _ DS) (to_inv (g · to_In2 _ DS))).
  Proof.
    rewrite PreAdditive_invlcomp. use isMonic_to_binop_BinDirectSum1.
  Qed.

  Lemma isMonic_to_binop_BinDirectSum2 {x y z : A} (f : x --> y) (g : Monic A x z)
        (DS : BinDirectSum A y z) :
    isMonic (to_binop _ _ (f · to_In1 _ DS) (g · to_In2 _ DS)).
  Proof.
    use mk_isMonic.
    intros x0 g0 h X.
    assert (e : g0 · to_binop x DS (f · to_In1 A DS) (g · to_In2 A DS) · to_Pr2 A DS =
                h · to_binop x DS (f · to_In1 A DS) (g · to_In2 A DS) · to_Pr2 A DS).
    {
      rewrite X. apply idpath.
    }
    rewrite <- assoc in e. rewrite <- assoc in e. rewrite to_postmor_linear' in e.
    rewrite <- assoc in e. rewrite <- assoc in e. rewrite (to_IdIn2 A DS) in e.
    rewrite (to_Unel1' DS) in e. rewrite ZeroArrow_comp_right in e.
    rewrite id_right in e. use (MonicisMonic A g).
    rewrite to_lunax'' in e. exact e.
  Qed.

  Lemma isEpi_to_binop_BinDirectSum1 {x y z : A} (f : Epi A y x) (g : z --> x)
        (DS : BinDirectSum A y z) :
    isEpi (to_binop _ _ (to_Pr1 _ DS · f) (to_Pr2 _ DS · g)).
  Proof.
    use mk_isEpi.
    intros z0 g0 h X.
    use (EpiisEpi A f).
    assert (e : to_In1 A DS · to_binop DS x (to_Pr1 A DS · f) (to_Pr2 A DS · g) · g0 =
                to_In1 A DS · to_binop DS x (to_Pr1 A DS · f) (to_Pr2 A DS · g) · h).
    {
      rewrite <- assoc. rewrite <- assoc. rewrite X. apply idpath.
    }
    rewrite to_premor_linear' in e. rewrite assoc in e. rewrite assoc in e.
    rewrite to_Unel1' in e. rewrite ZeroArrow_comp_left in e. rewrite to_runax'' in e.
    rewrite (to_IdIn1 A DS) in e. rewrite id_left in e. apply e.
  Qed.

  (** This version is used in AbelianPushoutPullback *)
  Lemma isEpi_to_binop_BinDirectSum1' {x y z : A} (f : Epi A x z) (g : y --> z)
        (DS : BinDirectSum A x y) :
    isEpi (to_binop _ _ (to_Pr1 _ DS · f) (to_inv (to_Pr2 _ DS · g))).
  Proof.
    rewrite PreAdditive_invrcomp. use isEpi_to_binop_BinDirectSum1.
  Qed.

  Lemma isEpi_to_binop_BinDirectSum2 {x y z : A} (f : y --> x) (g : Epi A z x)
        (DS : BinDirectSum A y z) :
    isEpi (to_binop _ _ (to_Pr1 _ DS · f) (to_Pr2 _ DS · g)).
  Proof.
    use mk_isEpi.
    intros z0 g0 h X.
    use (EpiisEpi A g).
    assert (e : to_In2 A DS · to_binop DS x (to_Pr1 A DS · f) (to_Pr2 A DS · g) · g0 =
                to_In2 A DS · to_binop DS x (to_Pr1 A DS · f) (to_Pr2 A DS · g) · h).
    {
      rewrite <- assoc. rewrite <- assoc. rewrite X. apply idpath.
    }
    rewrite to_premor_linear' in e. rewrite assoc in e. rewrite assoc in e.
    rewrite to_Unel2' in e. rewrite ZeroArrow_comp_left in e. rewrite to_lunax'' in e.
    rewrite (to_IdIn2 A DS) in e. rewrite id_left in e. apply e.
  Qed.

End additive_minus_monic.


(** Kernels and cokernels in PreAdditive *)
Section monics_and_epis_in_additive.

  Variable A : Additive.

  Lemma to_isMonic {x y : ob A} (f : x --> y)
        (H : ∏ (z : ob A) (g : z --> x) (H : g · f = ZeroArrow (to_Zero A) _ _),
             g = ZeroArrow (to_Zero A) _ _ ) : isMonic f.
  Proof.
    use mk_isMonic.
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
    use mk_isEpi.
    intros x0 g h X.
    set (tmp := H x0 (to_binop _ _ g (to_inv h))).
    use (to_rcan A (to_inv h)). rewrite (@to_rinvax' A (to_Zero A)). apply tmp. clear tmp.
    rewrite to_premor_linear'.
    use (to_rcan A (f · h)). rewrite to_assoc. rewrite <- to_premor_linear'.
    rewrite (@to_linvax' A (to_Zero A)). rewrite ZeroArrow_comp_right.
    rewrite to_runax''. rewrite to_lunax''. exact X.
  Qed.

End monics_and_epis_in_additive.
