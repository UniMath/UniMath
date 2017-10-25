(** * Cohomology of complexes *)
(** ** Contents
- Cohomology functor C(A) -> C(A)
- Alternative definition of cohomology complex
- Quasi-isomorphism in C(A)
- Cohomology functor K(A) -> C(A)
 - Construction of K(A) -> C(A)
 - K(A) -> C(A) is additive
 - Quasi-isomorphisms in K(A)
- Complex of kernels and complex of cokernels
 - Construction of the complexes
 - Cohomology and morphisms from cokernels to kernels
 *)

Unset Kernel Term Sharing.

Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Import UniMath.CategoryTheory.AdditiveFunctors.

Require Import UniMath.HomologicalAlgebra.Complexes.
Require Import UniMath.HomologicalAlgebra.KA.

Open Scope hz_scope.
Local Opaque hz isdecrelhzeq hzplus iscommrngops ishinh.

(** * Cohomology functor *)
(** ** Introduction
   In this section we define the cohomology functor H : C(A) -> C(A). Suppose A is the category of
   abelian groups. Then H sends a complex
                     ... -> X^{i-1} -> X^i -> X^{i+1} -> ...
   to the complex
     ... -> Ker d^{i-1} / Im d^{i-2} -> Ker d^i / Im d^{i-1} -> Ker d^{i+1} / Im d^i -> ...
   where the differentials are given by zero morphisms. A morphism f : X -> Y is sent to the induced
   morphism. That is, f^i : X^i -> Y^i induces a morphism #(H f)^i : ker d^i_X / Im d^{i-1}_X ->
   ker d^i_Y / Im d^{i-1}_Y# $(H f)^i : ker d^i_X / Im d^{i-1}_X -> ker d^i_Y / Im d^{i-1}_Y$ as one
   can check.

   In category theory, there are two isomorphic ways to define the cohomology complex. We use the
   following definition. The ith cohomology is defined to be the cokernel of the morphism X^{i-1} ->
   Ker d^i, the KernelIn map of Ker d^i obtained by using the fact that d^{i-1} · d^i = 0. If f is
   a morphism of complexes, then by using properties of kernelin and cokernelout we construct the
   induced morphism.

   The map on complexes is constructed in [CohomologyComplex]. The map on morphisms is constructed
   in [CohomologyMorphism]. The functor_data is contructed from these in [CohomologyFunctor_data],
   and finally in [CohomologyFunctor] we prove that this data defines a functor.
*)
Section def_cohomology_complex.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  (** ** Cohomology complex *)

  Local Lemma CohomologyComplex_KernelIn_eq' (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (transportf (λ x : pr1 hz, A ⟦ C (i - 1), C x ⟧) (hzrminusplus i 1) (Diff C (i - 1)))
      · (Diff C i) = ZeroArrow (to_Zero A) _ _.
  Proof.
    induction (hzrminusplus i 1). cbn. unfold idfun.
    apply (DSq (AbelianToAdditive A hs) C (i - 1)).
  Qed.

  Local Lemma CohomologyComplex_KernelIn_eq (C : Complex (AbelianToAdditive A hs)) (i : hz) :
      (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                  (Diff C (i - 1))) · (Diff C i) = ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite <- functtransportf. cbn.
    induction (hzrminusplus i 1). cbn. unfold idfun.
    apply (DSq (AbelianToAdditive A hs) C (i - 1)).
  Qed.

  Definition CohomologyComplex (C : (ComplexPreCat_AbelianPreCat A hs)) :
    ComplexPreCat_AbelianPreCat A hs.
  Proof.
    cbn in *.
    use mk_Complex.
    - intros i.
      exact (Abelian.Cokernel (KernelIn (to_Zero A) (Abelian.Kernel (Diff C i)) _ _
                                        (CohomologyComplex_KernelIn_eq C i))).
    - intros i. exact (ZeroArrow ((to_Zero A)) _ _).
    - intros i. cbn. apply ZeroArrow_comp_left.
  Defined.

  (** ** Cohomology morphism *)

  Local Lemma CohomologyMorphism_KernelIn_comm {C1 C2 : Complex (AbelianToAdditive A hs)}
        (f : Morphism C1 C2) (i : hz) :
    KernelArrow (Kernel (Diff C1 i)) · MMor f i · Diff C2 i =
    ZeroArrow (to_Zero A) (Kernel (Diff C1 i)) (C2 (i + 1)).
  Proof.
    rewrite <- assoc. set (tmp := MComm f i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma CohomolohyMorphism_Ker_comm {C1 C2 : Complex (AbelianToAdditive A hs)}
        (f : Morphism C1 C2) (i : hz) :
    (KernelIn (to_Zero A) (Kernel (Diff C1 i)) (C1 (i - 1))
              (transportf (precategory_morphisms (C1 (i - 1))) (maponpaths C1 (hzrminusplus i 1))
                          (Diff C1 (i - 1)))
              (CohomologyComplex_KernelIn_eq C1 i))
      · (KernelIn (to_Zero A) (Kernel (Diff C2 i)) (Kernel (Diff C1 i))
                   (KernelArrow (Kernel (Diff C1 i)) · MMor f i)
                   (CohomologyMorphism_KernelIn_comm f i)) =
    (MMor f (i - 1))
      · (KernelIn (to_Zero A) (Kernel (Diff C2 i)) (C2 (i - 1))
                   (transportf (precategory_morphisms (C2 (i - 1)))
                               (maponpaths C2 (hzrminusplus i 1)) (Diff C2 (i - 1)))
                   (CohomologyComplex_KernelIn_eq C2 i)).
  Proof.
    apply (KernelArrowisMonic (to_Zero A) (Kernel (Diff C2 i))).
    rewrite <- assoc. rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
    cbn. rewrite <- transport_target_postcompose. cbn.
    set (tmp := MComm f (i - 1)). cbn in tmp. rewrite tmp. clear tmp.
    rewrite assoc. rewrite KernelCommutes.
    induction (hzrminusplus i 1). cbn. unfold idfun. apply idpath.
  Qed.

  Local Lemma CohomologyMorphism_Ker_Coker_Zero {C1 C2 : Complex (AbelianToAdditive A hs)}
        (f : Morphism C1 C2) (i : hz) :
    (KernelIn (to_Zero A) (Kernel (Diff C1 i)) (C1 (i - 1))
              (transportf (precategory_morphisms (C1 (i - 1))) (maponpaths C1 (hzrminusplus i 1))
                          (Diff C1 (i - 1))) (CohomologyComplex_KernelIn_eq C1 i))
      · ((KernelIn (to_Zero A) (Kernel (Diff C2 i)) (Kernel (Diff C1 i))
                    (KernelArrow (Kernel (Diff C1 i)) · MMor f i)
                    (CohomologyMorphism_KernelIn_comm f i))
            ·  (CokernelArrow
                   (Cokernel
                      (KernelIn (to_Zero A) (Kernel (Diff C2 i)) (C2 (i - 1))
                                (transportf (precategory_morphisms (C2 (i - 1)))
                                            (maponpaths C2 (hzrminusplus i 1))
                                            (Diff C2 (i - 1)))
                                (CohomologyComplex_KernelIn_eq C2 i))))) =
    ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite assoc. rewrite CohomolohyMorphism_Ker_comm. rewrite <- assoc.
    rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Definition CohomologyMorphism_Mor {C1 C2 : Complex (AbelianToAdditive A hs)} (f : Morphism C1 C2)
             (i : hz) :
    AbelianToAdditive A hs ⟦((CohomologyComplex C1) : Complex (AbelianToAdditive A hs)) i,
                            ((CohomologyComplex C2) : Complex (AbelianToAdditive A hs)) i⟧.
  Proof.
    cbn.
    use CokernelOut.
    - use compose.
      + exact (Kernel (Diff C2 i)).
      + use KernelIn.
        * use compose.
          -- exact (C1 i).
          -- use KernelArrow.
          -- exact (MMor f i).
        * exact (CohomologyMorphism_KernelIn_comm f i).
      + use CokernelArrow.
    - apply CohomologyMorphism_Ker_Coker_Zero.
  Defined.

  Local Lemma CohomologyMorphism_Mor_comm {C1 C2 : Complex (AbelianToAdditive A hs)}
        (f : Morphism C1 C2) (i : hz) :
    (CohomologyMorphism_Mor f i)
      · (Diff ((CohomologyComplex C2) : Complex (AbelianToAdditive A hs)) i) =
    (Diff ((CohomologyComplex C1) : Complex (AbelianToAdditive A hs)) i)
      · (CohomologyMorphism_Mor f (i + 1)).
  Proof.
    cbn. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition CohomologyMorphism {C1 C2 : Complex (AbelianToAdditive A hs)} (f : Morphism C1 C2) :
    Morphism (CohomologyComplex C1) (CohomologyComplex C2).
  Proof.
    use mk_Morphism.
    - intros i. exact (CohomologyMorphism_Mor f i).
    - intros i. exact (CohomologyMorphism_Mor_comm f i).
  Defined.

  (** ** Cohomology functor *)

  Definition CohomologyFunctor_data :
    functor_data (ComplexPreCat_AbelianPreCat A hs) (ComplexPreCat_AbelianPreCat A hs).
  Proof.
    use tpair.
    - cbn. intros C. exact (CohomologyComplex C).
    - cbn. intros C1 C2 f. exact (CohomologyMorphism f).
  Defined.

  Local Lemma CohomologyFunctor_id (C : (ComplexPreCat_AbelianPreCat A hs)) :
    CohomologyMorphism (IdMor C) = IdMor (CohomologyComplex C).
  Proof.
    cbn in *.
    use MorphismEq.
    intros i. cbn. apply pathsinv0.
    apply CokernelEndo_is_identity. unfold CohomologyMorphism_Mor. rewrite CokernelCommutes.
    rewrite <- id_left. apply cancel_postcomposition.
    use KernelInsEq. rewrite KernelCommutes.
    rewrite id_left. rewrite id_right. apply idpath.
  Qed.

  Local Lemma CohomologyFunctor_assoc {C1 C2 C3 : (ComplexPreCat_AbelianPreCat A hs)}
        (f : (ComplexPreCat_AbelianPreCat A hs)⟦C1, C2⟧)
        (g : (ComplexPreCat_AbelianPreCat A hs)⟦C2, C3⟧) :
    # CohomologyFunctor_data (f · g) = # CohomologyFunctor_data f · # CohomologyFunctor_data g.
  Proof.
    cbn in *.
    use MorphismEq.
    intros i. cbn. unfold CohomologyMorphism_Mor. use CokernelOutsEq. rewrite CokernelCommutes.
    rewrite assoc. rewrite CokernelCommutes.
    rewrite <- assoc. rewrite CokernelCommutes.
    rewrite assoc. apply cancel_postcomposition.
    use KernelInsEq. rewrite KernelCommutes.
    rewrite <- assoc. rewrite KernelCommutes.
    rewrite assoc. rewrite KernelCommutes.
    cbn. rewrite assoc. apply idpath.
  Qed.

  Definition CohomologyFunctor :
    functor (ComplexPreCat_AbelianPreCat A hs) (ComplexPreCat_AbelianPreCat A hs).
  Proof.
    use tpair.
    - exact CohomologyFunctor_data.
    - cbn. split.
      + intros C. cbn. exact (CohomologyFunctor_id C).
      + intros C1 C2 C3 f g. exact (CohomologyFunctor_assoc f g).
  Defined.

End def_cohomology_complex.


(** * Alternative definition of Cohomology complex *)
(** ** Introduction
   We construct an isomorphic alternative of [CohomologyComplex].
*)
Section def_cohomology'_complex.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  Definition CohomologyComplex' (C : (ComplexPreCat_AbelianPreCat A hs)) :
    (ComplexPreCat_AbelianPreCat A hs).
  Proof.
    cbn in *.
    use mk_Complex.
    - intros i.
      exact (Kernel (CokernelOut
                       (to_Zero A) (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                         (maponpaths C (hzrminusplus i 1))
                                                         (Diff C (i - 1)))) _ (Diff C i)
                       (CohomologyComplex_KernelIn_eq A hs C i))).
    - intros i. exact (ZeroArrow (to_Zero A) _ _).
    - intros i. apply ZeroArrow_comp_left.
  Defined.

  Local Lemma CohomologyComplexIso_eq1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (factorization1_monic
       A (transportf (precategory_morphisms (C (i - 1)))
                     (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
      · (Diff C i) = ZeroArrow (to_Zero A) _ _.
  Proof.
    use (EpiisEpi A (factorization1_epi A hs (transportf (precategory_morphisms (C (i - 1)))
                                                         (maponpaths C (hzrminusplus i 1))
                                                         (Diff C (i - 1))))).
    rewrite assoc. rewrite <- factorization1. rewrite ZeroArrow_comp_right.
    exact (CohomologyComplex_KernelIn_eq A hs C i).
  Qed.

  Local Lemma CohomologyComplexIso_eq1' (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (factorization1_epi
       A hs (transportf (precategory_morphisms (C (i - 1)))
                        (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
      · (factorization1_monic
            A (transportf (precategory_morphisms (C (i - 1)))
                          (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
      · (Diff C i) = ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite <- factorization1. exact (CohomologyComplex_KernelIn_eq A hs C i).
  Qed.

  Local Lemma CohomologyComplexIso_eq2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                (Diff C (i - 1)))
      · (factorization2_epi A (Diff C i)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    use (MonicisMonic A (factorization2_monic A hs (Diff C i))).
    rewrite <- assoc.
    set (tmp := factorization1 hs (Diff C i)). cbn in tmp. cbn. rewrite <- assoc in tmp.
    rewrite <- tmp. clear tmp. rewrite ZeroArrow_comp_left.
    exact (CohomologyComplex_KernelIn_eq A hs C i).
  Qed.

  Local Lemma CohomologyComplexIso_eq2' (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                (Diff C (i - 1)))
      · ((factorization2_epi A (Diff C i)) · (factorization2_monic A hs (Diff C i))) =
    ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite <- factorization2. exact (CohomologyComplex_KernelIn_eq A hs C i).
  Qed.

  Local Lemma CohomologyComplexIso_KerCokerIso_eq1 {x y : A} {f : A⟦x, y⟧}
        (CK1 CK2 : cokernels.Cokernel (to_Zero A) f)
        (K1 : kernels.Kernel (to_Zero A) (CokernelArrow CK1))
        (K2 : kernels.Kernel (to_Zero A) (CokernelArrow CK2)) :
    KernelArrow K1 · CokernelArrow CK2 = ZeroArrow (to_Zero A) K1 CK2.
  Proof.
    assert (e1 : CokernelArrow CK2 =
                 (CokernelArrow CK1) · (CokernelOut (to_Zero A) CK1 CK2 (CokernelArrow CK2)
                                                     (CokernelCompZero (to_Zero A) CK2))).
    {
      rewrite CokernelCommutes. apply idpath.
    }
    rewrite e1. rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma CohomologyComplexIso_KerCokerIso_eq2 {x y : A} {f : A⟦x, y⟧}
        (CK1 CK2 : cokernels.Cokernel (to_Zero A) f)
        (K1 : kernels.Kernel (to_Zero A) (CokernelArrow CK1))
        (K2 : kernels.Kernel (to_Zero A) (CokernelArrow CK2)) :
    KernelArrow K2 · CokernelArrow CK1 = ZeroArrow (to_Zero A) K2 CK1.
  Proof.
    assert (e1 : CokernelArrow CK1 =
                 (CokernelArrow CK2) · (CokernelOut (to_Zero A) CK2 CK1 (CokernelArrow CK1)
                                                     (CokernelCompZero (to_Zero A) CK1))).
    {
      rewrite CokernelCommutes. apply idpath.
    }
    rewrite e1. rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Definition CohomologyComplexIso_KerCokerIso {x y : A} {f : A⟦x, y⟧}
        (CK1 CK2 : cokernels.Cokernel (to_Zero A) f)
        (K1 : kernels.Kernel (to_Zero A) (CokernelArrow CK1))
        (K2 : kernels.Kernel (to_Zero A) (CokernelArrow CK2)) : iso K1 K2.
  Proof.
    use isopair.
    - use KernelIn.
      + use KernelArrow.
      + exact (CohomologyComplexIso_KerCokerIso_eq1 CK1 CK2 K1 K2).
    - use is_iso_qinv.
      + use KernelIn.
        * use KernelArrow.
        * exact (CohomologyComplexIso_KerCokerIso_eq2 CK1 CK2 K1 K2).
      + split.
        * use (KernelArrowisMonic (to_Zero A) K1).
          rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
          rewrite id_left. apply idpath.
        * use (KernelArrowisMonic (to_Zero A) K2).
          rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
          rewrite id_left. apply idpath.
  Qed.

  Local Lemma CohomologyComplexIso_CokerKerIso_eq1 {x y : A} {f : A⟦x, y⟧}
        (K1 K2 : kernels.Kernel (to_Zero A) f)
        (CK1 : cokernels.Cokernel (to_Zero A) (KernelArrow K1))
        (CK2 : cokernels.Cokernel (to_Zero A) (KernelArrow K2)) :
    KernelArrow K1 · CokernelArrow CK2 = ZeroArrow (to_Zero A) K1 CK2.
  Proof.
    assert (e1 : KernelArrow K1 = (KernelIn (to_Zero A) K2 K1 (KernelArrow K1)
                                            (KernelCompZero (to_Zero A) K1)) · (KernelArrow K2)).
    {
      rewrite KernelCommutes. apply idpath.
    }
    rewrite e1. rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma CohomologyComplexIso_CokerKerIso_eq2 {x y : A} {f : A⟦x, y⟧}
        (K1 K2 : kernels.Kernel (to_Zero A) f)
        (CK1 : cokernels.Cokernel (to_Zero A) (KernelArrow K1))
        (CK2 : cokernels.Cokernel (to_Zero A) (KernelArrow K2)) :
    KernelArrow K2 · CokernelArrow CK1 = ZeroArrow (to_Zero A) K2 CK1.
  Proof.
    assert (e2 : KernelArrow K2 = (KernelIn (to_Zero A) K1 K2 (KernelArrow K2)
                                            (KernelCompZero (to_Zero A) K2)) · (KernelArrow K1)).
    {
      rewrite KernelCommutes. apply idpath.
    }
    rewrite e2. rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Definition CohomologyComplexIso_CokerKerIso {x y : A} {f : A⟦x, y⟧}
        (K1 K2 : kernels.Kernel (to_Zero A) f)
        (CK1 : cokernels.Cokernel (to_Zero A) (KernelArrow K1))
        (CK2 : cokernels.Cokernel (to_Zero A) (KernelArrow K2)) : iso CK1 CK2.
  Proof.
    use isopair.
    - use CokernelOut.
      + use CokernelArrow.
      + exact (CohomologyComplexIso_CokerKerIso_eq1 K1 K2 CK1 CK2).
    - use is_iso_qinv.
      + use CokernelOut.
        * use CokernelArrow.
        * exact (CohomologyComplexIso_CokerKerIso_eq2 K1 K2 CK1 CK2).
      + split.
        * use (CokernelArrowisEpi (to_Zero A) CK1).
          rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
          rewrite id_right. apply idpath.
        * use (CokernelArrowisEpi (to_Zero A) CK2).
          rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
          rewrite id_right. apply idpath.
  Qed.

  Local Lemma CohomologyComplexIso_isMonic (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    isMonic K1.
  Proof.
    intros K1.
    use isMonic_postcomp.
    - exact (C i).
    - use KernelArrow.
    - unfold K1. rewrite KernelCommutes. apply MonicisMonic.
  Qed.

  Local Lemma CohomologyComplexIso_isEpi (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK1 := CokernelOut
                 (to_Zero A)
                 (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                       (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 _ _ (CohomologyComplexIso_eq2 C i) in
    isEpi CK1.
  Proof.
    intros CK1.
    use isEpi_precomp.
    - exact (C i).
    - use CokernelArrow.
    - unfold CK1. rewrite CokernelCommutes. apply EpiisEpi.
  Qed.

  Local Lemma CohomologyComplexIso_mor_eq1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    (factorization1_epi
       A hs (transportf (precategory_morphisms (C (i - 1)))
                        (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1)))) · K1 =
    KernelIn (to_Zero A) (Abelian.Kernel (Diff C i)) _ _ (CohomologyComplex_KernelIn_eq A hs C i).
  Proof.
    intros K1.
    unfold K1.
    rewrite <- (@KernelInComp A (to_Zero A) _ _ _ _ _ _ _ _ (CohomologyComplexIso_eq1' C i)).
    use KernelInsEq. rewrite KernelCommutes. rewrite KernelCommutes.
    apply pathsinv0. apply factorization1.
  Qed.

  Local Lemma CohomologyComplexIso_mor_eq2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK1 := CokernelOut
                 (to_Zero A)
                 (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                       (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 _ _ (CohomologyComplexIso_eq2 C i) in
    (CokernelOut
       (to_Zero A)
       (Cokernel
          (transportf (precategory_morphisms (C (i - 1)))
                      (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
       (C (i + 1)) (Diff C i) (CohomologyComplex_KernelIn_eq A hs C i)) =
    CK1 · (factorization2_monic A hs (Diff C i)).
  Proof.
    intros CK1.
    unfold CK1.
    rewrite <- (@CokernelOutComp A (to_Zero A) _ _ _ _ _ _ _ _ (CohomologyComplexIso_eq2' C i)).
    use CokernelOutsEq. rewrite CokernelCommutes. rewrite CokernelCommutes.
    apply factorization2.
  Qed.

  Local Lemma CohomologyComplexIso_isKernel_Eq (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    K1 · (φ1 · φ2) = ZeroArrow (to_Zero A) _ _.
  Proof.
    intros φ1 φ2 K1.
    rewrite assoc. unfold K1. unfold φ1. rewrite KernelCommutes.
    set (f1 := factorization1 hs (transportf (precategory_morphisms (C (i - 1)))
                                             (maponpaths C (hzrminusplus i 1))
                                             (Diff C (i - 1)))).
    set (CK2 := CokernelPath A (to_Zero A) f1 (Cokernel _)).
    set (CK2' := CokernelEpiComp A hs (to_Zero A) _ _ CK2).
    set (K3 := MonicToKernel' A hs _ CK2').
    apply (KernelCompZero (to_Zero A) K3).
  Qed.

  Local Lemma CohomologyComplexIso_isKernel (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    isKernel (to_Zero A) K1 (φ1 · φ2) (CohomologyComplexIso_isKernel_Eq C i).
  Proof.
    intros φ1 φ2 K1.
    set (f1 := factorization1 hs (transportf (precategory_morphisms (C (i - 1)))
                                             (maponpaths C (hzrminusplus i 1))
                                             (Diff C (i - 1)))).
    set (CK2 := CokernelPath A (to_Zero A) f1 (Cokernel _)).
    set (CK2' := CokernelEpiComp A hs (to_Zero A) _ _ CK2).
    set (K3 := MonicToKernel' A hs _ CK2').
    use mk_isKernel.
    - exact hs.
    - intros w h H'. rewrite assoc in H'.
      use unique_exists.
      + exact (KernelIn (to_Zero A) K3 _ (h · φ1) H').
      + cbn beta.
        use (KernelArrowisMonic (to_Zero A) (Kernel (Diff C i))). unfold K1.
        rewrite <- assoc. rewrite KernelCommutes.
        fold φ1. rewrite <- (KernelCommutes (to_Zero A) K3 _ _ H').
        apply cancel_precomposition. apply idpath.
      + intros y. apply hs.
      + intros y X. cbn beta in X. apply (CohomologyComplexIso_isMonic C i). fold K1. rewrite X.
        use (KernelArrowisMonic (to_Zero A) (Kernel (Diff C i))). unfold K1.
        rewrite <- assoc. rewrite KernelCommutes.
        rewrite (KernelCommutes (to_Zero A) K3). apply idpath.
  Qed.

  Local Lemma CohomologyComplexIso_KernelArrow (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let K4 := mk_Kernel _ _ _ (CohomologyComplexIso_isKernel_Eq C i)
                         (CohomologyComplexIso_isKernel C i) in
    KernelArrow K4 = KernelIn (to_Zero A) (Kernel (Diff C i))
                              (Image
                                 (transportf (precategory_morphisms (C (i - 1)))
                                             (maponpaths C (hzrminusplus i 1))
                                             (Diff C (i - 1))))
                              (factorization1_monic
                                 A (transportf (precategory_morphisms (C (i - 1)))
                                               (maponpaths C (hzrminusplus i 1))
                                               (Diff C (i - 1))))
                              (CohomologyComplexIso_eq1 C i).
  Proof.
    apply idpath.
  Qed.

  Local Lemma CohomologyComplexIso_isCokernel_Eq (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let CK1 := CokernelOut
                 (to_Zero A)
                 (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                       (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 _ _ (CohomologyComplexIso_eq2 C i) in
    φ1 · φ2 · CK1 = ZeroArrow (to_Zero A) _ _.
  Proof.
    intros φ1 φ2 CK1.
    unfold CK1. unfold φ2. rewrite <- assoc. rewrite CokernelCommutes.
    set (f2 := factorization2 hs (Diff C i)).
    set (K2 := KernelPath A (to_Zero A) f2 (Kernel _)).
    set (K2' := KernelCompMonic A hs (to_Zero A) _ _ K2).
    set (CK3 := EpiToCokernel' A hs _ K2').
    apply (CokernelCompZero (to_Zero A) CK3).
  Qed.

  Local Lemma CohomologyComplexIso_isCokernel (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let CK1 := CokernelOut
                 (to_Zero A)
                 (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                       (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 _ _ (CohomologyComplexIso_eq2 C i) in
    isCokernel (to_Zero A) (φ1 · φ2) CK1 (CohomologyComplexIso_isCokernel_Eq C i).
  Proof.
    intros φ1 φ2 CK1.
    set (f2 := factorization2 hs (Diff C i)).
    set (K2 := KernelPath A (to_Zero A) f2 (Kernel _)).
    set (K2' := KernelCompMonic A hs (to_Zero A) _ _ K2).
    set (CK3 := EpiToCokernel' A hs _ K2').
    use mk_isCokernel.
    - exact hs.
    - intros w h H'. rewrite <- assoc in H'.
      use unique_exists.
      + exact (CokernelOut (to_Zero A) CK3 _ (φ2 · h) H').
      + cbn beta.
        use (CokernelArrowisEpi
               (to_Zero A) (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                 (maponpaths C (hzrminusplus i 1))
                                                 (Diff C (i - 1))))).
        unfold CK1. rewrite assoc. rewrite CokernelCommutes. fold φ2.
        rewrite <- (CokernelCommutes (to_Zero A) CK3 _ _ H').
        apply cancel_postcomposition. apply idpath.
      + intros y. apply hs.
      + intros y X. cbn beta in X. apply (CohomologyComplexIso_isEpi C i). fold CK1. rewrite X.
        use (CokernelArrowisEpi
               (to_Zero A) (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                 (maponpaths C (hzrminusplus i 1))
                                                 (Diff C (i - 1))))).
        unfold CK1.
        rewrite assoc.  rewrite CokernelCommutes.
        rewrite (CokernelCommutes (to_Zero A) CK3). apply idpath.
  Qed.

  Local Lemma CohomologyComplexIso_CokernelArrow (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK4 := mk_Cokernel _ _ _ (CohomologyComplexIso_isCokernel_Eq C i)
                           (CohomologyComplexIso_isCokernel C i) in
    CokernelArrow CK4 =
    (CokernelOut (to_Zero A)
                 (Cokernel
                    (transportf (precategory_morphisms (C (i - 1)))
                                (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 (CoImage (Diff C i)) (factorization2_epi A (Diff C i))
                 (CohomologyComplexIso_eq2 C i)).
  Proof.
    apply idpath.
  Qed.

  Definition CohomologyComplexIso_Mor1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    A⟦Cokernel
        (factorization1_epi
           A hs (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                            (Diff C (i - 1))) · K1),
       Cokernel
         (KernelIn (to_Zero A) (Kernel (Diff C i)) (C (i - 1))
                   (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                               (Diff C (i - 1))) (CohomologyComplex_KernelIn_eq A hs C i))⟧ :=
    @CokernelOutPaths_is_iso_mor
      A (to_Zero A) _ _ _ _ (CohomologyComplexIso_mor_eq1 C i) (Cokernel _) (Cokernel _).

  Definition CohomologyComplexIso_Mor2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    A ⟦Cokernel K1,
       Cokernel
         (factorization1_epi
            A hs (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                             (Diff C (i - 1))) · K1)⟧ :=
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    CokernelEpiComp_mor2
      A (to_Zero A) (factorization1_epi A hs (transportf (precategory_morphisms (C (i - 1)))
                                                     (maponpaths C (hzrminusplus i 1))
                                                     (Diff C (i - 1))))
      K1 (Cokernel _) (Cokernel _).

  Definition CohomologyComplexIso_Mor3 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK1 := CokernelOut
                 (to_Zero A)
                 (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                       (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 _ _ (CohomologyComplexIso_eq2 C i) in
    A⟦Kernel
        (CokernelOut
           (to_Zero A) (Cokernel
                      (transportf (precategory_morphisms (C (i - 1)))
                                  (maponpaths C (hzrminusplus i 1))
                                  (Diff C (i - 1)))) (C (i + 1)) (Diff C i)
           (CohomologyComplex_KernelIn_eq A hs C i)),
      Kernel (CK1 · factorization2_monic A hs (Diff C i))⟧ :=
    @KernelInPaths_is_iso_mor
      A (to_Zero A) _ _ _ _ (CohomologyComplexIso_mor_eq2 C i) (Kernel _) (Kernel _).

  Definition CohomologyComplexIso_Mor4 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK1 := CokernelOut
                 (to_Zero A)
                 (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                       (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 _ _ (CohomologyComplexIso_eq2 C i) in
    A ⟦Kernel (CK1 · factorization2_monic A hs (Diff C i)), Kernel CK1⟧ :=
    (KernelCompMonic_mor1 A (to_Zero A) _ _ (Kernel _) (Kernel _)).

  Definition CohomologyComplexIso_Mor5 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i) in
    let K4 := mk_Kernel _ _ _ (CohomologyComplexIso_isKernel_Eq C i)
                         (CohomologyComplexIso_isKernel C i) in
    A⟦Cokernel (KernelArrow K4), Cokernel K1⟧ :=
    @CokernelOutPaths_is_iso_mor
      A (to_Zero A) _ _ _ _ (CohomologyComplexIso_KernelArrow C i) (Cokernel _) (Cokernel _).

  Definition CohomologyComplexIso_Mor6 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let K4 := mk_Kernel _ _ _ (CohomologyComplexIso_isKernel_Eq C i)
                        (CohomologyComplexIso_isKernel C i) in
    iso (CoImage (φ1 · φ2)) (Cokernel (KernelArrow K4)) :=
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let K4 := mk_Kernel _ _ _ (CohomologyComplexIso_isKernel_Eq C i)
                        (CohomologyComplexIso_isKernel C i) in
    CohomologyComplexIso_CokerKerIso _ K4 (CoImage (φ1 · φ2)) (Cokernel (KernelArrow K4)).

  Definition CohomologyComplexIso_Mor7 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK1 := CokernelOut
                 (to_Zero A)
                 (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                       (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                 _ _ (CohomologyComplexIso_eq2 C i) in
    A⟦Kernel CK1,
      Kernel
        (CokernelArrow
           (mk_Cokernel (to_Zero A)
                        (KernelArrow (Kernel (Diff C i)) · CokernelArrow
                                     (Cokernel
                                        (transportf (precategory_morphisms (C (i - 1)))
                                                    (maponpaths C (hzrminusplus i 1))
                                                    (Diff C (i - 1))))) CK1
                        (CohomologyComplexIso_isCokernel_Eq C i)
                        (CohomologyComplexIso_isCokernel C i)))⟧ :=
    @KernelInPaths_is_iso_mor
      A (to_Zero A) _ _ _ _ (! (CohomologyComplexIso_CokernelArrow C i)) (Kernel _) (Kernel _).

  Definition CohomologyComplexIso_Mor8 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let CK4 := mk_Cokernel _ _ _ (CohomologyComplexIso_isCokernel_Eq C i)
                           (CohomologyComplexIso_isCokernel C i) in
    iso (Kernel (CokernelArrow CK4)) (Image (φ1 · φ2)) :=
    let φ1 := KernelArrow (Kernel (Diff C i)) in
    let φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))) in
    let CK4 := mk_Cokernel _ _ _ (CohomologyComplexIso_isCokernel_Eq C i)
                           (CohomologyComplexIso_isCokernel C i) in
    CohomologyComplexIso_KerCokerIso CK4 _ (Kernel (CokernelArrow CK4)) (Image (φ1 · φ2)).

  Definition CohomologyComplexIso_Mor_i (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    AbelianToAdditive A hs ⟦((CohomologyComplex' C)  : Complex (AbelianToAdditive A hs)) i,
                            ((CohomologyComplex A hs C) : Complex (AbelianToAdditive A hs)) i⟧.
  Proof.
    cbn.
    set (φ1 := KernelArrow (Kernel (Diff C i))).
    set (φ2 := CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                   (maponpaths C (hzrminusplus i 1))
                                                   (Diff C (i - 1))))).
    (* The idea is to pre- and postcompose with morphisms to reach inverse of
       [CoIm_to_Im_is_iso]. *)
    (* Change source and target by compose and postcompose with isomorphisms *)
    set (f1 := factorization1 hs (transportf (precategory_morphisms (C (i - 1)))
                                             (maponpaths C (hzrminusplus i 1))
                                             (Diff C (i - 1)))).
    set (f2 := factorization2 hs (Diff C i)).
    set (K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i)).
    set (CK1 := CokernelOut (to_Zero A) (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                          (maponpaths C (hzrminusplus i 1))
                                                          (Diff C (i - 1)))) _
                            _ (CohomologyComplexIso_eq2 C i)).
    use (postcompose (CohomologyComplexIso_Mor1 C i)).
    use (postcompose (CohomologyComplexIso_Mor2 C i)).
    use (compose (CohomologyComplexIso_Mor3 C i)).
    use (compose (CohomologyComplexIso_Mor4 C i)).
    (* Postcompose *)
    set (CK2 := CokernelPath A (to_Zero A) f1 (Cokernel _)).
    set (CK2' := CokernelEpiComp A hs (to_Zero A) _ _ CK2).
    set (K3 := MonicToKernel' A hs _ CK2').
    set (K4 := mk_Kernel _ _ _ (CohomologyComplexIso_isKernel_Eq C i)
                         (CohomologyComplexIso_isKernel C i)).
    use (postcompose (CohomologyComplexIso_Mor5 C i)).
    use (postcompose (CohomologyComplexIso_Mor6 C i)).
    (* compose *)
    set (K2 := KernelPath A (to_Zero A) f2 (Kernel _)).
    set (K2' := KernelCompMonic A hs (to_Zero A) _ _ K2).
    set (CK3 := EpiToCokernel' A hs _ K2').
    set (CK4 := mk_Cokernel _ _ _ (CohomologyComplexIso_isCokernel_Eq C i)
                            (CohomologyComplexIso_isCokernel C i)).
    use (compose (CohomologyComplexIso_Mor7 C i)).
    use (compose (CohomologyComplexIso_Mor8 C i)).
    exact (iso_inv_from_is_iso _ (is_iso_qinv _ _ (CoIm_to_Im_is_iso A hs (φ1 · φ2)))).
  Defined.

  Local Lemma CohomologyComplexIso_Mor_comm (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (CohomologyComplexIso_Mor_i C i) · ZeroArrow (to_Zero A) _ _ =
    ZeroArrow (to_Zero A) _ _ · (CohomologyComplexIso_Mor_i C (i + 1)).
  Proof.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition CohomologyComplexIso_Mor (C : Complex (AbelianToAdditive A hs)) :
    ComplexPreCat_AbelianPreCat A hs ⟦CohomologyComplex' C, CohomologyComplex A hs C⟧.
  Proof.
    use mk_Morphism.
    - intros i. exact (CohomologyComplexIso_Mor_i C i).
    - intros i. exact (CohomologyComplexIso_Mor_comm C i).
  Defined.

  Local Opaque is_iso_qinv.

  Lemma CohomologyComplexIso_is_iso_i (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    is_iso (CohomologyComplexIso_Mor_i C i).
  Proof.
    unfold CohomologyComplexIso_Mor. cbn.
    unfold CohomologyComplexIso_Mor_i. cbn.
    unfold postcompose. use is_iso_comp_of_is_isos.
    - use is_iso_comp_of_is_isos.
      + use is_iso_comp_of_is_isos.
        * unfold CohomologyComplexIso_Mor3.
          apply KernelInPaths_is_iso.
        * use is_iso_comp_of_is_isos.
          -- unfold CohomologyComplexIso_Mor4.
              set (CK1 := Cokernel
                            (transportf (precategory_morphisms (C (i - 1)))
                                        (maponpaths C (hzrminusplus i 1))
                                        (Diff C (i - 1)))).
              set (K1 := Kernel
                           (CokernelOut (to_Zero A) CK1 (CoImage (Diff C i))
                                        (factorization2_epi A (Diff C i))
                                        (CohomologyComplexIso_eq2 C i))).
              apply (KernelCompMonic1 A (to_Zero A)
                                      (CokernelOut (to_Zero A) CK1 (CoImage (Diff C i))
                                                   (factorization2_epi A (Diff C i))
                                                   (CohomologyComplexIso_eq2 C i))
                                      (factorization2_monic A hs (Diff C i)) (Kernel _) K1).
          -- use is_iso_comp_of_is_isos.
             ++ use is_iso_comp_of_is_isos.
                ** use is_iso_comp_of_is_isos.
                   --- unfold CohomologyComplexIso_Mor7.
                       apply KernelInPaths_is_iso.
                   --- use is_iso_comp_of_is_isos.
                       +++ unfold CohomologyComplexIso_Mor8. apply pr2.
                       +++ apply is_iso_inv_from_iso.
                ** unfold CohomologyComplexIso_Mor6. apply pr2.
             ++ unfold CohomologyComplexIso_Mor5. apply CokernelOutPaths_is_iso.
      + unfold CohomologyComplexIso_Mor2.
        set (K1 := KernelIn (to_Zero A) (Kernel (Diff C i)) _ _ (CohomologyComplexIso_eq1 C i)).
        apply (CokernelEpiComp2 A (to_Zero A)
                                (factorization1_epi
                                   A hs (transportf (precategory_morphisms (C (i - 1)))
                                                    (maponpaths C (hzrminusplus i 1))
                                                    (Diff C (i - 1))))
                                K1 (Cokernel _) (Cokernel _)).
    - unfold CohomologyComplexIso_Mor1. apply CokernelOutPaths_is_iso.
  Qed.

  Local Transparent is_iso_qinv.

  Local Lemma CohomologyComplexIso_is_iso (C : Complex (AbelianToAdditive A hs)) :
    is_iso (CohomologyComplexIso_Mor C).
  Proof.
    use ComplexIsoIndexIso. intros i. exact (CohomologyComplexIso_is_iso_i C i).
  Qed.

  Definition CohomologyComplexIso (C : Complex (AbelianToAdditive A hs)) :
    iso (CohomologyComplex' C) (CohomologyComplex A hs C).
  Proof.
    use isopair.
    - exact (CohomologyComplexIso_Mor C).
    - exact (CohomologyComplexIso_is_iso C).
  Defined.

End def_cohomology'_complex.


(** * Definition of quasi-isomorphisms *)
(** ** Introduction
   A quasi-isomorphism is a morphism of complexes which maps to an isomorphisms by the cohomology
   functor H : C(A) -> C(A). See section [def_cohomology_complex] for definition of this functor.

   Quasi-isomorphisms are defined in [isQIS]. In [IdentityIsQIS] we show that identity morphism is
   a quasi-isomorphism, and in [CompIsQIS] we show that composition of quasi-isomorphisms is a
   quasi-isomorphism.
*)
Section def_quasi_isomorphisms.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  Definition isQIS {C1 C2 : (ComplexPreCat_AbelianPreCat A hs)}
             (f : (ComplexPreCat_AbelianPreCat A hs)⟦C1, C2⟧) : UU :=
    is_iso (#(CohomologyFunctor A hs) f).

  Lemma isaprop_isQIS {C1 C2 : (ComplexPreCat_AbelianPreCat A hs)}
        (f : (ComplexPreCat_AbelianPreCat A hs)⟦C1, C2⟧) : isaprop (isQIS f).
  Proof.
    apply isaprop_is_iso.
  Qed.

  Lemma IdentityIsQIS (C : (ComplexPreCat_AbelianPreCat A hs)) : isQIS (identity C).
  Proof.
    exact (pr2 (functor_on_iso (CohomologyFunctor A hs) (identity_iso C))).
  Qed.

  Lemma CompIsQIS {C1 C2 C3 : (ComplexPreCat_AbelianPreCat A hs)}
        (f1 : (ComplexPreCat_AbelianPreCat A hs)⟦C1, C2⟧) (H1 : isQIS f1)
        (f2 : (ComplexPreCat_AbelianPreCat A hs)⟦C2, C3⟧) (H2 : isQIS f2) :
    isQIS (f1 · f2).
  Proof.
    unfold isQIS. rewrite functor_comp.
    apply (@is_iso_comp_of_isos (ComplexPreCat_AbelianPreCat A hs) _ _ _
                                (isopair _ H1) (isopair _ H2)).
  Qed.

End def_quasi_isomorphisms.


(** * Cohomology functor is an additive functor *)
(** ** Introduction
   In this section we show that the cohomology functor, [CohomologyFunctor], is an additive functor.
   This is shown in [CohomologyFunctor_Additive]. *)
Section def_cohomology_functor_additive.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  Local Lemma CohomologyFunctor_isAdditive :
    @isAdditiveFunctor (ComplexPreCat_Additive (AbelianToAdditive A hs)) (ComplexPreCat_Additive (AbelianToAdditive A hs))
                       (CohomologyFunctor A hs).
  (* note: with primitive projections off, the goal can be written more simply as
            isAdditiveFunctor (CohomologyFunctor A hs)
   *)
  Proof.
    use mk_isAdditiveFunctor.
    intros C1 C2.
    use tpair.
    - intros f1 f2.
      use MorphismEq.
      intros i. cbn in *. unfold CohomologyMorphism_Mor.
      set (CK1 := Cokernel
                    (KernelIn (to_Zero A) (Kernel (Diff C1 i)) (C1 (i - 1))
                              (transportf (precategory_morphisms (C1 (i - 1)))
                                          (maponpaths C1 (hzrminusplus i 1)) (Diff C1 (i - 1)))
                              (CohomologyComplex_KernelIn_eq A hs C1 i))).
      cbn in CK1. fold CK1.
      set (CK2 := Cokernel
                    (KernelIn (to_Zero A) (Kernel (Diff C2 i)) (C2 (i - 1))
                              (transportf (precategory_morphisms (C2 (i - 1)))
                                          (maponpaths C2 (hzrminusplus i 1)) (Diff C2 (i - 1)))
                              (CohomologyComplex_KernelIn_eq A hs C2 i))).
      cbn in CK2. fold CK2.
      set (tmp := CokernelOutOp (AbelianToAdditive A hs)).
      cbn in tmp. rewrite <- tmp. clear tmp.
      use CokernelOutsEq. rewrite CokernelCommutes. rewrite CokernelCommutes.
      set (tmp := @to_postmor_linear' (AbelianToAdditive A hs)). cbn in tmp.
      rewrite <- tmp. clear tmp. apply cancel_postcomposition.
      set (tmp := KernelInOp (AbelianToAdditive A hs)).
      cbn in tmp. rewrite <- tmp. clear tmp.
      use KernelInsEq. rewrite KernelCommutes. rewrite KernelCommutes.
      set (tmp := @to_premor_linear' (AbelianToAdditive A hs)). cbn in tmp.
      rewrite <- tmp. clear tmp. apply idpath.
    - cbn.
      use MorphismEq.
      intros i. cbn in *. unfold CohomologyMorphism_Mor.
      set (CK1 := Cokernel
                    (KernelIn (to_Zero A) (Kernel (Diff C1 i)) (C1 (i - 1))
                              (transportf (precategory_morphisms (C1 (i - 1)))
                                          (maponpaths C1 (hzrminusplus i 1)) (Diff C1 (i - 1)))
                              (CohomologyComplex_KernelIn_eq A hs C1 i))).
      cbn in CK1. fold CK1.
      set (CK2 := Cokernel
                    (KernelIn (to_Zero A) (Kernel (Diff C2 i)) (C2 (i - 1))
                              (transportf (precategory_morphisms (C2 (i - 1)))
                                          (maponpaths C2 (hzrminusplus i 1)) (Diff C2 (i - 1)))
                              (CohomologyComplex_KernelIn_eq A hs C2 i))).
      cbn in CK2. fold CK2.
      use CokernelOutsEq.
      rewrite CokernelCommutes. rewrite ZeroArrow_comp_right.
      rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (CokernelArrow CK2)).
      apply cancel_postcomposition.
      use KernelInsEq.
      rewrite KernelCommutes.
      rewrite ZeroArrow_comp_left. cbn. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition CohomologyFunctor_Additive :
    AdditiveFunctor (ComplexPreCat_Additive (AbelianToAdditive A hs))
                    (ComplexPreCat_Additive (AbelianToAdditive A hs)).
  Proof.
    use mk_AdditiveFunctor.
    - exact (CohomologyFunctor A hs).
    - exact CohomologyFunctor_isAdditive.
  Defined.

End def_cohomology_functor_additive.



(** * CohomologyFunctor factors through naive homotopy category *)
(** ** Introduction
   We show that there exists a functor K(A) -> K(A) such that the following diagram is commutative
                           C(A) -> C(A)
                             |      ||         (Think this as a triangle)
                           K(A) -> C(A)
   Here C(A) -> C(A) is the cohomology functor H : C(A) -> C(A), [CohomologyFunctor], see section
   [def_cohomology_complex]. The vertical functor C(A) -> K(A) is the canonical functor
   [ComplexHomotFunctor]. The constructed functor K(A) -> K(A) is also additive. Using this
   functor we define quasi-isomorphisms for K(A).

   On objects this functor sends a complex X to its cohomology complex. This is easily verified to
   commute because the vertical functors are identity on objects. To construct the map on morphisms
   we  first show that two homotopic, [ComplexHomotSubset], morphisms in C(A) are mapped to the
   same morphism by the cohomology functor for C(A). Thus, given a morphism f in K(A), for every
   morphism f' which maps to f by C(A) -> K(A) the image under C(A) -> C(A) is the same, that is,
   is contractible. This is the observation we use to define the map on morphisms. After this
   observation it is easy to see that the diagram is commutative.

   In [CohomologyFunctorHomotopy] it is shown that a morphism induced by homotopy is sent to the
   zero morphism in C(A). In [CohomologyFunctorHomotopies] we use this observation to prove that
   two homotopic morphisms are sent to the same morphisms by the cohomology functor. In
   [CohomologyFunctorH_Mor] we show that the image on morphisms is contractible, in
   [CohomologyFunctorH_functor_data] we construct the functor data for K(A) -> C(A), and finally
   in [CohomologyFunctorH] we construct the functor. Commutativity of the diagram is proved in
   [CohomologyFunctorHCommutes]. The fact that K(A) -> C(A) is additive is proved in
   [CohomologyFunctorH_Additive].
*)
Section def_cohomology_homotopy.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.


  (** ** Homotopic maps are mapped to equal morphisms by the cohomology functor C(A) -> C(A) *)

  Lemma CohomologyFunctorHomotopy_eq1 {C1 C2 : Complex (AbelianToAdditive A hs)}
        (H : ComplexHomot _ C1 C2) (i : hz) :
    KernelArrow (Kernel (Diff C1 i)) · transportf (precategory_morphisms (C1 i))
                (maponpaths C2 (hzrminusplus i 1)) (H i · Diff C2 (i - 1)) ·
                Diff C2 i = ZeroArrow (to_Zero A) (Kernel (Diff C1 i)) (C2 (i + 1)).
  Proof.
    induction (hzrminusplus i 1). cbn. unfold idfun. rewrite <- assoc. rewrite <- assoc.
    set (tmp := DSq _ C2 (i - 1)). cbn in tmp. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  (** Homotopy is mapped to ZeroArrow *)
  Lemma CohomologyFunctorHomotopy {C1 C2 : Complex (AbelianToAdditive A hs)}
        (H : ComplexHomot _ C1 C2) :
    CohomologyMorphism A hs (ComplexHomotMorphism (AbelianToAdditive A hs) H) =
    ZeroMorphism (AbelianToAdditive A hs) (CohomologyComplex A hs C1) (CohomologyComplex A hs C2).
  Proof.
    use MorphismEq. intros i. cbn. unfold CohomologyMorphism_Mor.
    use CokernelOutsEq. rewrite CokernelCommutes.
    rewrite ZeroArrow_comp_right.
    set (tmp := @KernelIn _ (to_Zero A) _ _ _ (Kernel (Diff C2 i)) (Kernel (Diff C1 i))
                          (KernelArrow (Kernel (Diff C1 i)) ·
                                       (transportf (precategory_morphisms (C1 i))
                                                   (maponpaths C2 (hzrminusplus i 1))
                                                   (H i · Diff C2 (i - 1))))
                          (CohomologyFunctorHomotopy_eq1 H i)).
    assert (e0 : KernelIn (to_Zero A) (Kernel (Diff C2 i)) (Kernel (Diff C1 i))
    (KernelArrow (Kernel (Diff C1 i)) · Abelian_op A hs (C1 i) (C2 i)
                                           (transportf (precategory_morphisms (C1 i))
                                                       (maponpaths C2 (hzrminusplus i 1))
                                                       (H i · Diff C2 (i - 1)))
                                           (transportf (precategory_morphisms (C1 i))
                                                       (maponpaths C2 (hzrplusminus i 1))
                                                       (Diff C1 i · H (i + 1))))
    (CohomologyMorphism_KernelIn_comm A hs (ComplexHomotMorphism (AbelianToAdditive A hs) H) i) =
                 tmp).
    {
      unfold tmp. clear tmp. use KernelInsEq. rewrite KernelCommutes. rewrite KernelCommutes.
      set (tmp := @to_premor_linear' (AbelianToAdditive A hs)). cbn in tmp. rewrite tmp. clear tmp.
      rewrite transport_target_postcompose. rewrite transport_target_postcompose.
      rewrite assoc. rewrite assoc.
      rewrite KernelCompZero. rewrite ZeroArrow_comp_left. rewrite <- PreAdditive_unel_zero.
      set (tmp :=  @to_runax' (AbelianToAdditive A hs)). cbn in tmp. rewrite tmp. clear tmp.
      apply idpath.
    }
    cbn. cbn in e0. rewrite e0. clear e0. unfold tmp. clear tmp.
    assert (e1 : KernelIn (to_Zero A) (Kernel (Diff C2 i)) (Kernel (Diff C1 i))
                          ((KernelArrow (Kernel (Diff C1 i)))
                             · (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrminusplus i 1))
                                            (H i · Diff C2 (i - 1))))
                          (CohomologyFunctorHomotopy_eq1 H i) =
                 (KernelArrow (Kernel (Diff C1 i)))
                   · (H i)
                   · (KernelIn ((to_Zero A)) (Abelian.Kernel (Diff C2 i)) _ _
                                (CohomologyComplex_KernelIn_eq A hs C2 i))).
    {
      use KernelInsEq. rewrite KernelCommutes. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. rewrite KernelCommutes.
      rewrite transport_target_postcompose. apply idpath.
    }
    cbn. cbn in e1. rewrite e1. clear e1. rewrite <- assoc. rewrite CokernelCompZero.
    rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Lemma CohomologyFunctorHomotopies {C1 C2 : Complex (AbelianToAdditive A hs)}
        (f g : (ComplexPreCat_Additive (AbelianToAdditive A hs))⟦C1, C2⟧)
        (H : subgrhrel (ComplexHomotSubgrp (AbelianToAdditive A hs) C1 C2) f g) :
    # (CohomologyFunctor_Additive A hs) f = # (CohomologyFunctor_Additive A hs) g.
  Proof.
    set (inv := @to_inv (ComplexPreCat_Additive (AbelianToAdditive A hs)) _ _
                        (# (CohomologyFunctor_Additive A hs) g)).
    set (tmp := @grrcan (@to_abgrop (ComplexPreCat_Additive (AbelianToAdditive A hs)) _ _)
                        (# (CohomologyFunctor_Additive A hs) f)
                        (# (CohomologyFunctor_Additive A hs) g) inv).
    apply tmp. clear tmp. unfold inv. clear inv.
    set (tmp := @rinvax (ComplexPreCat_Additive (AbelianToAdditive A hs)) _ _
                        (# (CohomologyFunctor_Additive A hs) g)).
    use (pathscomp0 _ (! tmp)). clear tmp.
    rewrite <- AdditiveFunctorInv.
    set (tmp := AdditiveFunctorLinear (CohomologyFunctor_Additive A hs) f (to_inv g)).
    apply pathsinv0 in tmp. use (pathscomp0 tmp). clear tmp.
    use (squash_to_prop H). apply has_homsets_ComplexPreCat_AbelianPreCat.
    intros H'. induction H' as [H1 H2]. induction H1 as [H11 H12]. cbn in H11. cbn in H2.
    cbn. rewrite <- H2. clear H.
    use (squash_to_prop H12). apply has_homsets_ComplexPreCat_AbelianPreCat.
    intros G. induction G as [G1 G2]. rewrite <- G2. clear H11 H12 H2 G2.
    apply CohomologyFunctorHomotopy.
  Qed.


  (** ** Structure for the image of a morphism to make type cheking faster *)

  Definition CohomologyFunctorHIm {C1 C2 : ComplexHomot_Additive (AbelianToAdditive A hs)}
             (f : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧) : UU :=
    ∑ (h : (ComplexPreCat_Additive (AbelianToAdditive A hs))⟦CohomologyComplex A hs C1,
                                                             CohomologyComplex A hs C2⟧),
    ∏ (f' : ComplexPreCat_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧)
      (H : # (ComplexHomotFunctor (AbelianToAdditive A hs)) f' = f),
    h = # (CohomologyFunctor A hs) f'.

  Definition CohomologyFunctorHImMor {C1 C2 : ComplexHomot_Additive (AbelianToAdditive A hs)}
             {f : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧}
             (h : CohomologyFunctorHIm f) :
    (ComplexPreCat_Additive (AbelianToAdditive A hs))⟦CohomologyComplex A hs C1,
                                                      CohomologyComplex A hs C2⟧ := pr1 h.

  Definition CohomologyFunctorHImEq {C1 C2 : ComplexHomot_Additive (AbelianToAdditive A hs)}
             {f : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧}
             (h : CohomologyFunctorHIm f)
             (f' : ComplexPreCat_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧)
             (H : # (ComplexHomotFunctor (AbelianToAdditive A hs)) f' = f) :
    CohomologyFunctorHImMor h = # (CohomologyFunctor A hs) f' := pr2 h f' H.

  Definition mk_CohomologyFunctorHIm {C1 C2 : ComplexHomot_Additive (AbelianToAdditive A hs)}
             (f : (ComplexHomot_Additive (AbelianToAdditive A hs))⟦C1, C2⟧)
             (h : (ComplexPreCat_Additive (AbelianToAdditive A hs))⟦CohomologyComplex A hs C1,
                                                                    CohomologyComplex A hs C2⟧)
             (HH : ∏ (f' : ComplexPreCat_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧)
                     (H : # (ComplexHomotFunctor (AbelianToAdditive A hs)) f' = f),
                   h = # (CohomologyFunctor A hs) f') : CohomologyFunctorHIm f :=
    tpair _ h HH.

  Lemma CohomologyFunctorHImEquality {C1 C2 : ComplexHomot_Additive (AbelianToAdditive A hs)}
             {f : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧}
             (h : CohomologyFunctorHIm f) (h' : CohomologyFunctorHIm f)
             (e : CohomologyFunctorHImMor h = CohomologyFunctorHImMor h') : h = h'.
  Proof.
    use total2_paths_f.
    - exact e.
    - apply proofirrelevance. apply impred_isaprop. intros t0.
      apply impred_isaprop. intros H0. apply has_homsets_ComplexPreCat.
  Qed.

  (** ** Construction of the functor and commutativity  *)

  Lemma CohomologyFunctorH_Mor_eq {C1 C2 : ComplexHomot_Additive (AbelianToAdditive A hs)}
        (f : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧)
        (H : hfiber # (ComplexHomotFunctor (AbelianToAdditive A hs)) f)
        (f' : ComplexPreCat_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧)
        (H' : # (ComplexHomotFunctor (AbelianToAdditive A hs)) f' = f) :
    # (CohomologyFunctor A hs) (pr1 H) = # (CohomologyFunctor A hs) f'.
  Proof.
    use CohomologyFunctorHomotopies.
    use (@abgrquotpr_rel_paths _ (binopeqrel_subgr_eqrel
                                    (ComplexHomotSubgrp (AbelianToAdditive A hs) C1 C2))).
    use (pathscomp0 (hfiberpr2 _ _ H)). apply pathsinv0. exact H'.
  Qed.

  Definition CohomologyFunctorH_Mor {C1 C2 : ComplexHomot_Additive (AbelianToAdditive A hs)}
             (f : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧) :
    iscontr (CohomologyFunctorHIm f).
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj (AbelianToAdditive A hs) f)).
    apply isapropiscontr. intros H.
    use iscontrpair.
    - use mk_CohomologyFunctorHIm.
      + exact ((# (CohomologyFunctor A hs) (hfiberpr1 _ _ H))).
      + intros f' H'. exact (CohomologyFunctorH_Mor_eq f H f' H').
    - intros t. use CohomologyFunctorHImEquality.
      use CohomologyFunctorHImEq.
      exact (hfiberpr2 _ _ H).
  Qed.

  Lemma CohomologyFunctorH_Mor_Id (C : ComplexHomot_Additive (AbelianToAdditive A hs)) :
    CohomologyFunctorHImMor (iscontrpr1 (CohomologyFunctorH_Mor (identity C))) = identity _.
  Proof.
    use (pathscomp0 (CohomologyFunctorHImEq
                       (iscontrpr1 (CohomologyFunctorH_Mor (identity C)))
                       (identity _)
                       (functor_id (ComplexHomotFunctor (AbelianToAdditive A hs)) _))).
    rewrite functor_id. apply idpath.
  Qed.

  Lemma CohomologyFunctorH_Mor_Comp {C1 C2 C3 : ComplexHomot_Additive (AbelianToAdditive A hs)}
             (f : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C1, C2⟧)
             (g : ComplexHomot_Additive (AbelianToAdditive A hs) ⟦C2, C3⟧) :
    (CohomologyFunctorHImMor (iscontrpr1 (CohomologyFunctorH_Mor (f · g)))) =
    (CohomologyFunctorHImMor (iscontrpr1 (CohomologyFunctorH_Mor f)))
      · (CohomologyFunctorHImMor (iscontrpr1 (CohomologyFunctorH_Mor g))) .
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj (AbelianToAdditive A hs) f)).
    apply has_homsets_ComplexPreCat. intros f'.
    use (squash_to_prop (ComplexHomotFunctor_issurj (AbelianToAdditive A hs) g)).
    apply has_homsets_ComplexPreCat. intros g'.
    rewrite (CohomologyFunctorHImEq (iscontrpr1 (CohomologyFunctorH_Mor f)) _ (hfiberpr2 _ _ f')).
    rewrite (CohomologyFunctorHImEq (iscontrpr1 (CohomologyFunctorH_Mor g)) _ (hfiberpr2 _ _ g')).
    set (tmp := functor_comp (CohomologyFunctor A hs) (hfiberpr1 _ _ f') (hfiberpr1 _ _ g')).
    use (pathscomp0 _ tmp). clear tmp.
    use (CohomologyFunctorHImEq (iscontrpr1 (CohomologyFunctorH_Mor (f · g)))).
    rewrite functor_comp. rewrite (hfiberpr2 _ _ f'). rewrite (hfiberpr2 _ _ g'). apply idpath.
  Qed.

  Definition CohomologyFunctorH_functor_data :
    functor_data (ComplexHomot_Additive (AbelianToAdditive A hs))
                 (ComplexPreCat_Additive (AbelianToAdditive A hs)).
  Proof.
    use tpair.
    - intros C. exact (CohomologyComplex A hs C).
    - intros C1 C2 f. exact (CohomologyFunctorHImMor (iscontrpr1 (CohomologyFunctorH_Mor f))).
  Defined.

  Local Lemma CohomologyFunctorH_isfunctor : is_functor CohomologyFunctorH_functor_data.
  Proof.
    split.
    - intros C. use CohomologyFunctorH_Mor_Id.
    - intros C1 C2 C3 f1 f2. use (CohomologyFunctorH_Mor_Comp f1 f2).
  Qed.

  Definition CohomologyFunctorH :
    functor (ComplexHomot_Additive (AbelianToAdditive A hs))
            (ComplexPreCat_Additive (AbelianToAdditive A hs)).
  Proof.
    use tpair.
    - exact CohomologyFunctorH_functor_data.
    - exact CohomologyFunctorH_isfunctor.
  Defined.

  Lemma CohomologyFunctorHCommutes :
    functor_composite (ComplexHomotFunctor (AbelianToAdditive A hs)) CohomologyFunctorH =
    (CohomologyFunctor A hs).
  Proof.
    use total2_paths_f.
    - use total2_paths_f.
      + apply idpath.
      + rewrite idpath_transportf.
        use funextsec. intros C1.
        use funextsec. intros C2.
        use funextsec. intros f.
        use (CohomologyFunctorHImEq
               (iscontrpr1
                  (CohomologyFunctorH_Mor
                     (# (ComplexHomotFunctor (AbelianToAdditive A hs)) f))) f
               (idpath _)).
    - apply proofirrelevance. apply isaprop_is_functor.
      use has_homsets_ComplexPreCat.
  Qed.


  (** ** Additivity of CohomologyFunctorH *)

  Local Opaque to_binop.
  Local Lemma CohomologyFunctorH_Additive_zero
        (C1 C2 : (ComplexHomot_Additive (AbelianToAdditive A hs))) :
    # CohomologyFunctorH
      (ZeroArrow (Additive.to_Zero (ComplexHomot_Additive (AbelianToAdditive A hs))) C1 C2) =
    ZeroArrow (Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)))
              (CohomologyFunctorH C1) (CohomologyFunctorH C2).
  Proof.
    use (pathscomp0 _ (@AdditiveFunctorZeroArrow
                         (ComplexPreCat_Additive (AbelianToAdditive A hs))
                         (ComplexPreCat_Additive (AbelianToAdditive A hs))
                         (CohomologyFunctor_Additive A hs) C1 C2)).
    assert (e0 : # (ComplexHomotFunctor (AbelianToAdditive A hs))
                   (ZeroArrow (Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)))
                              _ _) =
                 ZeroArrow (Additive.to_Zero (ComplexHomot_Additive (AbelianToAdditive A hs)))
                           C1 C2).
    {
      apply AdditiveFunctorZeroArrow.
    }
    rewrite <- e0. clear e0.
    use CohomologyFunctorHImEq.
    apply idpath.
  Qed.

  Local Lemma CohomologyFunctorH_Additive_linear
        {C1 C2 : (ComplexHomot_Additive (AbelianToAdditive A hs))}
        (f g : (ComplexHomot_Additive (AbelianToAdditive A hs))⟦C1, C2⟧) :
    # CohomologyFunctorH (to_binop C1 C2 f g) =
    to_binop (CohomologyFunctorH C1) (CohomologyFunctorH C2)
             (# CohomologyFunctorH f) (# CohomologyFunctorH g).
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj (AbelianToAdditive A hs) f)).
    apply has_homsets_ComplexPreCat. intros f'.
    use (squash_to_prop (ComplexHomotFunctor_issurj (AbelianToAdditive A hs) g)).
    apply has_homsets_ComplexPreCat. intros g'.
    cbn.
    rewrite (CohomologyFunctorHImEq (iscontrpr1 (CohomologyFunctorH_Mor f))
                                    (hfiberpr1 _ _ f') (hfiberpr2 _ _ f')).
    rewrite (CohomologyFunctorHImEq (iscontrpr1 (CohomologyFunctorH_Mor g))
                                    (hfiberpr1 _ _ g') (hfiberpr2 _ _ g')).
    set (tmp := @AdditiveFunctorLinear
                  (ComplexPreCat_Additive (AbelianToAdditive A hs))
                  (ComplexPreCat_Additive (AbelianToAdditive A hs))
                  (CohomologyFunctor_Additive A hs) C1 C2
                  (hfiberpr1 # (ComplexHomotFunctor (AbelianToAdditive A hs)) f f')
                  (hfiberpr1 # (ComplexHomotFunctor (AbelianToAdditive A hs)) g g')).
    use (pathscomp0 _ tmp). clear tmp.
    use (CohomologyFunctorHImEq (iscontrpr1 (CohomologyFunctorH_Mor (to_binop C1 C2 f g)))).
    rewrite AdditiveFunctorLinear.
    rewrite (hfiberpr2 _ _ f'). rewrite (hfiberpr2 _ _ g'). apply idpath.
  Qed.

  Local Lemma CohomologyFunctorH_isAdditive : isAdditiveFunctor CohomologyFunctorH.
  Proof.
    refine (@mk_isAdditiveFunctor' (ComplexHomot_Additive (AbelianToAdditive A hs))
                                   (ComplexPreCat_Additive (AbelianToAdditive A hs))
                                   CohomologyFunctorH _ _).
    - intros C1 C2. exact (CohomologyFunctorH_Additive_zero C1 C2).
    - intros C1 C2 f g. exact (CohomologyFunctorH_Additive_linear f g).
  Qed.

  Definition CohomologyFunctorH_Additive :
    AdditiveFunctor (ComplexHomot_Additive (AbelianToAdditive A hs))
                    (ComplexPreCat_Additive (AbelianToAdditive A hs)).
  Proof.
    use mk_AdditiveFunctor.
    - exact CohomologyFunctorH.
    - exact CohomologyFunctorH_isAdditive.
  Defined.
  Local Transparent to_binop.


  (** ** Quasi-isomorphisms in K(A) *)

  Definition isHQIS {C1 C2 : (ComplexHomot_Additive (AbelianToAdditive A hs))}
             (f : (ComplexHomot_Additive (AbelianToAdditive A hs))⟦C1, C2⟧) : UU :=
    is_iso (# CohomologyFunctorH_Additive f).

  Lemma isaprop_isHQIS {C1 C2 : (ComplexHomot_Additive (AbelianToAdditive A hs))}
             (f : (ComplexHomot_Additive (AbelianToAdditive A hs))⟦C1, C2⟧) : isaprop (isHQIS f).
  Proof.
    apply isaprop_is_iso.
  Qed.

  Lemma IdentityIsHQIS (C : (ComplexHomot_Additive (AbelianToAdditive A hs))) : isHQIS (identity C).
  Proof.
    exact (pr2 (functor_on_iso CohomologyFunctorH (identity_iso C))).
  Qed.

  Lemma CompIsHQIS {C1 C2 C3 : (ComplexHomot_Additive (AbelianToAdditive A hs))}
        (f1 : (ComplexHomot_Additive (AbelianToAdditive A hs))⟦C1, C2⟧) (H1 : isHQIS f1)
        (f2 : (ComplexHomot_Additive (AbelianToAdditive A hs))⟦C2, C3⟧) (H2 : isHQIS f2) :
    isHQIS (f1 · f2).
  Proof.
    unfold isHQIS. rewrite functor_comp.
    apply (@is_iso_comp_of_isos (ComplexPreCat_Additive (AbelianToAdditive A hs)) _ _ _
                                (isopair _ H1) (isopair _ H2)).
  Qed.

End def_cohomology_homotopy.


(** * Complex of kernels and complex of cokernels
   Let X be a complex. We construct a complex of kernels, which has objects ker d^{i+1}, and a
   complex of cokernels, which has objects coker d^{i-1}. The differentials of these complexes are
   the induced morphisms obtained by KernelIn and CokernelOut. For all integers i, we construct a
   morphisms h^i : coker d^{i-1} -> ker d^{i+1}, which is unique up to 2 commutative triangles.
   We show that the ith cohomology of X is isomorphic to the kernel of h^i and that the (i+1)th
   cohomology of X is isomorphic to cokernel of h^i. These results will be used, together with the
   snake lemma, to construct the long exact sequence associated to a short exact sequence of
   complexes.

   The complex of kernels is constructed in [KernelComplex]. The complex of cokernels is
   constructed in [CokernelComplex]. The morphism h^i is constructed in [CokernelKernelMorphism],
   where it is also shown to be unique with respect to the 2 commutative triangles. An isomorphism
   of ith cohomology of X with the kernel of h^i is constructed in [CokernelKernelCohomology1]. An
   isomorphism of the (i+1)th cohomology of X with cokernel of h^i is constructed in
   [CokernelKernelCohomology2].
 *)
Section def_kernel_cokernel_complex.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  (** ** Construction of kernel and cokernel complexes *)
  (** *** Complex of kernels *)

  Local Lemma KernelComplex_Kernel_comm (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    KernelArrow (Kernel (Diff C i)) · Diff C i · Diff C (i + 1) =
    ZeroArrow (to_Zero A) (Kernel (Diff C i)) (C (i + 1 + 1)).
  Proof.
    rewrite <- assoc.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (KernelArrow (Kernel (Diff C i)))).
    apply cancel_precomposition.
    exact (DSq (AbelianToAdditive A hs) C i).
  Qed.

  Local Lemma KernelComplex_comm (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Kernel (Diff C i))
              (KernelArrow (Kernel (Diff C i)) · Diff C i)
              (KernelComplex_Kernel_comm C i))
      · (KernelIn (to_Zero A) (Kernel (Diff C (i + 1 + 1))) (Kernel (Diff C (i + 1)))
                   (KernelArrow (Kernel (Diff C (i + 1))) · Diff C (i + 1))
                   (KernelComplex_Kernel_comm C (i + 1))) =
    ZeroArrow (to_Zero A) (Kernel (Diff C i)) (Kernel (Diff C (i + 1 + 1))).
  Proof.
    use KernelInsEq.
    rewrite <- assoc. rewrite KernelCommutes. rewrite assoc. rewrite KernelCommutes.
    rewrite ZeroArrow_comp_left. exact (KernelComplex_Kernel_comm C i).
  Qed.

  Definition KernelComplex (C : Complex (AbelianToAdditive A hs)) :
    Complex (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i. exact (Kernel (Diff C (i + 1))).
    - intros i. cbn.
      use KernelIn.
      + use compose.
        * exact (C (i + 1)).
        * use KernelArrow.
        * exact (Diff C (i + 1)).
      + exact (KernelComplex_Kernel_comm C (i + 1)).
    - intros i. cbn. exact (KernelComplex_comm C (i + 1)).
  Defined.


  (** *** Complex of cokernels *)

  Local Lemma CokernelComplex_Cokernel_comm (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (Diff C (i - 1))
      · (transportf (λ x' : A, A ⟦ x', C (i + 1 - 1 + 1) ⟧)
                     (! maponpaths C (hzrminusplus i 1 @ hzrplusminus' i 1)) (Diff C (i + 1 - 1)) ·
                     CokernelArrow (Cokernel (Diff C (i + 1 - 1)))) =
    ZeroArrow (to_Zero A) (C (i - 1)) (Cokernel (Diff C (i + 1 - 1))).
  Proof.
    induction (hzrminusplus i 1 @ hzrplusminus' i 1). cbn. unfold idfun.
    rewrite assoc. set (tmp := DSq (AbelianToAdditive A hs) C (i - 1)). cbn in tmp.
    rewrite tmp. clear tmp. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma CokernelComplex_comm (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (Cokernel (Diff C (i + 1 - 1)))
                (transportf (λ x' : A, A ⟦ x', C (i + 1 - 1 + 1) ⟧)
                            (! maponpaths C (hzrminusplus i 1 @ hzrplusminus' i 1))
                            (Diff C (i + 1 - 1)) · CokernelArrow (Cokernel (Diff C (i + 1 - 1))))
                (CokernelComplex_Cokernel_comm C i)
                · CokernelOut (to_Zero A) (Cokernel (Diff C (i + 1 - 1)))
                (Cokernel (Diff C (i + 1 + 1 - 1)))
                (transportf (λ x' : A, A ⟦ x', C (i + 1 + 1 - 1 + 1) ⟧)
                            (! maponpaths C
                               (hzrminusplus (i + 1) 1 @ hzrplusminus' (i + 1) 1))
                            (Diff C (i + 1 + 1 - 1)) · CokernelArrow
                            (Cokernel
                               (Diff C (i + 1 + 1 - 1))))
                (CokernelComplex_Cokernel_comm C (i + 1)) =
    ZeroArrow (to_Zero A) (Cokernel (Diff C (i - 1))) (Cokernel (Diff C (i + 1 + 1 - 1))).
  Proof.
    use (CokernelArrowisEpi (to_Zero A) (Cokernel (Diff C (i - 1)))).
    rewrite ZeroArrow_comp_right. rewrite assoc. rewrite CokernelCommutes.
    rewrite <- assoc. rewrite CokernelCommutes. rewrite assoc.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (CokernelArrow (Cokernel (Diff C (i + 1 + 1 - 1))))).
    apply cancel_postcomposition.
    use (transport_source_path _ _ (! maponpaths C (hzrplusminus i 1 @ hzrminusplus' i 1))).
    rewrite <- transport_source_precompose.
    rewrite <- maponpathsinv0. rewrite <- functtransportf.
    rewrite <- maponpathsinv0. rewrite <- functtransportf.
    rewrite transport_f_f.
    assert (e0 : (! (hzrminusplus i 1 @ hzrplusminus' i 1)
                    @ ! (hzrplusminus i 1 @ hzrminusplus' i 1)) = idpath _) by apply isasethz.
    cbn in e0. cbn. rewrite e0. clear e0. cbn. unfold idfun.
    rewrite transport_source_ZeroArrow.
    induction (hzrminusplus (i + 1) 1). cbn.
    induction (hzrplusminus' (i + 1 - 1 + 1) 1). cbn. unfold idfun.
    exact (DSq _ C (i + 1 - 1)).
  Qed.

  Definition CokernelComplex (C : Complex (AbelianToAdditive A hs)) :
    Complex (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i. exact (Cokernel (Diff C (i - 1))).
    - intros i. cbn.
      use CokernelOut.
      + use compose.
        * exact (C (i + 1 - 1 + 1)).
        * use (transportf (λ x' : A, precategory_morphisms x' (C (i + 1 - 1 + 1)))
                          (! maponpaths C (hzrminusplus i 1 @ hzrplusminus' i 1))).
          cbn.
          exact (Diff C (i + 1 - 1)).
        * use CokernelArrow.
      + exact (CokernelComplex_Cokernel_comm C i).
    - intros i. cbn. exact (CokernelComplex_comm C i).
  Defined.


  (** ** Construction of h^i and isomorphisms with cohomology *)
  (** *** Uniqueness and existence of h^i *)

  Local Lemma CokernelKernelMorphism_comm1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    Diff C (i - 1) · transportf (λ x : A, A ⟦x, C (i + 1)⟧)
         (! maponpaths C (hzrminusplus i 1)) (Diff C i) =
    ZeroArrow (to_Zero A) (C (i - 1)) (C (i + 1)).
  Proof.
    induction (hzrminusplus i 1). cbn. unfold idfun. exact (DSq _ C (i - 1)).
  Qed.


  Local Lemma CokernelKernelMorphism_comm2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                            (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                (CokernelKernelMorphism_comm1 C i) · Diff C (i + 1) =
    ZeroArrow (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1 + 1)).
  Proof.
    use CokernelOutsEq.
    rewrite assoc. rewrite CokernelCommutes. rewrite ZeroArrow_comp_right.
    induction (hzrminusplus i 1). cbn. unfold idfun.
    exact (DSq _ C (i - 1 + 1)).
  Qed.

  Local Lemma CokernelKernelMorphism_comm3 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    KernelIn
      (to_Zero A) (Kernel (Diff C (i + 1))) (C i) (Diff C i) (DSq (AbelianToAdditive A hs) C i) =
    transportf (λ i0 : pr1 hz, A ⟦ C i0, Cokernel (Diff C (i - 1)) ⟧) (hzrminusplus i 1)
               (CokernelArrow (Cokernel (Diff C (i - 1))))
               · KernelIn (to_Zero A) (Kernel (Diff C (i + 1)))
               (Cokernel (Diff C (i - 1)))
               (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1)))
                            (C (i + 1))
                            (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                        (! maponpaths C (hzrminusplus i 1))
                                        (Diff C i)) (CokernelKernelMorphism_comm1 C i))
               (CokernelKernelMorphism_comm2 C i).
  Proof.
    use KernelInsEq. rewrite KernelCommutes. rewrite <- assoc. rewrite KernelCommutes.
    assert (e1 : transportf (λ i0 : pr1 hz, A ⟦ C i0, Cokernel (Diff C (i - 1)) ⟧)
                            (hzrminusplus i 1) (CokernelArrow (Cokernel (Diff C (i - 1)))) =
                 transportf (λ x : A, A⟦x, Cokernel (Diff C (i - 1))⟧)
                            (maponpaths C (hzrminusplus i 1))
                            (CokernelArrow (Cokernel (Diff C (i - 1))))).
    {
      rewrite <- functtransportf. apply idpath.
    }
    rewrite e1. clear e1. rewrite <- transport_source_precompose. rewrite CokernelCommutes.
    rewrite transport_f_f. rewrite <- maponpathsinv0. rewrite <- maponpathscomp0.
    rewrite <- functtransportf.
    assert (e2 : ! hzrminusplus i 1 @ hzrminusplus i 1 = idpath _) by apply isasethz.
    rewrite e2. apply idpath.
  Qed.

  Local Lemma CokernelKernelMorphism_comm1' (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    Diff C (i - 1) · transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
         (! maponpaths C (hzrminusplus i 1)) (Diff C i) =
    ZeroArrow (to_Zero A) (C (i - 1)) (C (i + 1)).
  Proof.
    induction (hzrminusplus i 1). cbn. unfold idfun. exact (DSq _ C (i - 1)).
  Qed.

  Local Lemma CokernelKernelMorphism_comm2' (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                            (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                (CokernelKernelMorphism_comm1' C i) =
    (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Cokernel (Diff C (i - 1)))
              (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                           (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                       (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                           (CokernelKernelMorphism_comm1 C i))
              (CokernelKernelMorphism_comm2 C i))
      · (KernelArrow (Kernel (Diff C (i + 1)))).
  Proof.
    rewrite KernelCommutes. use CokernelOutsEq.
    rewrite CokernelCommutes. rewrite CokernelCommutes. apply idpath.
  Qed.

  Local Lemma CokernelKernelMorphism_uni (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    ∏ t : ∑ f : A ⟦Cokernel (Diff C (i - 1)), Kernel (Diff C (i + 1))⟧,
                (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (C i) (Diff C i)
                          (DSq (AbelianToAdditive A hs) C i) =
                 transportf (λ i0 : pr1 hz, A ⟦ C i0, Cokernel (Diff C (i - 1)) ⟧)
                            (hzrminusplus i 1) (CokernelArrow (Cokernel (Diff C (i - 1)))) · f)
                  × (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                                 (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                             (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                                 (CokernelKernelMorphism_comm1' C i) =
                     f · KernelArrow (Kernel (Diff C (i + 1)))),
  t =
  KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Cokernel (Diff C (i - 1)))
    (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
       (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧) (! maponpaths C (hzrminusplus i 1)) (Diff C i))
       (CokernelKernelMorphism_comm1 C i)) (CokernelKernelMorphism_comm2 C i),,
    CokernelKernelMorphism_comm3 C i,, CokernelKernelMorphism_comm2' C i.
  Proof.
    intros t. induction t as [t1 t2]. induction t2 as [t21 t22].
    use total2_paths_f.
    - cbn. use KernelInsEq. rewrite KernelCommutes.
      use CokernelOutsEq. rewrite CokernelCommutes.
      rewrite assoc.
      use transport_source_path.
      + exact (C i).
      + exact (! maponpaths C (hzrminusplus' i 1)).
      + rewrite transport_f_f. rewrite <- maponpathsinv0. rewrite <- maponpathsinv0.
        rewrite <- maponpathscomp0.
        assert (e0 : (! hzrminusplus i 1 @ ! hzrminusplus' i 1) = idpath _) by apply isasethz.
        cbn in e0. cbn. rewrite e0. clear e0. cbn. unfold idfun.
        rewrite transport_source_precompose. rewrite transport_source_precompose.
        rewrite <- functtransportf.
        assert (e1 : ! hzrminusplus' i 1 = hzrminusplus i 1) by apply isasethz.
        cbn in e1. rewrite e1. clear e1. rewrite <- t21.
        rewrite KernelCommutes. apply idpath.
    - apply proofirrelevance. apply isapropdirprod.
      + apply hs.
      + apply hs.
  Qed.

  Definition CokernelKernelMorphism (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    iscontr (∑ f : A⟦(CokernelComplex C) i, (KernelComplex C) i⟧,
                   ((KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (C i) (Diff C i) (DSq _ C i)) =
                    (transportf (λ (i0 : hz), A⟦C i0, (Cokernel (Diff C (i - 1)))⟧)
                                (hzrminusplus i 1)
                                (CokernelArrow (Cokernel (Diff C (i - 1))))) · f)
                     × ((CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                                     (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                                 (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                                     (CokernelKernelMorphism_comm1' C i)) =
                       f · (KernelArrow (Kernel (Diff C (i + 1)))))).
  Proof.
    use tpair.
    - use tpair.
      + cbn. use KernelIn.
        * use CokernelOut.
          -- exact (transportf (λ (x : A), A⟦x, C(i + 1)⟧) (! maponpaths C (hzrminusplus i 1))
                               (Diff C i)).
          -- exact (CokernelKernelMorphism_comm1 C i).
        * exact (CokernelKernelMorphism_comm2 C i).
      + cbn. split.
        * exact (CokernelKernelMorphism_comm3 C i).
        * exact (CokernelKernelMorphism_comm2' C i).
    - cbn. exact (CokernelKernelMorphism_uni C i).
  Defined.


  (** *** Kernel and cohomology *)

  Local Lemma CokernelKernelCohomology1_eq (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK := Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                   (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))) in
    (Diff C (i - 1))
      · (transportf (λ x' : A, A ⟦ x', CK⟧)
                     (! maponpaths C (hzrminusplus i 1)) (CokernelArrow CK)) =
    ZeroArrow (to_Zero A) _ _.
  Proof.
    induction (hzrminusplus i 1). cbn. unfold idfun. apply CokernelCompZero.
  Qed.

  Local Lemma CokernelKernelCohomology1_Mor1_eq1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                (Diff C (i - 1)))
      · (transportf (λ x' : A, A ⟦ x', Cokernel (Diff C (i - 1)) ⟧)
                     (maponpaths C (hzrminusplus i 1))
                     (CokernelArrow (Cokernel (Diff C (i - 1))))) = ZeroArrow (to_Zero A) _ _.
  Proof.
    rewrite transport_compose'. use CokernelCompZero.
  Qed.

  Local Lemma CokernelKernelCohomology1_Mor1_comm1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    KernelArrow
      (Kernel
         (CokernelOut (to_Zero A)
                      (Cokernel
                         (transportf (precategory_morphisms (C (i - 1)))
                                     (maponpaths C (hzrminusplus i 1))
                                     (Diff C (i - 1)))) (C (i + 1)) (Diff C i)
                      (CohomologyComplex_KernelIn_eq A hs C i))) ·
      CokernelOut (to_Zero A)
      (Cokernel
         (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                     (Diff C (i - 1))))
      (Cokernel (Diff C (i - 1)))
      (transportf (λ x' : A, A ⟦ x', Cokernel (Diff C (i - 1)) ⟧)
                  (maponpaths C (hzrminusplus i 1)) (CokernelArrow (Cokernel (Diff C (i - 1)))))
      (CokernelKernelCohomology1_Mor1_eq1 C i) ·
      KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Cokernel (Diff C (i - 1)))
      (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                   (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧) (! maponpaths C (hzrminusplus i 1))
                               (Diff C i))
                   (CokernelKernelMorphism_comm1 C i)) (CokernelKernelMorphism_comm2 C i) =
    ZeroArrow (to_Zero A) _ _.
  Proof.
    set (K := Kernel
                (CokernelOut (to_Zero A)
                             (Cokernel
                                (transportf (precategory_morphisms (C (i - 1)))
                                            (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                             (C (i + 1)) (Diff C i) (CohomologyComplex_KernelIn_eq A hs C i))).
    cbn. use (KernelArrowisMonic (to_Zero A) (Kernel (Diff C (i + 1)))).
    rewrite <- assoc. rewrite <- assoc. rewrite KernelCommutes. rewrite ZeroArrow_comp_left.
    cbn. cbn in K. fold K. rewrite <- (KernelCompZero (to_Zero A) K). apply cancel_precomposition.
    use CokernelOutsEq. rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
    use transport_source_path.
    - exact (C (i - 1 + 1)).
    - exact (! maponpaths C (hzrminusplus i 1)).
    - rewrite <- transport_source_precompose.
      set (tmp := CokernelCommutes
                    (to_Zero A) (Cokernel (Diff C (i - 1))) _ _ (CokernelKernelMorphism_comm1 C i)).
      cbn in tmp. cbn. rewrite tmp. clear tmp. rewrite transport_f_f.
      rewrite <- maponpathsinv0. rewrite <- maponpathscomp0.
      assert (e0 : (hzrminusplus i 1 @ ! hzrminusplus i 1) = idpath _) by apply isasethz.
      cbn. cbn in e0. rewrite e0. clear e0. cbn. unfold idfun. apply idpath.
  Qed.

  Definition CokernelKernelCohomology1_Mor1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    A⟦(((CohomologyFunctor A hs C) : Complex (AbelianToAdditive A hs)) i),
      (Kernel (pr1 (pr1 (CokernelKernelMorphism C i))))⟧.
  Proof.
    set (K := Kernel
                (CokernelOut (to_Zero A)
                             (Cokernel
                                (transportf (precategory_morphisms (C (i - 1)))
                                            (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
                             (C (i + 1)) (Diff C i) (CohomologyComplex_KernelIn_eq A hs C i))).
    use (compose (iso_inv_from_is_iso _ (CohomologyComplexIso_is_iso_i A hs C i))).
    use KernelIn.
    - cbn.
      use (compose (KernelArrow K)).
      use CokernelOut.
      + exact (transportf (λ x' : A, A ⟦x', Cokernel (Diff C (i - 1))⟧)
                          (maponpaths C (hzrminusplus i 1))
                          (CokernelArrow (Cokernel (Diff C (i - 1))))).
      + exact (CokernelKernelCohomology1_Mor1_eq1 C i).
    - exact (CokernelKernelCohomology1_Mor1_comm1 C i).
  Defined.

  Local Lemma CokernelKernelCohomology1_Mor2_comm1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    KernelArrow
      (Kernel
         (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Cokernel (Diff C (i - 1)))
                   (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                                (transportf (λ x : A, A ⟦x, C (i + 1)⟧)
                                            (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                                (CokernelKernelMorphism_comm1 C i))
                   (CokernelKernelMorphism_comm2 C i))) ·
      CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1)))
      (Cokernel
         (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                     (Diff C (i - 1))))
      (transportf (λ x' : A, A ⟦x', Cokernel
                                      (transportf (precategory_morphisms (C (i - 1)))
                                                  (maponpaths C (hzrminusplus i 1))
                                                  (Diff C (i - 1)))⟧)
                  (! maponpaths C (hzrminusplus i 1))
                  (CokernelArrow
                     (Cokernel
                        (transportf (precategory_morphisms (C (i - 1)))
                                    (maponpaths C (hzrminusplus i 1))
                                    (Diff C (i - 1)))))) (CokernelKernelCohomology1_eq C i) ·
      (CokernelOut (to_Zero A)
                   (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                         (maponpaths C (hzrminusplus i 1))
                                         (Diff C (i - 1)))) (C (i + 1)) (Diff C i)
                   (CohomologyComplex_KernelIn_eq A hs C i)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (CK := Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                    (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1)))).
    cbn. cbn in CK. fold CK.
    set (K := (Kernel
                 (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Cokernel (Diff C (i - 1)))
                           (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                                        (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                                    (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                                        (CokernelKernelMorphism_comm1 C i))
                           (CokernelKernelMorphism_comm2 C i)))).
    cbn. cbn in K. fold K.
    set (tmp := dirprod_pr2 (pr2 (pr1 (CokernelKernelMorphism C i)))).
    assert (e0 : CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) CK
                             (transportf (λ x' : A, A ⟦ x', CK ⟧)
                                         (! maponpaths C (hzrminusplus i 1))
                                         (CokernelArrow CK))
                             (CokernelKernelCohomology1_eq C i) · CokernelOut (to_Zero A) CK
                             (C (i + 1)) (Diff C i)
                             (CohomologyComplex_KernelIn_eq A hs C i) =
                 (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Cokernel (Diff C (i - 1)))
                           (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                                        (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                                    (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                                        (CokernelKernelMorphism_comm1 C i))
                           (CokernelKernelMorphism_comm2 C i)) · KernelArrow (Kernel _)).
    {
      use CokernelOutsEq. rewrite assoc. rewrite CokernelCommutes.
      use transport_source_path.
      + exact (C i).
      + exact (! maponpaths C (! hzrminusplus i 1)).
      + rewrite transport_source_precompose. rewrite transport_f_f.
        rewrite maponpathsinv0. rewrite pathsinv0inv0.
        assert (e0 : (! maponpaths C (hzrminusplus i 1) @ maponpaths C (hzrminusplus i 1)) =
                     maponpaths C (idpath _)).
        {
          rewrite <- maponpathsinv0. rewrite <- maponpathscomp0. apply maponpaths.
          apply isasethz.
        }
        cbn. cbn in e0. rewrite e0. clear e0. cbn. unfold idfun. rewrite CokernelCommutes.
        cbn in tmp. rewrite <- tmp. clear tmp.
        use transport_source_path.
        * exact (C (i - 1 + 1)).
        * exact (! maponpaths C (hzrminusplus i 1)).
        * rewrite transport_source_precompose. rewrite transport_source_precompose.
          rewrite transport_f_f. rewrite <- maponpathsinv0. rewrite <- maponpathscomp0.
          rewrite pathsinv0r. cbn. unfold idfun. rewrite CokernelCommutes.
          rewrite maponpathsinv0. apply idpath.
    }
    rewrite <- assoc. cbn in e0. rewrite e0. clear e0.
    rewrite KernelCommutes. unfold K.
    set (CKO := CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                            (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                        (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                            (CokernelKernelMorphism_comm1 C i)). cbn. cbn in CKO. fold CKO.
    set (K2 := Kernel (KernelIn (to_Zero A) (Kernel (Diff C (i + 1)))
                                (Cokernel (Diff C (i - 1))) CKO
                                (CokernelKernelMorphism_comm2 C i))).
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (KernelArrow (Kernel (Diff C (i + 1))))).
    rewrite <- (KernelCompZero (to_Zero A) K2).
    unfold CKO. unfold K2. clear K2. unfold CKO. clear CKO. cbn.
    rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0. use KernelCommutes.
  Qed.

  Definition CokernelKernelCohomology1_Mor2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    A⟦(Kernel (pr1 (pr1 (CokernelKernelMorphism C i)))),
      (((CohomologyFunctor A hs C) : Complex (AbelianToAdditive A hs)) i)⟧.
  Proof.
    use (postcompose (CohomologyComplexIso_Mor_i A hs C i)). cbn.
    use KernelIn.
    - use (compose (KernelArrow _)).
      use CokernelOut.
      + exact (transportf (λ x' : A, precategory_morphisms x' _)
                          (! maponpaths C (hzrminusplus i 1))
                          (CokernelArrow (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                                               (maponpaths C (hzrminusplus i 1))
                                                               (Diff C (i - 1)))))).
      + exact (CokernelKernelCohomology1_eq C i).
    - exact (CokernelKernelCohomology1_Mor2_comm1 C i).
  Defined.

  Local Lemma CokernelKernelCohomology1_id1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    CokernelKernelCohomology1_Mor2 C i · CokernelKernelCohomology1_Mor1 C i =
    identity (Kernel (pr1 (pr1 (CokernelKernelMorphism C i)))).
  Proof.
    unfold CokernelKernelCohomology1_Mor2. unfold postcompose.
    unfold CokernelKernelCohomology1_Mor1. cbn.
    (* Make the goal more readable *)
    set (K1 := Kernel
                 (CokernelOut (to_Zero A)
                              (Cokernel
                                 (transportf (precategory_morphisms (C (i - 1)))
                                             (maponpaths C (hzrminusplus i 1))
                                             (Diff C (i - 1)))) (C (i + 1)) (Diff C i)
                              (CohomologyComplex_KernelIn_eq A hs C i))).
    cbn in K1. fold K1.
    set (K2 := (Kernel
                  (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (Cokernel (Diff C (i - 1)))
                            (CokernelOut (to_Zero A) (Cokernel (Diff C (i - 1))) (C (i + 1))
                                         (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                                     (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                                         (CokernelKernelMorphism_comm1 C i))
                            (CokernelKernelMorphism_comm2 C i)))).
    cbn in K2. fold K2.
    set (CK1 := (Cokernel (Diff C (i - 1)))).
    set (CK2 := (Cokernel
                   (transportf (precategory_morphisms (C (i - 1))) (maponpaths C (hzrminusplus i 1))
                               (Diff C (i - 1))))). cbn in CK2. fold CK2.

    use KernelInsEq. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite KernelCommutes. rewrite id_left.
    (* Get rid of the inv_from_iso stuff *)
    assert (ee : ((CohomologyComplexIso_Mor_i A hs C i)
                    · (inv_from_iso
                          (CohomologyComplexIso_Mor_i A hs C i,,
                                                      CohomologyComplexIso_is_iso_i A hs C i) ·
                          (KernelArrow K1 · CokernelOut (to_Zero A) CK2 CK1
                                       (transportf
                                          (λ x' : A, A ⟦ x', CK1 ⟧)
                                          (maponpaths C (hzrminusplus i 1))
                                          (CokernelArrow CK1))
                                       (CokernelKernelCohomology1_Mor1_eq1 C i)))) =
                 (KernelArrow K1 · CokernelOut (to_Zero A) CK2 CK1
                              (transportf
                                 (λ x' : A, A ⟦ x', CK1 ⟧)
                                 (maponpaths C (hzrminusplus i 1))
                                 (CokernelArrow CK1))
                              (CokernelKernelCohomology1_Mor1_eq1 C i))).
    {
      rewrite assoc. rewrite assoc. apply cancel_postcomposition.
      assert (ee' : (CohomologyComplexIso_Mor_i A hs C i)
                      · (inv_from_iso ((CohomologyComplexIso_Mor_i A hs C i)
                                          ,, (CohomologyComplexIso_is_iso_i A hs C i))) =
                    identity _).
      {
        apply (iso_inv_after_iso (isopair _ (CohomologyComplexIso_is_iso_i A hs C i))).
      }
      cbn beta in ee'. rewrite ee'. clear ee'. apply id_left.
    }
    cbn in ee. cbn.
    apply (maponpaths
             (λ gg : _, KernelIn (to_Zero A) K1 K2
                                  (KernelArrow K2 · CokernelOut (to_Zero A) CK1 CK2
                                               (transportf (λ x' : A, A ⟦ x', CK2 ⟧)
                                                           (! maponpaths C (hzrminusplus i 1))
                                                           (CokernelArrow CK2))
                                               (CokernelKernelCohomology1_eq C i))
                                  (CokernelKernelCohomology1_Mor2_comm1 C i) · gg)) in ee.
    use (pathscomp0 ee). clear ee.
    (* Use KernelCommutes and CokernelCommutes to solve the goal *)
    rewrite assoc. rewrite KernelCommutes. rewrite <- id_right. rewrite <- assoc.
    apply cancel_precomposition. use CokernelOutsEq.
    rewrite id_right. rewrite assoc. rewrite CokernelCommutes.
    use transport_source_path.
    -- exact (C i).
    -- exact (! maponpaths C (! hzrminusplus i 1)).
    -- rewrite transport_source_precompose. rewrite transport_f_f.
       rewrite <- maponpathsinv0. rewrite <- maponpathsinv0. rewrite <- maponpathscomp0.
       rewrite pathsinv0inv0. rewrite pathsinv0l. cbn. unfold idfun.
       apply CokernelCommutes.
  Qed.

  Local Lemma CokernelKernelCohomology1_id2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    CokernelKernelCohomology1_Mor1 C i · CokernelKernelCohomology1_Mor2 C i =
    identity _.
  Proof.
    unfold CokernelKernelCohomology1_Mor2. unfold postcompose.
    unfold CokernelKernelCohomology1_Mor1. cbn.
    (* Make the goal more readable *)
    set (CK1 := (Cokernel (Diff C (i - 1)))).
    set (CK2 := (Cokernel (transportf (precategory_morphisms (C (i - 1)))
                                      (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))).
    cbn in CK2. fold CK2.
    set (K1 := Kernel (CokernelOut (to_Zero A) CK2 (C (i + 1)) (Diff C i)
                                   (CohomologyComplex_KernelIn_eq A hs C i))).
    set (K2 := Kernel
                 (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) CK1
                           (CokernelOut (to_Zero A) CK1 (C (i + 1))
                                        (transportf (λ x : A, A ⟦ x, C (i + 1) ⟧)
                                                    (! maponpaths C (hzrminusplus i 1)) (Diff C i))
                                        (CokernelKernelMorphism_comm1 C i))
                           (CokernelKernelMorphism_comm2 C i))).
    cbn in K2. fold K2.
    set (KI21 := KernelIn (to_Zero A) K2 K1
                          ((KernelArrow K1)
                             · (CokernelOut (to_Zero A) CK2 CK1
                                             (transportf (λ x' : A, A ⟦ x', CK1 ⟧)
                                                         (maponpaths C (hzrminusplus i 1))
                                                         (CokernelArrow CK1))
                                             (CokernelKernelCohomology1_Mor1_eq1 C i)))
                          (CokernelKernelCohomology1_Mor1_comm1 C i)).
    cbn in KI21. fold KI21.
    set (KI12 := KernelIn (to_Zero A) K1 K2
                          (KernelArrow K2 · CokernelOut (to_Zero A) CK1 CK2
                                       (transportf (λ x' : A, A ⟦ x', CK2 ⟧)
                                                   (! maponpaths C (hzrminusplus i 1))
                                                   (CokernelArrow CK2))
                                       (CokernelKernelCohomology1_eq C i))
                          (CokernelKernelCohomology1_Mor2_comm1 C i)).
    cbn in KI12. fold KI12.
    (* Begin to prove the equality *)
    (* Cancel the inv_from_iso *)
    use (pre_comp_with_iso_is_inj _ _ _ _ _ (CohomologyComplexIso_is_iso_i A hs C i)).
    rewrite assoc. rewrite assoc. rewrite assoc.
    assert (e : (CohomologyComplexIso_Mor_i A hs C i)
                  · (inv_from_iso ((CohomologyComplexIso_Mor_i A hs C i)
                                      ,, (CohomologyComplexIso_is_iso_i A hs C i))) = identity _).
    {
      apply (iso_inv_after_iso (isopair _ (CohomologyComplexIso_is_iso_i A hs C i))).
    }
    cbn beta in e. rewrite id_right.
    apply (maponpaths (λ gg : _, gg · KI21 · KI12 · CohomologyComplexIso_Mor_i A hs C i))
      in e.
    use (pathscomp0 e). clear e. rewrite id_left.
    (* Cancel the last morphism *)
    use (post_comp_with_iso_is_inj
           _ _ _ _  (is_iso_inv_from_iso (isopair _ (CohomologyComplexIso_is_iso_i A hs C i)))).
    rewrite <- assoc. rewrite <- assoc.
    assert (ee : (CohomologyComplexIso_Mor_i A hs C i)
                   · (inv_from_iso (isopair _ (CohomologyComplexIso_is_iso_i A hs C i))) =
                 identity _).
    {
      apply (iso_inv_after_iso (isopair _ (CohomologyComplexIso_is_iso_i A hs C i))).
    }
    cbn beta in ee. rewrite ee.
    apply (maponpaths (λ gg : _, KI21 · (KI12 · gg))) in ee. use (pathscomp0 ee). clear ee.
    rewrite id_right.
    (* Solve by using KernelInsEq *)
    unfold KI12, KI21. clear KI12 KI21. unfold K1, K2. clear K1 K2. unfold CK1, CK2. clear CK1 CK2.
    cbn.
    use KernelInsEq. rewrite <- assoc. rewrite KernelCommutes. rewrite assoc.
    rewrite KernelCommutes.
    rewrite id_left. rewrite <- id_right. rewrite <- assoc. apply cancel_precomposition.
    use CokernelOutsEq. rewrite assoc. rewrite CokernelCommutes. rewrite id_right.
    use transport_source_path.
    - exact (C (i - 1 + 1)).
    - exact (! maponpaths C (hzrminusplus i 1)).
    - rewrite transport_source_precompose. rewrite transport_f_f.
      rewrite <- maponpathsinv0. rewrite <- maponpathscomp0.
      rewrite pathsinv0r. cbn. unfold idfun. rewrite maponpathsinv0. apply CokernelCommutes.
  Qed.

  Definition CokernelKernelCohomology1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    iso (Kernel (pr1 (pr1 (CokernelKernelMorphism C i))))
        ((((CohomologyFunctor A hs C) : Complex (AbelianToAdditive A hs)) i)).
  Proof.
    use isopair.
    - exact (CokernelKernelCohomology1_Mor2 C i).
    - use is_iso_qinv.
      + exact (CokernelKernelCohomology1_Mor1 C i).
      + split.
        * exact (CokernelKernelCohomology1_id1 C i).
        * exact (CokernelKernelCohomology1_id2 C i).
  Defined.


  (** *** Cokernel and cohomology *)

  Local Lemma CokernelKernelCohomology2_comm1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    let CK := Cokernel (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (C (i + 1 - 1))
                                 (transportf (precategory_morphisms (C (i + 1 - 1)))
                                             (maponpaths C (hzrminusplus (i + 1) 1))
                                             (Diff C (i + 1 - 1)))
                                 (CohomologyComplex_KernelIn_eq A hs C (i + 1))) in
    pr1 (pr1 (CokernelKernelMorphism C i)) · CokernelArrow CK = ZeroArrow (to_Zero A) _ _.
  Proof.
    intros CK. cbn.
    assert (e0 : isEpi (transportf (λ i0 : pr1 hz, A ⟦C i0, Cokernel (Diff C (i - 1))⟧)
                                   (hzrminusplus i 1)
                                   (CokernelArrow (Cokernel (Diff C (i - 1)))))).
    {
      set (tmp' := transport_source_isEpi
                     A (CokernelArrow (Cokernel (Diff C (i - 1))))
                     (CokernelArrowisEpi _ _) (maponpaths C (hzrminusplus i 1))).
      rewrite <- functtransportf in tmp'. apply tmp'.
    }
    use e0. rewrite assoc. clear e0. rewrite ZeroArrow_comp_right.
    set (tmp := dirprod_pr1 (pr2 (pr1 (CokernelKernelMorphism C i)))).
    cbn in tmp. rewrite <- tmp. clear tmp.
    set (tmp := CokernelCompZero _ CK).
    use transport_source_path.
    - exact (C (i + 1 - 1)).
    - exact (! maponpaths C (hzrplusminus i 1)).
    - rewrite transport_source_ZeroArrow. cbn in tmp. rewrite <- tmp. clear tmp.
      rewrite transport_source_precompose. apply cancel_postcomposition. clear CK.
      rewrite transport_source_KernelIn. use KernelInsEq.
      rewrite KernelCommutes. rewrite KernelCommutes.
      apply pathsinv0. rewrite <- maponpathsinv0.
      use (pathscomp0 _ (transport_hz_section A C 1 (Diff C) _ _ (hzrplusminus i 1))).
      use transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Definition CokernelKernelCohomology2_Mor1 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    A⟦(Cokernel (pr1 (pr1 (CokernelKernelMorphism C i)))),
      ((((CohomologyFunctor A hs C) : Complex (AbelianToAdditive A hs)) (i + 1)))⟧.
  Proof.
    use CokernelOut.
    - use CokernelArrow.
    - exact (CokernelKernelCohomology2_comm1 C i).
  Defined.

  Local Lemma CokernelKernelCohomology2_comm2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (C (i + 1 - 1))
              (transportf (precategory_morphisms (C (i + 1 - 1)))
                          (maponpaths C (hzrminusplus (i + 1) 1))
                          (Diff C (i + 1 - 1))) (CohomologyComplex_KernelIn_eq A hs C (i + 1)))
      · (CokernelArrow (Cokernel (pr1 (pr1 (CokernelKernelMorphism C i))))) =
    ZeroArrow (to_Zero A) _ _.
  Proof.
    set (tmp := dirprod_pr1 (pr2 (pr1 (CokernelKernelMorphism C i)))).
    assert (e0 : KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (C (i + 1 - 1))
                          (transportf (precategory_morphisms (C (i + 1 - 1)))
                                      (maponpaths C (hzrminusplus (i + 1) 1))
                                      (Diff C (i + 1 - 1)))
                          (CohomologyComplex_KernelIn_eq A hs C (i + 1)) =
                 transportf (λ x' : ob A, precategory_morphisms x' _)
                            (! maponpaths C (hzrplusminus i 1))
                            (KernelIn (to_Zero A) (Kernel (Diff C (i + 1))) (C i) (Diff C i)
                                      (DSq (AbelianToAdditive A hs) C i))).
    {
      rewrite transport_source_KernelIn.
      use KernelInsEq.
      rewrite KernelCommutes. rewrite KernelCommutes. clear tmp.
      rewrite <- maponpathsinv0.
      use (pathscomp0 _ (transport_hz_section A C 1 (Diff C) _ _ (hzrplusminus i 1))).
      use transportf_paths. apply maponpaths. apply isasethz.
    }
    cbn in e0. cbn. rewrite e0. clear e0. rewrite tmp. clear tmp. cbn.
    rewrite transport_source_precompose. rewrite <- assoc. rewrite CokernelCompZero.
    apply ZeroArrow_comp_right.
  Qed.

  Definition CokernelKernelCohomology2_Mor2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    A⟦((((CohomologyFunctor A hs C) : Complex (AbelianToAdditive A hs)) (i + 1))),
      (Cokernel (pr1 (pr1 (CokernelKernelMorphism C i))))⟧.
  Proof.
    use CokernelOut.
    - use CokernelArrow.
    - exact (CokernelKernelCohomology2_comm2 C i).
  Defined.

  Local Lemma CokernelKernelCohomology2_inverses (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    is_inverse_in_precat (CokernelKernelCohomology2_Mor1 C i) (CokernelKernelCohomology2_Mor2 C i).
  Proof.
    split.
    - unfold CokernelKernelCohomology2_Mor1. use CokernelOutsEq.
      rewrite assoc. rewrite CokernelCommutes.
      unfold CokernelKernelCohomology2_Mor2.
      cbn. rewrite CokernelCommutes. rewrite id_right. apply idpath.
    - unfold CokernelKernelCohomology2_Mor2. use CokernelOutsEq.
      rewrite assoc. cbn. rewrite CokernelCommutes.
      unfold CokernelKernelCohomology2_Mor1.
      cbn. rewrite CokernelCommutes. rewrite id_right. apply idpath.
  Qed.

  Definition CokernelKernelCohomology2 (C : Complex (AbelianToAdditive A hs)) (i : hz) :
    iso (Cokernel (pr1 (pr1 (CokernelKernelMorphism C i))))
        ((((CohomologyFunctor A hs C) : Complex (AbelianToAdditive A hs)) (i + 1))).
  Proof.
    use isopair.
    - exact (CokernelKernelCohomology2_Mor1 C i).
    - use is_iso_qinv.
      + exact (CokernelKernelCohomology2_Mor2 C i).
      + exact (CokernelKernelCohomology2_inverses C i).
  Defined.

End def_kernel_cokernel_complex.

Local Transparent hz isdecrelhzeq hzplus iscommrngops.
Close Scope hz_scope.
