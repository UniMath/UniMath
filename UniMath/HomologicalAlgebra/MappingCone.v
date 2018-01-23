(** * Mapping cones in C(A) *)
(** ** Contents
- Definition of a mapping cone C(f)
- C(id)
- Rotation of triangles
- Inverse rotation of triangles
- Extension of triangles
- Octahedral axiom in K(A)
 *)

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
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Import UniMath.CategoryTheory.AdditiveFunctors.

Require Import UniMath.HomologicalAlgebra.Complexes.
Require Import UniMath.HomologicalAlgebra.KA.
Require Import UniMath.HomologicalAlgebra.TranslationFunctors.

Unset Kernel Term Sharing.

Local Open Scope hz_scope.
Local Open Scope cat.

Opaque hz isdecrelhzeq hzplus hzminus hzone hzzero iscommrngops ZeroArrow.

(** * Mapping cone *)
(** ** Introduction
In this section we construct the mapping cone, which is a complex, of a morphism f : C_1 -> C_2
of complexes. We denote mapping cone of f by Cone(f). The objects of mapping cone are given
by T C_1^i ⊕ C_2^i. The ith differential of Cone(f) is given by
         #  - p_1 · d^{i+1}_X · i_1 - i_2 · f^{i+1} · p_1 + p_2 · d^i_Y · i_2 #
         $  - p_1 · d^{i+1}_X · i_1 - i_2 · f^{i+1} · p_1 + p_2 · d^i_Y · i_2 $

We split the definition of the ith differential into a sum of 3 morphisms. These are constructed in
[MappingConeDiff1], [MappingConeDiff3], and [MappingConeDiff3], and correspond the morphisms of the
above formula, respectively. In [MappingConeDiff] we construct the differential. In
[MappingCone_comp] we show that composition of two consecutive differentials is 0. The complex
Cone(f) is constructed in [MappingCone].
*)
Section mapping_cone.

  Variable A : Additive.

  (**  # - (p_1 · d^{i+1}_{C_1} · i_1) # *)
  Definition MappingConeDiff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ to_BinDirectSums A (C1 (i + 1)) (C2 i), to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)) ⟧.
  Proof.
    intros DS1 DS2.
    use compose.
    - exact (TranslationComplex A C1 i).
    - exact (to_Pr1 A DS1).
    - use compose.
      + exact (TranslationComplex A C1 (i + 1)).
      + exact (DiffTranslationComplex A C1 i).
      + exact (to_In1 A DS2).
  Defined.

  (**  # (p_1 · f (i + 1) · i_2) # *)
  Definition MappingConeDiff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ to_BinDirectSums A (C1 (i + 1)) (C2 i), to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)) ⟧.
  Proof.
    intros DS1 DS2.
    use compose.
    - exact (TranslationComplex A C1 i).
    - exact (to_Pr1 A DS1).
    - use compose.
      + exact (C2 (i + 1)).
      + exact (f (i + 1)).
      + exact (to_In2 A DS2).
  Defined.

  (** # p2 · d^i_{C_2} · i2 # *)
  Definition MappingConeDiff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ to_BinDirectSums A (C1 (i + 1)) (C2 i), to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)) ⟧.
  Proof.
    intros DS1 DS2.
    use compose.
    - exact (C2 i).
    - exact (to_Pr2 A DS1).
    - use compose.
      + exact (C2 (i + 1)).
      + exact (Diff C2 i).
      + exact (to_In2 A DS2).
  Defined.

  Definition MappingConeDiff {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ to_BinDirectSums A (C1 (i + 1)) (C2 i), to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)) ⟧.
  Proof.
    intros DS1 DS2.
    use to_binop.
    - exact (MappingConeDiff1 f i).
    - use to_binop.
      +  exact (MappingConeDiff2 f i).
      +  exact (MappingConeDiff3 f i).
  Defined.

  Lemma MappingCone_Diff1_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff1 f i) · (MappingConeDiff1 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff1. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_IdIn1 A DS2). rewrite id_right. cbn.
    rewrite <- (assoc _ _ (DiffTranslationComplex A C1 (i + 1))). cbn.
    set (tmp := DiffTranslationComplex_comp A C1 i). cbn in tmp. cbn. rewrite tmp.
    rewrite ZeroArrow_comp_right. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff1_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff1 f i) · (MappingConeDiff3 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff1. unfold MappingConeDiff3. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A DS2)).
    rewrite (to_Unel1 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff2_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    let DS3 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1 + 1)) (C2 (i + 1 + 1)) in
    (MappingConeDiff2 f i) · (MappingConeDiff1 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2 DS3. unfold MappingConeDiff2. unfold MappingConeDiff1.
    fold DS1. fold DS2. fold DS3.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

   Lemma MappingCone_Diff2_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff2 f i) · (MappingConeDiff2 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff2. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff3_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff3 f i) · (MappingConeDiff1 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff3. unfold MappingConeDiff1. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff3_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff3 f i) · (MappingConeDiff2 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff3. unfold MappingConeDiff2. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff3_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    let DS3 := to_BinDirectSums A ((TranslationComplex A C1) (i + 1 + 1)) (C2 (i + 1 + 1)) in
    (MappingConeDiff3 f i) · (MappingConeDiff3 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2 DS3. unfold MappingConeDiff3. fold DS1. fold DS2. fold DS3.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A DS2)).
    rewrite (to_IdIn2 A DS2). rewrite id_right. rewrite <- (assoc _ _ (Diff C2 (i + 1))).
    rewrite (DSq A C2 i). rewrite ZeroArrow_comp_right. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_comp {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (to_binop _ _ (MappingConeDiff1 f i)
              (to_binop _ _ (MappingConeDiff2 f i) (MappingConeDiff3 f i)))
      · (to_binop _ _ (MappingConeDiff1 f (i + 1))
                   (to_binop _ _ (MappingConeDiff2 f (i + 1)) (MappingConeDiff3 f (i + 1)))) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1 + 1)) (C2 (i + 1 + 1))).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite (to_IdIn2 A DS2). rewrite (to_Unel2' DS2). rewrite id_right. rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_runax''. unfold DiffTranslationComplex.
    rewrite <- (assoc _ (to_In1 A DS2)). rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite (to_IdIn1 A DS2). rewrite (to_Unel1' DS2). rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite to_lunax''.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- (assoc _ (Diff C1 (i + 1))). rewrite DSq.
    rewrite <- (assoc _ (Diff C2 i)). rewrite DSq. rewrite inv_inv_eq.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_runax''. rewrite <- (assoc _ (f (i + 1))).
    rewrite (MComm f (i + 1)). rewrite assoc. rewrite (@to_linvax' A (Additive.to_Zero A)).
    apply idpath.
  Qed.

  Definition MappingCone {C1 C2 : Complex A} (f : Morphism C1 C2) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    - intros i. exact (MappingConeDiff f i).
    - intros i. exact (MappingCone_comp f i).
  Defined.

  (** In2 to MappingCone *)

  Local Lemma MappingConeIn2_comm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    to_In2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i)) · MappingConeDiff f i =
    Diff C2 i · to_In2 A (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
  Proof.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite to_premor_linear'. rewrite assoc. rewrite (to_Unel2' DS1).
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite to_premor_linear'. rewrite assoc. rewrite (to_Unel2' DS1).
    rewrite ZeroArrow_comp_left. rewrite to_lunax''. rewrite assoc.
    rewrite (to_IdIn2 _ DS1). apply id_left.
  Qed.

  Definition MappingConeIn2 {C1 C2 : Complex A} (f : Morphism C1 C2) : Morphism C2 (MappingCone f).
  Proof.
    use mk_Morphism.
    - intros i. exact (to_In2 _ (to_BinDirectSums A (TranslationComplex A C1 i) (C2 i))).
    - intros i. exact (MappingConeIn2_comm f i).
  Defined.

  (** Pr1 from MappingCone *)

  Local Lemma MappingConePr1_comm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i)) · to_inv (Diff C1 (i + 1)) =
    MappingConeDiff f i · to_Pr1 A (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
  Proof.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite to_postmor_linear'. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn1 _ DS2). rewrite id_right.
    rewrite to_postmor_linear'. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite <- assoc.
    rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite to_runax''. rewrite to_runax''. unfold DiffTranslationComplex.
    apply idpath.
  Qed.

  Definition MappingConePr1 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    Morphism (MappingCone f) (TranslationComplex A C1).
  Proof.
    use mk_Morphism.
    - intros i. exact (to_Pr1 _ (to_BinDirectSums A (TranslationComplex A C1 i) (C2 i))).
    - intros i. exact (MappingConePr1_comm f i).
  Defined.

End mapping_cone.


(** * Results on C(id) *)
(** ** Introduction
We show that for all objects X in K(A) we have the following isomorphism of triangles
                     X --> X -->   0   --> X[1]
                     |     |       |        |
                     X --> X --> C(id) --> X[1]
*)
Section mapping_cone_of_id.

  Variable A : Additive.

  Local Opaque precategory_morphisms InvTranslationFunctorHIm TranslationFunctorHIm
        ComplexHomotFunctor compose InvTranslationFunctorH TranslationFunctorH
        TranslationFunctor InvTranslationFunctor identity.

  Definition MappingConeIn2Homot (C : Complex A) :
    ComplexHomot A C (MappingCone A (@identity (ComplexPreCat_Additive A) C)).
  Proof.
    intros i.
    exact (transportf
             (λ x' : ob A, precategory_morphisms
                              x' ((MappingCone A (@identity (ComplexPreCat_Additive A) C)) (i - 1)))
             (maponpaths C (hzrminusplus i 1))
             (to_In1 A (to_BinDirectSums A (C (i - 1 + 1)) (C (i - 1))))).
  Defined.

  Lemma MappingConeIn2Eq (C : Complex A) :
    # (ComplexHomotFunctor A) (MappingConeIn2 A (@identity (ComplexPreCat_Additive A) C)) =
    # (ComplexHomotFunctor A) (ZeroArrow (Additive.to_Zero (ComplexPreCat_Additive A)) _ _).
  Proof.
    use ComplexHomotFunctor_rel_mor'.
    - exact (MappingConeIn2Homot C).
    - rewrite to_inv_zero. rewrite to_runax''. use MorphismEq. intros i. cbn.
      unfold MappingConeIn2Homot. unfold MappingConeDiff.
      unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
      set (DS1 := to_BinDirectSums A (C (i + 1)) (C i)).
      set (DS2 := to_BinDirectSums A (C (i - 1 + 1)) (C (i - 1))).
      set (DS3 := to_BinDirectSums A (C (i - 1 + 1 + 1)) (C (i - 1 + 1))).
      set (DS4 := to_BinDirectSums A (C (i + 1 - 1 + 1)) (C (i + 1 - 1))).
      rewrite id_left. rewrite to_premor_linear'. rewrite to_premor_linear'.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite <- transport_source_precompose. rewrite (to_IdIn1 A DS2).
      rewrite <- transport_source_precompose. rewrite id_left.
      rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
      rewrite id_left. rewrite <- transport_source_precompose.
      rewrite (to_Unel1' DS2). rewrite transport_source_ZeroArrow.
      rewrite ZeroArrow_comp_left. rewrite to_runax''.
      rewrite transport_source_to_binop. unfold DiffTranslationComplex.
      assert (e1 : (transportf
                      (precategory_morphisms (C i))
                      (maponpaths (λ i0 : pr1 hz, BinDirectSumOb
                                                    _ (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                  (hzrminusplus i 1))
                      (transportf (λ x' : A, A ⟦ x', DS3 ⟧) (maponpaths C (hzrminusplus i 1))
                                  (to_binop (C (i - 1 + 1)) DS3
                                            (to_inv (Diff C (i - 1 + 1)) · to_In1 A DS3)
                                            (to_In2 A DS3)))) =
                   to_binop (C i) DS1 (to_inv (Diff C i) · to_In1 A DS1) (to_In2 A DS1)).
      {
        unfold DS1, DS2, DS3, DS4.
        set (tmp := transport_hz_double_section_source_target
                      A C (λ (i0 : hz), to_BinDirectSums A (C (i0 + 1)) (C i0))
                      (λ (i0 : hz), to_binop (C i0) (to_BinDirectSums A (C (i0 + 1)) (C i0))
                                              (to_inv (Diff C i0)
                                                      · to_In1 A (to_BinDirectSums
                                                                     A (C (i0 + 1)) (C i0)))
                                (to_In2 A (to_BinDirectSums A (C (i0 + 1)) (C i0))))
                      _ _ (hzrminusplus i 1)).
        cbn beta in tmp. use (pathscomp0 _ (! tmp)). clear tmp. apply idpath.
      }
      apply (maponpaths (λ gg : _,
                           to_binop _ _ gg ((transportf
                                               (precategory_morphisms (C i))
                                               (maponpaths
                                                  (λ i0 : pr1 hz, BinDirectSumOb
                                                                    _  (to_BinDirectSums
                                                                          A (C (i0 + 1)) (C i0)))
                                                  (hzrplusminus i 1))
                                               (Diff C i · transportf (λ x' : A, A ⟦ x', DS4 ⟧)
                                                     (maponpaths C (hzrminusplus (i + 1) 1))
                                                     (to_In1 A DS4)))))) in e1.
      use (pathscomp0 _ (! e1)). clear e1.

      rewrite transport_target_postcompose.

      assert (e2 : transportf (precategory_morphisms (C (i + 1)))
                              (maponpaths (λ i0 : pr1 hz,
                                                  BinDirectSumOb
                                                    _ (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                          (hzrplusminus i 1))
                              (transportf (λ x' : A, A ⟦ x', DS4 ⟧)
                                          (maponpaths C (hzrminusplus (i + 1) 1))
                                          (to_In1 A DS4)) = to_In1 A DS1).
      {
        unfold DS1, DS2, DS3, DS4.
        set (tmp := transport_hz_double_section_source_target
                      A (λ i0 : hz, C (i0 + 1)) (λ (i0 : hz),
                                                    to_BinDirectSums A (C (i0 + 1)) (C i0))
                      (λ (i0 : hz), to_In1 A (to_BinDirectSums A (C (i0 + 1)) (C i0))) _ _
                      (hzrplusminus i 1)). cbn beta in tmp.
        use (pathscomp0 _ (! tmp)). clear tmp. apply maponpaths.
        assert (e3 : (maponpaths C (hzrminusplus (i + 1) 1)) =
                     (maponpaths (λ i0 : hz, C (i0 + 1)) (hzrplusminus i 1))).
        {
          assert (e4 : maponpaths (λ i0 : hz, C (i0 + 1)) (hzrplusminus i 1) =
                       maponpaths C (maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e4. clear e4. apply maponpaths. apply isasethz.
        }
        rewrite e3. apply idpath.
      }
      rewrite e2. clear e2. rewrite to_commax'. rewrite <- to_assoc.
      rewrite <- to_postmor_linear'. rewrite (@to_rinvax' A (Additive.to_Zero A)).
      rewrite ZeroArrow_comp_left. rewrite to_lunax''. apply idpath.
  Qed.

  Definition MappingConePr1Homot (C : Complex A) :
    ComplexHomot
      A (MappingCone A (@identity (ComplexPreCat_Additive A) C)) (TranslationComplex A C).
  Proof.
    intros i. cbn.
    exact (transportf (precategory_morphisms (to_BinDirectSums A (C (i + 1)) (C i)))
                      (maponpaths C (! hzrminusplus i 1))
                      (to_Pr2 A (to_BinDirectSums A (C (i + 1)) (C i)))).
  Defined.

  Lemma MappingConePr1Eq (C : Complex A) :
    # (ComplexHomotFunctor A) (MappingConePr1 A (@identity (ComplexPreCat_Additive A) C)) =
    # (ComplexHomotFunctor A) (ZeroArrow (Additive.to_Zero (ComplexPreCat_Additive A)) _ _).
  Proof.
    use ComplexHomotFunctor_rel_mor'.
    - exact (MappingConePr1Homot C).
    - rewrite to_inv_zero. rewrite to_runax''. use MorphismEq. intros i. cbn.
      unfold MappingConePr1Homot. unfold MappingConeDiff.
      unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
      set (DS1 := to_BinDirectSums A (C (i + 1)) (C i)).
      set (DS2 := to_BinDirectSums A (C (i + 1 + 1)) (C (i + 1))).
      rewrite id_left. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
      rewrite <- transport_target_postcompose. rewrite <- transport_target_postcompose.
      rewrite <- transport_target_postcompose. rewrite assoc. rewrite assoc.
      rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      rewrite (to_IdIn2 A DS2). rewrite id_right. rewrite id_right.
      rewrite (to_Unel1' DS2). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
      rewrite transport_target_ZeroArrow. rewrite (to_lunax'').
      assert (e1 : (transportf (precategory_morphisms DS1)
                               (maponpaths (λ i0 : pr1 hz, C (i0 + 1)) (hzrplusminus i 1))
                               (to_binop DS1 (C (i + 1 - 1 + 1))
                                         (transportf (precategory_morphisms DS1)
                                                     (maponpaths C (! hzrminusplus (i + 1) 1))
                                                     (to_Pr1 A DS1))
                                         (transportf (precategory_morphisms DS1)
                                                     (maponpaths C (! hzrminusplus (i + 1) 1))
                                                     (to_Pr2 A DS1 · Diff C i)))) =
                   to_binop DS1 (C (i + 1)) (to_Pr1 A DS1) (to_Pr2 A DS1 · Diff C i)).
      {
        unfold DS1, DS2.
        set (tmp := transport_hz_double_section_source_target
                      A (λ (i0 : hz), to_BinDirectSums A (C (i0 + 1)) (C i0))
                      (λ i0 : hz, C (i0 + 1))
                      (λ (i0 : hz), to_binop (to_BinDirectSums A (C (i0 + 1)) (C i0)) (C (i0 + 1))
                                              (to_Pr1 A (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                              (to_Pr2 A (to_BinDirectSums A (C (i0 + 1)) (C i0))
                                                      · Diff C i0))
                      _ _ (hzrplusminus i 1)). cbn beta in tmp.
        use (pathscomp0 _ (! tmp)). clear tmp. apply maponpaths.
        rewrite transport_target_to_binop.
        set (tmp := transport_hz_double_section
                      A (λ i0 : hz, to_BinDirectSums A (C (i0 + 1)) (C i0))
                      (λ (i0 : hz), C (i0 + 1))
                      (λ i0 : hz, (to_binop (to_BinDirectSums A (C (i0 + 1)) (C i0)) (C (i0 + 1))
                                             (to_Pr1 A (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                             (to_Pr2 A (to_BinDirectSums A (C (i0 + 1)) (C i0))
                                                     · Diff C i0))) _ _
                      (! hzrplusminus i 1)). cbn beta in tmp.
        assert (e2 : (maponpaths (λ i0 : hz, C (i0 + 1)) (! hzrplusminus i 1)) =
                     (maponpaths C (! hzrminusplus (i + 1) 1))).
        {
          assert (e3 : maponpaths (λ i0 : hz, C (i0 + 1)) (! hzrplusminus i 1) =
                       maponpaths C (maponpaths (λ (i0 : hz), i0 + 1) (! hzrplusminus i 1))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e3. clear e3. apply maponpaths. apply isasethz.
        }
        rewrite e2 in tmp. clear e2. use (pathscomp0 tmp). clear tmp.
        assert (e4 : (maponpaths (λ i0 : hz, BinDirectSumOb _ (to_BinDirectSums
                                                                     A (C (i0 + 1)) (C i0)))
                                 (! (! hzrplusminus i 1))) =
                     (maponpaths (λ i0 : hz, BinDirectSumOb
                                               _ (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                 (hzrplusminus i 1))).
        {
          apply maponpaths. apply isasethz.
        }
        rewrite e4. apply idpath.
      }
      apply (maponpaths (λ gg : _, to_binop
                                      _ _
                                      (transportf (precategory_morphisms DS1)
                                                  (maponpaths (λ i0 : pr1 hz, C (i0 + 1))
                                                              (hzrminusplus i 1))
                                                  (transportf (precategory_morphisms DS1)
                                                              (maponpaths C (! hzrminusplus i 1))
                                                              (to_Pr2 A DS1) ·
                                                              to_inv (Diff C (i - 1 + 1))))
                                      gg)) in e1.
      use (pathscomp0 _ (! e1)). clear e1.
      assert (e2 : (transportf (precategory_morphisms DS1) (maponpaths (λ i0 : pr1 hz, C (i0 + 1))
                                                                       (hzrminusplus i 1))
                               (transportf (precategory_morphisms DS1)
                                           (maponpaths C (! hzrminusplus i 1)) (to_Pr2 A DS1) ·
                                           to_inv (Diff C (i - 1 + 1)))) =
                   to_Pr2 A DS1 · to_inv (Diff C i)).
      {
        rewrite transport_target_postcompose.
        rewrite transport_compose. apply cancel_precomposition.
        rewrite <- transport_target_to_inv. rewrite <- transport_source_to_inv.
        apply maponpaths. rewrite <- maponpathsinv0. rewrite pathsinv0inv0.
        induction (hzrminusplus i 1). apply idpath.
      }
      apply (maponpaths (λ gg : _, to_binop _ _ gg
                                             (to_binop DS1 (C (i + 1)) (to_Pr1 A DS1)
                                                       (to_Pr2 A DS1 · Diff C i))))
        in e2.
      use (pathscomp0 _ (! e2)). clear e2.
      rewrite to_commax'. rewrite to_assoc. rewrite <- to_premor_linear'.
      rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite ZeroArrow_comp_right.
      rewrite to_runax''. apply idpath.
  Qed.

  Local Transparent precategory_morphisms identity ZeroArrow compose.

  Definition MappingConeIdHomot (C : Complex A) :
    ComplexHomot A (MappingCone A (@identity (ComplexPreCat_Additive A) C))
                 (MappingCone A (@identity (ComplexPreCat_Additive A) C)).
  Proof.
    intros i. cbn.
    exact ((to_Pr2 A (to_BinDirectSums A (C (i + 1)) (C i)))
             · (transportf
                   (λ x' : ob A, precategory_morphisms
                                    x' ((MappingCone A (@identity (ComplexPreCat_Additive A) C))
                                          (i - 1)))
                   (maponpaths C (hzrminusplus i 1))
                   (to_In1 A (to_BinDirectSums A (C (i - 1 + 1)) (C (i - 1)))))).
  Defined.

  Lemma IDMappingConeEq (C : Complex A) :
    # (ComplexHomotFunctor A) (@identity (ComplexPreCat_Additive A)
                                         (MappingCone A (@identity (ComplexPreCat_Additive A) C))) =
    # (ComplexHomotFunctor A) (ZeroArrow (Additive.to_Zero (ComplexPreCat_Additive A)) _ _).
  Proof.
    use ComplexHomotFunctor_rel_mor'.
    - exact (MappingConeIdHomot C).
    - rewrite to_inv_zero. rewrite to_runax''. use MorphismEq. intros i. cbn.
      use (pathscomp0 (! (to_BinOpId A (to_BinDirectSums A (C (i + 1)) (C i))))).
      unfold MappingConeIdHomot. unfold MappingConeDiff.
      unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
      rewrite id_left. rewrite id_left. cbn.
      set (DS1 := to_BinDirectSums A (C (i + 1)) (C i)).
      set (DS2 := to_BinDirectSums A (C (i - 1 + 1)) (C (i - 1))).
      set (DS3 := to_BinDirectSums A (C (i - 1 + 1 + 1)) (C (i - 1 + 1))).
      set (DS4 := to_BinDirectSums A (C (i + 1 + 1)) (C (i + 1))).
      set (DS5 := to_BinDirectSums A (C (i + 1 - 1 + 1)) (C (i + 1 - 1))).
      unfold DiffTranslationComplex.
      rewrite to_commax'.
      rewrite to_premor_linear'. rewrite to_premor_linear'.
      rewrite to_postmor_linear'. rewrite to_postmor_linear'.
      rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
      rewrite <- transport_source_precompose.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite assoc. rewrite assoc. rewrite (to_IdIn1 A DS2). rewrite id_left.
      rewrite id_left. rewrite (to_Unel1' DS2). rewrite ZeroArrow_comp_left.
      rewrite ZeroArrow_comp_left. rewrite transport_source_ZeroArrow.
      rewrite ZeroArrow_comp_right. rewrite to_runax''. rewrite <- to_premor_linear'.
      rewrite transport_target_postcompose.
      rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
      rewrite <- (assoc _ (to_In2 A DS4)). rewrite (to_Unel1' DS4).
      rewrite (to_IdIn2 A DS4). rewrite id_right. rewrite id_right.
      rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
      rewrite to_lunax''. rewrite <- to_postmor_linear'.
      rewrite transport_target_postcompose. rewrite <- transport_target_to_binop.
      assert (e1 : transportf (precategory_morphisms (C i))
                              (maponpaths (λ i0 : pr1 hz,
                                                  BinDirectSumOb
                                                    _ (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                          (hzrminusplus i 1))
                              (transportf (λ x' : A, A ⟦ x', DS3 ⟧)
                                          (maponpaths C (hzrminusplus i 1))
                                          (to_inv (Diff C (i - 1 + 1)) · to_In1 A DS3)) =
                   to_inv (Diff C i) · to_In1 A DS1).
      {
        unfold DS1.
        set (tmp := transport_hz_double_section_source_target
                      A C (λ i0 : hz, (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                      (λ i0 : hz, to_inv (Diff C i0)
                                          · to_In1 A (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                      _ _ (hzrminusplus i 1)). cbn beta in tmp.
        unfold DS3.
        exact (! tmp).
      }
      assert (e2 : transportf (precategory_morphisms (C i))
                              (maponpaths (λ i0 : pr1 hz, BinDirectSumOb
                                                    _ (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                          (hzrminusplus i 1))
                              (transportf (λ x' : A, A ⟦ x', DS3 ⟧)
                                          (maponpaths C (hzrminusplus i 1))
                                          (to_In2 A DS3)) =
                   to_In2 A DS1).
      {
        unfold DS1, DS3.
        set (tmp := transport_hz_double_section_source_target
                      A C (λ i0 : hz, (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                      (λ i0 : hz, to_In2 A (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                      _ _ (hzrminusplus i 1)). cbn beta in tmp.
        exact (! tmp).
      }
      set (e3 := to_binop_eq e1 e2).
      apply (maponpaths (λ gg : _, to_Pr2 A DS1 · gg)) in e3.
      apply (maponpaths
               (λ gg : _, to_binop
                             _ _ gg
                             (to_binop DS1 (C (i + 1)) (to_Pr1 A DS1)
                                       (to_Pr2 A DS1 · Diff C i) · transportf
                                       (precategory_morphisms (C (i + 1)))
                                       (maponpaths
                                          (λ i0 : pr1 hz,
                                                  BinDirectSumOb
                                                    _ (to_BinDirectSums
                                                         A (C (i0 + 1)) (C i0)))
                                          (hzrplusminus i 1))
                                       (transportf
                                          (λ x' : A, A ⟦ x', DS5 ⟧)
                                          (maponpaths C
                                                      (hzrminusplus (i + 1) 1))
                                          (to_In1 A DS5))))) in e3.
      use (pathscomp0 _ (! e3)). clear e3. clear e1 e2.
      assert (e4 : transportf
                     (precategory_morphisms (C (i + 1)))
                     (maponpaths (λ i0 : pr1 hz, BinDirectSumOb
                                                   _ (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                                 (hzrplusminus i 1))
                     (transportf (λ x' : A, A ⟦ x', DS5 ⟧)
                                 (maponpaths C (hzrminusplus (i + 1) 1)) (to_In1 A DS5)) =
                   to_In1 A DS1).
      {
        unfold DS1, DS5.
        set (tmp := transport_hz_double_section_source_target
                      A (λ i0 : hz, C (i0 + 1))
                      (λ i0 : hz, (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                      (λ i0 : hz, to_In1 A (to_BinDirectSums A (C (i0 + 1)) (C i0)))
                      _ _ (hzrplusminus i 1)). cbn beta in tmp.
        use (pathscomp0 _ (! tmp)). clear tmp.
        apply maponpaths.
        assert (e5 : (maponpaths C (hzrminusplus (i + 1) 1)) =
                     (maponpaths (λ i0 : hz, C (i0 + 1)) (hzrplusminus i 1))).
        {
          assert (e6 : maponpaths (λ i0 : hz, C (i0 + 1)) (hzrplusminus i 1) =
                       maponpaths C (maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e6. apply maponpaths. apply isasethz.
        }
        rewrite e5. apply idpath.
      }
      apply (maponpaths
               (λ gg : _, to_binop DS1 (to_BinDirectSums A (C (i + 1)) (C i))
                                    (to_Pr2 A DS1 · to_binop (C i) (to_BinDirectSums
                                                                       A (C (i + 1)) (C i))
                                            (to_inv (Diff C i) · to_In1 A DS1)
                                            (to_In2 A DS1))
                                    (to_binop DS1 (C (i + 1)) (to_Pr1 A DS1)
                                              (to_Pr2 A DS1 · Diff C i) · gg))) in e4.
      use (pathscomp0 _ (! e4)). clear e4.
      rewrite to_premor_linear'. rewrite to_postmor_linear'.
      rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp. rewrite assoc.
      rewrite (to_commax' A (to_inv (to_Pr2 A DS1 · Diff C i · to_In1 A DS1))).
      rewrite (to_commax' A _ (to_Pr2 A DS1 · Diff C i · to_In1 A DS1)).
      rewrite <- to_assoc. rewrite (to_assoc _ _ _ (to_Pr2 A DS1 · Diff C i · to_In1 A DS1)).
      rewrite (@to_linvax' A (Additive.to_Zero A)). rewrite to_runax''. apply idpath.
  Qed.

  Lemma IDMappingCone_is_z_isomorphism_inverses (C : Complex A) :
    is_inverse_in_precat
      (ZeroArrow (Additive.to_Zero (ComplexHomot_Additive A))
                 ((ComplexHomotFunctor A) (Additive.to_Zero (ComplexPreCat_Additive A)))
                 ((ComplexHomotFunctor A) (MappingCone A (@identity (ComplexPreCat_Additive A) C))))
      (ZeroArrow (Additive.to_Zero (ComplexHomot_Additive A))
                 ((ComplexHomotFunctor A) (MappingCone A (@identity (ComplexPreCat_Additive A) C)))
                 ((ComplexHomotFunctor A) (Additive.to_Zero (ComplexPreCat_Additive A)))).
  Proof.
    use mk_is_inverse_in_precat.
    - rewrite ZeroArrow_comp_left.
      use (@ArrowsToZero (ComplexHomot_Additive A) (Additive.to_Zero (ComplexHomot_Additive A))).
    - rewrite ZeroArrow_comp_left.
      use (pathscomp0 _ (functor_id (ComplexHomotFunctor A)
                                    (MappingCone A (@identity (ComplexPreCat_Additive A) C)))).
      use (pathscomp0 (! (AdditiveFunctorZeroArrow (ComplexHomotFunctor A) _ _))).
      exact (! (IDMappingConeEq C)).
  Qed.

  Lemma IDMappingCone_is_z_isomorphism (C : Complex A) :
    is_z_isomorphism
      (ZeroArrow (Additive.to_Zero (ComplexHomot_Additive A))
                 ((ComplexHomotFunctor A) (Additive.to_Zero (ComplexPreCat_Additive A)))
                 ((ComplexHomotFunctor A)
                    (MappingCone A (@identity (ComplexPreCat_Additive A) C)))).
  Proof.
    use mk_is_z_isomorphism.
    - exact (ZeroArrow (Additive.to_Zero (ComplexHomot_Additive A)) _ _).
    - exact (IDMappingCone_is_z_isomorphism_inverses C).
  Defined.

End mapping_cone_of_id.


(** * Rotation *)
(** ** Introduction
We prove results that are needed to prove that rotation of a distinguished triangle in K(A) is a
distinguished triangle. More precisely, we construct h in the following diagram
                          Y  --> C(f) --> X[1]  --> Y[1]
                          |       |       h |         |
                          Y  --> C(f) --> C(i2) --> Y[1]
here i2 : Y --> C(f) is the second inclusion. Also, we show that h is an isomorphism in K(A)
and that the above diagram is commutative in K(A).
*)
Section rotation_mapping_cone.

  Variable A : Additive.

  Local Lemma RotMorphismComm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    to_binop (C1 (i + 1)) (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
             ((to_inv (f (i + 1)))
                · to_In1 A (to_BinDirectSums
                               A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i))))
             ((to_In1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                · (to_In2 A (to_BinDirectSums
                                A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))))
             · MappingConeDiff A (MappingConeIn2 A f) i =
    to_inv (Diff C1 (i + 1)) · to_binop (C1 (i + 1 + 1))
           (to_BinDirectSums A (C2 (i + 1 + 1))
                             (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))))
           ((to_inv (f (i + 1 + 1)))
              · (to_In1 A (to_BinDirectSums A (C2 (i + 1 + 1))
                                             (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))))))
           (to_In1 A (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))) ·
                   to_In2 A
                   (to_BinDirectSums A (C2 (i + 1 + 1))
                                     (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))))).
  Proof.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C2 (i + 1 + 1)) DS3).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite (to_Unel2' DS2).
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite (to_IdIn2 A DS2).
    rewrite id_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite to_runax''. unfold DiffTranslationComplex.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    fold DS1 DS2 DS3 DS4. unfold DiffTranslationComplex.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite (to_Unel1' DS1). rewrite (to_IdIn1 A DS1).
    rewrite id_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite id_left.
    rewrite <- (assoc _ (to_In1 A DS2)). rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite (to_Unel1' DS2). rewrite (to_IdIn1 A DS2). rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''. rewrite to_lunax''.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite to_binop_inv_inv. rewrite <- to_assoc. rewrite <- to_assoc.
    rewrite (to_commax' _ _ (to_inv (Diff C1 (i + 1) · to_In1 A DS3 · to_In2 A DS4))).
    rewrite to_assoc. rewrite to_assoc. rewrite (@to_linvax' A (Additive.to_Zero _)).
    rewrite to_runax''. rewrite to_binop_inv_inv. apply maponpaths.
    rewrite to_commax'.
    use to_binop_eq.
    - apply cancel_postcomposition. rewrite <- PreAdditive_invrcomp.
      rewrite <- PreAdditive_invrcomp. apply maponpaths.
      exact (MComm f (i + 1)).
    - apply idpath.
  Qed.

  Definition RotMorphism {C1 C2 : Complex A} (f : Morphism C1 C2) :
    Morphism (TranslationComplex A C1) (MappingCone A (MappingConeIn2 A f)).
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      use to_binop.
      + use compose.
        * exact (C2 (i + 1)).
        * exact (to_inv (f (i + 1))).
        * exact (to_In1 A (to_BinDirectSums A (C2 (i + 1))
                                            (to_BinDirectSums A (C1 (i + 1)) (C2 i)))).
      + use compose.
        * exact (to_BinDirectSums A (C1 (i + 1)) (C2 i)).
        * exact (to_In1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
        * exact (to_In2 A (to_BinDirectSums A (C2 (i + 1))
                                            (to_BinDirectSums A (C1 (i + 1)) (C2 i)))).
    - intros i. exact (RotMorphismComm f i).
  Defined.

  Lemma RotMorphismInvComm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    to_Pr2 A (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i))) ·
           to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i)) · to_inv (Diff C1 (i + 1)) =
    MappingConeDiff A (MappingConeIn2 A f) i
                    · (to_Pr2 A (to_BinDirectSums
                                    A (C2 (i + 1 + 1))
                                    (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))) ·
                               to_Pr1 A (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
  Proof.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C2 (i + 1 + 1)) DS3).
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    fold DS1 DS2 DS3 DS4. unfold DiffTranslationComplex.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_IdIn2 A DS4). rewrite id_right. rewrite id_right.
    rewrite id_right. rewrite id_right.
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite (to_Unel1' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''.
    rewrite <- (assoc _ (to_In2 A DS3)). rewrite <- (assoc _ (to_In2 A DS3)).
    rewrite <- (assoc _ (to_In2 A DS3)). rewrite <- (assoc _ (to_In1 A DS3)).
    rewrite (to_Unel2' DS3). rewrite (to_IdIn1 A DS3). rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right. rewrite to_lunax''.
    rewrite to_lunax''. rewrite to_runax''. apply idpath.
  Qed.

  Definition RotMorphismInv {C1 C2 : Complex A} (f : Morphism C1 C2) :
    Morphism (MappingCone A (MappingConeIn2 A f)) (TranslationComplex A C1).
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      use compose.
      + exact (to_BinDirectSums A (C1 (i + 1)) (C2 i)).
      + exact (to_Pr2 A (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))).
      + exact (to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
    - intros i. exact (RotMorphismInvComm f i).
  Defined.

  Definition RotMorphismIsoHomot {C1 C2 : Complex A} (f : Morphism C1 C2)  :
    ComplexHomot A (MappingCone A (MappingConeIn2 A f)) (MappingCone A (MappingConeIn2 A f)).
  Proof.
    intros i. cbn.
    use compose.
    - exact (to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    - exact (to_Pr2 A (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))).
    - use compose.
      + exact (C2 i).
      + exact (to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + exact (transportf
                 (λ x' : ob A, precategory_morphisms
                                  x' (to_BinDirectSums
                                        A (C2 (i - 1 + 1))
                                        (to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1)))))
                 (maponpaths C2 (hzrminusplus i 1))
                 (to_In1 A (to_BinDirectSums A (C2 (i - 1 + 1))
                                             (to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1)))))).
  Defined.

  Lemma RotMorphismIsoEq1 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    (((RotMorphism f) : (ComplexPreCat_Additive A)⟦_, _⟧) · RotMorphismInv f) =
    (@identity (ComplexPreCat_Additive A) (TranslationComplex A C1)).
  Proof.
    use MorphismEq. intros i. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
    rewrite to_postmor_linear'. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In1 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite (to_IdIn2 A DS2). rewrite id_right. rewrite (to_Unel1' DS2).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. exact (to_IdIn1 A DS1).
  Qed.

  Local Lemma RotMorphismEq2' {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i) in
    let DS2 := to_BinDirectSums A (C2 (i + 1)) DS1 in
    to_binop DS2 DS2
             (to_binop DS2 DS2 (to_Pr2 A DS2 · to_Pr2 A DS1 · to_inv (Diff C2 i · to_In1 A DS2))
                       (to_Pr2 A DS2 · to_Pr2 A DS1 · (to_In2 A DS1 · to_In2 A DS2)))
             (to_binop DS2 DS2 (to_Pr1 A DS2 · to_In1 A DS2)
                       (to_binop DS2 DS2 (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)
                                 (to_Pr2 A DS2 · to_Pr2 A DS1 · Diff C2 i · to_In1 A DS2))) =
    to_binop DS2 DS2 (to_binop DS2 DS2 (to_Pr1 A DS2 · to_In1 A DS2)
                               (to_Pr2 A DS2 · to_In2 A DS2))
             (to_inv
                (to_binop DS2 DS2
                          (to_Pr2 A DS2 · to_Pr1 A DS1 · to_inv (f (i + 1)) · to_In1 A DS2)
                          (to_Pr2 A DS2 · to_Pr1 A DS1 · to_In1 A DS1 · to_In2 A DS2))).
  Proof.
    intros DS1 DS2. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite to_assoc. rewrite to_assoc.
    rewrite <- (to_assoc A _ (to_Pr1 A DS2 · to_In1 A DS2)).
    rewrite (to_commax' A _ (to_Pr1 A DS2 · to_In1 A DS2)).
    rewrite to_assoc.
    rewrite <- (to_assoc A _ (to_Pr1 A DS2 · to_In1 A DS2)).
    rewrite (to_commax' A _ (to_Pr1 A DS2 · to_In1 A DS2)).
    rewrite to_assoc. apply maponpaths.
    rewrite <- to_binop_inv_comm_2.
    rewrite <- (to_assoc A _ (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)).
    rewrite (to_commax' A _ (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)).
    rewrite to_assoc.
    rewrite <- (to_assoc A _ (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)).
    rewrite (to_commax' A _ (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)).
    rewrite to_assoc.
    rewrite <- (to_assoc A _ (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)).
    rewrite (to_commax' A _ (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)).
    rewrite to_assoc.
    apply maponpaths. rewrite assoc. rewrite assoc.
    rewrite (to_commax' A (to_Pr2 A DS2 · to_Pr2 A DS1 · to_In2 A DS1 · to_In2 A DS2)).
    rewrite <- to_assoc. rewrite (@to_linvax' A (Additive.to_Zero _)). rewrite to_lunax''.
    apply (to_rcan A (to_Pr2 A DS2 · to_Pr1 A DS1 · to_In1 A DS1 · to_In2 A DS2)).
    rewrite <- to_postmor_linear'. rewrite <- assoc. rewrite <- assoc.
    rewrite <- to_premor_linear'. rewrite to_commax'. rewrite (to_BinOpId A DS1).
    rewrite id_right.
    rewrite <- (@to_runax'' A (Additive.to_Zero A) _ _ (to_Pr2 A DS2 · to_In2 A DS2)).
    rewrite to_assoc. rewrite to_assoc. apply maponpaths. rewrite to_lunax''.
    rewrite assoc. rewrite (@to_linvax' A (Additive.to_Zero _)). apply idpath.
  Qed.

  Lemma RotMorphismIsoEq2'_eq {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i) in
    let DS2 := to_BinDirectSums A (C2 (i + 1)) DS1 in
    to_binop DS2 DS2
             (to_binop DS2 DS2 (to_Pr2 A DS2 · to_Pr2 A DS1 · to_inv (Diff C2 i · to_In1 A DS2))
                       (to_Pr2 A DS2 · to_Pr2 A DS1 · (to_In2 A DS1 · to_In2 A DS2)))
             (to_binop DS2 DS2 (to_Pr1 A DS2 · to_In1 A DS2)
                       (to_binop DS2 DS2 (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)
                                 (to_Pr2 A DS2 · to_Pr2 A DS1 · Diff C2 i · to_In1 A DS2))) =
    to_binop DS2 DS2 (identity DS2)
    (to_inv
       (to_Pr2 A DS2 · to_Pr1 A DS1 · to_binop (C1 (i + 1)) DS2
               (to_inv (f (i + 1)) · to_In1 A DS2)
               (to_In1 A DS1 · to_In2 A DS2))).
  Proof.
    intros DS1 DS2. use (pathscomp0 (RotMorphismEq2' f i)). fold DS1 DS2.
    rewrite (to_BinOpId A DS2). apply maponpaths. apply maponpaths.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. apply idpath.
  Qed.

  Lemma RotMorphismIsoEq2''_1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    transportf
      (precategory_morphisms
         (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i))))
      (@maponpaths
         hz A (λ i0 : pr1 hz, to_BinDirectSums
                                A (C2 (i0 + 1)) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
         _ _ (hzrminusplus i 1))
      (RotMorphismIsoHomot f i · MappingConeDiff A (MappingConeIn2 A f) (i - 1)) =
    to_binop (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
             (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
             (to_Pr2 A (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                     · to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))
                     · to_inv (Diff C2 i
                                     · to_In1 A
                                     (to_BinDirectSums
                                        A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))))
             (to_Pr2 A (to_BinDirectSums
                          A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                     · to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))
                     · (to_In2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))
                                · to_In2 A
                                (to_BinDirectSums A (C2 (i + 1))
                                                  (to_BinDirectSums A (C1 (i + 1)) (C2 i))))).
  Proof.
    unfold RotMorphismIsoHomot.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C2 (i + 1 + 1)) DS3).
    set (DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
    set (DS6 := to_BinDirectSums A (C2 (i - 1 + 1 + 1)) DS5).
    set (DS7 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
    set (DS8 := to_BinDirectSums A (C2 (i - 1 + 1)) DS7).
    set (DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS10 := to_BinDirectSums A (C2 (i + 1 - 1 + 1)) DS9).
    unfold DiffTranslationComplex.
    rewrite <- to_premor_linear'. rewrite assoc.
    rewrite transport_target_postcompose. rewrite <- assoc. apply cancel_precomposition.
    rewrite <- transport_source_precompose. rewrite <- transport_target_postcompose.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite assoc.
    rewrite (assoc (to_In1 A DS8)). rewrite (assoc (to_In1 A DS8)).
    rewrite (to_IdIn1 A DS8). rewrite (to_Unel1' DS8). rewrite id_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''. rewrite id_left.
    rewrite <- transport_target_to_binop. rewrite <- transport_source_to_binop.
    use to_binop_eq.
    + rewrite PreAdditive_invlcomp.
      unfold DS2, DS1, DS6, DS5.
      set (tmp := transport_hz_double_section_source_target
                    A C2
                    (λ i0 : hz, (to_BinDirectSums
                                    A (C2 (i0 + 1)) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                    (λ i0 : hz, to_inv (Diff C2 i0)
                                        · (to_In1
                                              A (to_BinDirectSums
                                                   A (C2 (i0 + 1))
                                                   (to_BinDirectSums
                                                      A (C1 (i0 + 1)) (C2 i0)))))
                    _ _ (hzrminusplus i 1)). cbn beta in tmp.
      use (pathscomp0 _ (! tmp)). clear tmp. rewrite transport_source_target_comm.
      apply idpath.
    + unfold DS2, DS1, DS6, DS5.
      set (tmp := transport_hz_double_section_source_target
                    A C2
                    (λ i0 : hz, (to_BinDirectSums
                                    A (C2 (i0 + 1)) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                    (λ i0 : hz, to_In2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)) · to_In2 A
                                        (to_BinDirectSums
                                           A (C2 (i0 + 1))
                                           (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                    _ _ (hzrminusplus i 1)). cbn beta in tmp.
      use (pathscomp0 _ (! tmp)). clear tmp. rewrite transport_source_target_comm.
      apply idpath.
  Qed.


  Lemma RotMorphismIsoEq2''_2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i) in
    let DS2 := to_BinDirectSums A (C2 (i + 1)) DS1 in
    let DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)) in
    let DS4 := to_BinDirectSums A (C2 (i + 1 + 1)) DS3 in
    let DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1)) in
    let DS10 := to_BinDirectSums A (C2 (i + 1 - 1 + 1)) DS9 in
    transportf
      (precategory_morphisms DS2)
      (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums
                                          A (C2 (i0 + 1))
                                          (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                   _ _ (hzrplusminus i 1))
      (to_Pr1 A DS2 · to_In2 A DS3 · (to_Pr2 A DS3 · transportf (λ x' : A, A ⟦ x', DS10 ⟧)
                                               (maponpaths C2 (hzrminusplus (i + 1) 1))
                                               (to_In1 A DS10))) = to_Pr1 A DS2 ·
                                                                          to_In1 A DS2.
  Proof.
    intros DS1 DS2 DS3 DS4 DS9 DS10.
    rewrite assoc. rewrite <- (assoc _ (to_In2 A DS3)). rewrite (to_IdIn2 A DS3).
    rewrite id_right. rewrite transport_target_postcompose. apply cancel_precomposition.
    set (tmp := transport_hz_double_section_source_target
                  A (λ i0 : hz, C2 (i0 + 1))
                  (λ i0 : hz, (to_BinDirectSums
                                  A (C2 (i0 + 1)) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                  (λ i0 : hz, to_In1 A (to_BinDirectSums
                                           A (C2 (i0 + 1))
                                           (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                  _ _ (hzrplusminus i 1)). cbn beta in tmp.
    use (pathscomp0 _ (! tmp)). clear tmp. apply maponpaths.
    assert (e2 : maponpaths (λ i0 : hz, C2 (i0 + 1)) (hzrplusminus i 1) =
                 maponpaths C2 (hzrminusplus (i + 1) 1)).
    {
      assert (e3 : maponpaths (λ i0 : hz, C2 (i0 + 1)) (hzrplusminus i 1) =
                   maponpaths C2 (maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1))).
      {
        induction (hzrplusminus i 1). apply idpath.
      }
      rewrite e3. apply maponpaths. apply isasethz.
        }
    rewrite e2. apply idpath.
  Qed.

  Lemma RotMorphismIsoEq2''_3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i) in
    let DS2 := to_BinDirectSums A (C2 (i + 1)) DS1 in
    let DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)) in
    let DS4 := to_BinDirectSums A (C2 (i + 1 + 1)) DS3 in
    let DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1)) in
    let DS10 := to_BinDirectSums A (C2 (i + 1 - 1 + 1)) DS9 in
    transportf (precategory_morphisms DS2)
               (@maponpaths
                  hz A (λ i0 : pr1 hz, to_BinDirectSums
                                         A (C2 (i0 + 1))
                                         (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                  _ _ (hzrplusminus i 1))
               (to_Pr2 A DS2 · MappingConeDiff A f i
                       · (to_Pr2 A DS3 · transportf (λ x' : A, A ⟦ x', DS10 ⟧)
                                  (maponpaths C2 (hzrminusplus (i + 1) 1))
                                  (to_In1 A DS10))) =
    to_binop DS2 DS2 (to_Pr2 A DS2 · to_Pr1 A DS1 · f (i + 1) · to_In1 A DS2)
             (to_Pr2 A DS2 · to_Pr2 A DS1 · Diff C2 i · to_In1 A DS2).
  Proof.
    intros DS1 DS2 DS3 DS4 DS9 DS10.
    rewrite transport_target_postcompose. rewrite <- (assoc (to_Pr2 A DS2)).
    rewrite <- (assoc (to_Pr2 A DS2)). rewrite <- (assoc (to_Pr2 A DS2)).
    rewrite <- (assoc (to_Pr2 A DS2)). rewrite <- assoc. rewrite <- assoc.
    rewrite <- to_premor_linear'. apply cancel_precomposition.
    rewrite assoc. rewrite <- to_postmor_linear'.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    fold DS1 DS2 DS3 DS4 DS9 DS10. rewrite assoc.
    unfold DiffTranslationComplex. rewrite transport_target_postcompose.
    rewrite assoc. rewrite to_postmor_linear'.
    rewrite (to_postmor_linear' _ _ (to_Pr2 A DS3)).
    rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A DS3)).
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite <- (assoc _ _ (to_Pr2 A DS3)).
    rewrite (to_Unel1' DS3). rewrite (to_IdIn2 A DS3). rewrite id_right. rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite to_lunax''. apply cancel_precomposition.
    set (tmp := transport_hz_double_section_source_target
                  A (λ i0 : hz, C2 (i0 + 1))
                  (λ i0 : hz, (to_BinDirectSums
                                  A (C2 (i0 + 1)) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                  (λ i0 : hz, to_In1 A (to_BinDirectSums
                                           A (C2 (i0 + 1))
                                           (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                  _ _ (hzrplusminus i 1)). cbn beta in tmp.
    use (pathscomp0 _ (! tmp)). clear tmp. apply maponpaths.
    assert (e2 : maponpaths (λ i0 : hz, C2 (i0 + 1)) (hzrplusminus i 1) =
                 maponpaths C2 (hzrminusplus (i + 1) 1)).
    {
      assert (e3 : maponpaths (λ i0 : hz, C2 (i0 + 1)) (hzrplusminus i 1) =
                   maponpaths C2 (maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1))).
      {
        induction (hzrplusminus i 1). apply idpath.
      }
      rewrite e3. apply maponpaths. apply isasethz.
    }
    rewrite e2. apply idpath.
  Qed.

  Lemma RotMorphismIsoEq2'' {C1 C2 : Complex A} (f : Morphism C1 C2) :
    to_binop ((MappingCone A (MappingConeIn2 A f)) : (ComplexPreCat_Additive A))
             ((MappingCone A (MappingConeIn2 A f)) : (ComplexPreCat_Additive A))
             (@identity (ComplexPreCat_Additive A) (MappingCone A (MappingConeIn2 A f)))
             (to_inv ((RotMorphismInv f : (ComplexPreCat_Additive A)⟦_, _⟧) · RotMorphism f)) =
    ComplexHomotMorphism A (RotMorphismIsoHomot f).
  Proof.
    use MorphismEq. intros i. cbn.
    apply pathsinv0. use (pathscomp0 _ (RotMorphismIsoEq2'_eq f i)).
    use to_binop_eq.
    - exact (RotMorphismIsoEq2''_1 f i).
    - unfold RotMorphismIsoHomot.
      unfold MappingConeDiff.
      unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
      unfold DiffTranslationComplex.
      set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
      set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
      set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
      set (DS4 := to_BinDirectSums A (C2 (i + 1 + 1)) DS3).
      set (DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
      set (DS6 := to_BinDirectSums A (C2 (i - 1 + 1 + 1)) DS5).
      set (DS7 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
      set (DS8 := to_BinDirectSums A (C2 (i - 1 + 1)) DS7).
      set (DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
      set (DS10 := to_BinDirectSums A (C2 (i + 1 - 1 + 1)) DS9).
      rewrite to_postmor_linear'. rewrite assoc. rewrite (assoc _ _ (to_In1 A DS4)).
      rewrite <- (assoc _ (to_In1 A DS4)). rewrite (to_Unel1' DS4).
      rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
      rewrite to_lunax''. rewrite assoc. rewrite (assoc _ _ (to_In2 A DS4)).
      rewrite (assoc _ _ (to_In2 A DS4)). rewrite to_postmor_linear'.
      rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
      rewrite (to_IdIn2 A DS4). rewrite id_right. rewrite id_right.
      rewrite to_postmor_linear'. rewrite <- transport_target_to_binop.
      use to_binop_eq.
      + exact (RotMorphismIsoEq2''_2 f i).
      + exact (RotMorphismIsoEq2''_3 f i).
  Qed.

  Lemma RotMorphism_is_z_isomorphism_inverses {C1 C2 : Complex A} (f : Morphism C1 C2) :
    is_inverse_in_precat (# (ComplexHomotFunctor A) (RotMorphism f))
                         (# (ComplexHomotFunctor A) (RotMorphismInv f)).
  Proof.
    use mk_is_inverse_in_precat.
    - rewrite <- functor_comp.
      rewrite <- (@functor_id _ _ (ComplexHomotFunctor A)).
      apply maponpaths. exact (RotMorphismIsoEq1 f).
    - rewrite <- functor_comp.
      rewrite <- (@functor_id _ _ (ComplexHomotFunctor A)).
      apply pathsinv0.
      use ComplexHomotFunctor_rel_mor'.
      + exact (RotMorphismIsoHomot f).
      + exact (RotMorphismIsoEq2'' f).
  Qed.

  Lemma RotMorphism_is_z_isomorphism {C1 C2 : Complex A} (f : Morphism C1 C2) :
    is_z_isomorphism (# (ComplexHomotFunctor A) (RotMorphism f)).
  Proof.
    use mk_is_z_isomorphism.
    - exact (# (ComplexHomotFunctor A) (RotMorphismInv f)).
    - exact (RotMorphism_is_z_isomorphism_inverses f).
  Defined.

  (** Commutativity of the middle square *)
  Definition RotMorphismCommHomot {C1 C2 : Complex A} (f : Morphism C1 C2) :
    ComplexHomot A (MappingCone A f) (MappingCone A (MappingConeIn2 A f)).
  Proof.
    intros i. cbn. use compose.
    - exact (C2 i).
    - exact (to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
    - exact (transportf (λ x' : ob A, precategory_morphisms
                                         x' (to_BinDirectSums A (C2 (i - 1 + 1))
                                                              (to_BinDirectSums A (C1 (i - 1 + 1))
                                                                                (C2 (i - 1)))))
                        (maponpaths C2 (hzrminusplus i 1))
                        (to_In1 A (to_BinDirectSums
                                     A (C2 (i - 1 + 1)) (to_BinDirectSums
                                                           A (C1 (i - 1 + 1)) (C2 (i - 1)))))).
  Defined.

  Definition RotMorphismCommMor1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A⟦ (MappingCone A f) i,
       to_BinDirectSums A (TranslationComplex A C2 (i - 1 + 1)) ((MappingCone A f) (i - 1 + 1)) ⟧.
  Proof.
    cbn.
    use to_binop.
    - use compose.
      + exact (C2 i).
      + exact (to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + use compose.
        * exact (C2 (i + 1)).
        * exact (to_inv (Diff C2 i)).
        * exact (transportf
                   (λ x' : ob A, precategory_morphisms
                                    x' (to_BinDirectSums
                                          A (C2 (i - 1 + 1 + 1))
                                          (to_BinDirectSums A (C1 (i - 1 + 1 + 1))
                                                            (C2 (i - 1 + 1)))))
                   (maponpaths C2 (maponpaths (λ i0 : hz, (i0 + 1)) (hzrminusplus i 1)))
                   (to_In1 A (to_BinDirectSums
                                A (C2 (i - 1 + 1 + 1))
                                (to_BinDirectSums
                                   A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1)))))).
    - use compose.
      + exact (C2 i).
      + exact (to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + use compose.
        * exact (to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
        * exact (transportf (λ x' : ob A, precategory_morphisms
                                             x' (to_BinDirectSums A (C1 (i - 1 + 1 + 1))
                                                                  (C2 (i - 1 + 1))))
                            (maponpaths C2 (hzrminusplus i 1))
                            (to_In2 A (to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))))).
        * exact (to_In2 A (to_BinDirectSums A (C2 (i - 1 + 1 + 1))
                                            (to_BinDirectSums
                                               A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))))).
  Defined.

  Lemma RotMorphismCommHomot1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    RotMorphismCommHomot f i · MappingConeDiff A (MappingConeIn2 A f) (i - 1) =
    RotMorphismCommMor1 f i.
  Proof.
    unfold RotMorphismCommHomot.
    unfold MappingConeDiff. cbn. unfold RotMorphismCommMor1. cbn.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
    set (DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
    set (DS6 := to_BinDirectSums A (C2 (i - 1 + 1 + 1)) DS5).
    set (DS7 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
    set (DS8 := to_BinDirectSums A (C2 (i - 1 + 1)) DS7).
    unfold DiffTranslationComplex.
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    use to_binop_eq.
    - rewrite <- assoc. apply cancel_precomposition.
      rewrite <- transport_source_precompose. rewrite assoc. rewrite (to_IdIn1 A DS8).
      rewrite id_left. induction (hzrminusplus i 1). apply idpath.
    - rewrite <- assoc. rewrite <- transport_source_precompose. rewrite assoc.
      rewrite (to_IdIn1 A DS8). rewrite id_left. rewrite <- assoc.
      rewrite <- transport_source_precompose. rewrite assoc.
      rewrite (to_Unel1' DS8). rewrite ZeroArrow_comp_left.
      rewrite transport_source_ZeroArrow. rewrite ZeroArrow_comp_right.
      rewrite to_runax''. rewrite <- transport_source_precompose. apply idpath.
  Qed.

  Definition RotMorphismCommMor2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A ⟦ to_BinDirectSums A (C1 (i + 1)) (C2 i),
        to_BinDirectSums
          A (C2 (i + 1 - 1 + 1)) (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) ⟧.
  Proof.
    cbn.
    use to_binop.
    - use compose.
      + exact (C1 (i + 1)).
      + exact (to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + use compose.
        * exact (C2 (i + 1)).
        * exact (f (i + 1)).
        * exact (transportf (λ x' : ob A, precategory_morphisms
                                             x' (to_BinDirectSums
                                                   A (C2 (i + 1 - 1 + 1))
                                                   (to_BinDirectSums A (C1 (i + 1 - 1 + 1))
                                                                     (C2 (i + 1 - 1)))))
                            (maponpaths C2 (hzrminusplus (i + 1) 1))
                            (to_In1 A (to_BinDirectSums
                                         A (C2 (i + 1 - 1 + 1))
                                         (to_BinDirectSums
                                            A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1)))))).
    - use compose.
      + exact (C2 i).
      + exact (to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + use compose.
        * exact (C2 (i + 1)).
        * exact (Diff C2 i).
        * exact (transportf (λ x' : ob A, precategory_morphisms
                                             x' (to_BinDirectSums
                                                   A (C2 (i + 1 - 1 + 1))
                                                   (to_BinDirectSums A (C1 (i + 1 - 1 + 1))
                                                                     (C2 (i + 1 - 1)))))
                            (maponpaths C2 (hzrminusplus (i + 1) 1))
                            (to_In1 A (to_BinDirectSums
                                         A (C2 (i + 1 - 1 + 1))
                                         (to_BinDirectSums
                                            A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1)))))).
  Defined.

  Lemma RotMorphismCommHomot2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    MappingConeDiff A f i · RotMorphismCommHomot f (i + 1) = RotMorphismCommMor2 f i.
  Proof.
    unfold RotMorphismCommHomot.
    unfold MappingConeDiff. cbn. unfold RotMorphismCommMor2. cbn.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS10 := to_BinDirectSums A (C2 (i + 1 - 1 + 1)) DS9).
    unfold DiffTranslationComplex.
    rewrite to_postmor_linear'. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_Unel1' DS3). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite to_postmor_linear'. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_IdIn2 A DS3). rewrite id_right.
    rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_IdIn2 A DS3). rewrite id_right.
    use to_binop_eq.
    - rewrite assoc. apply idpath.
    - rewrite assoc. apply idpath.
  Qed.

  Lemma RotMorphism_comm' {C1 C2 : Complex A} (f : Morphism C1 C2) :
    @to_binop (ComplexPreCat_Additive A) (MappingCone A f) (MappingCone A (MappingConeIn2 A f))
              (MappingConeIn2 A (MappingConeIn2 A f))
             (to_inv (((MappingConePr1 A f) : (ComplexPreCat_Additive A)⟦_, _⟧) · RotMorphism f)) =
    ComplexHomotMorphism A (RotMorphismCommHomot f).
  Proof.
    use MorphismEq. intros i. cbn. apply pathsinv0.
    use pathscomp0.
    - exact (to_binop (to_BinDirectSums A (C1 (i + 1)) (C2 i))
                      (to_BinDirectSums A (C2 (i + 1)) (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                      (transportf (precategory_morphisms (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                                  (@maponpaths
                                     hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                            A (C2 (i0 + 1))
                                                            (to_BinDirectSums
                                                               A (C1 (i0 + 1)) (C2 i0)))
                                     _ _ (hzrminusplus i 1)) (RotMorphismCommMor1 f i))
                      (transportf (precategory_morphisms (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                                  (@maponpaths
                                     hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                            A (C2 (i0 + 1))
                                                            (to_BinDirectSums
                                                               A (C1 (i0 + 1)) (C2 i0)))
                                     _ _ (hzrplusminus i 1)) (RotMorphismCommMor2 f i))).
    - use to_binop_eq.
      + apply maponpaths. exact (RotMorphismCommHomot1 f i).
      + apply maponpaths. exact (RotMorphismCommHomot2 f i).
    - unfold RotMorphismCommMor1, RotMorphismCommMor2. cbn.
      set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
      set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
      set (DS3 := to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
      set (DS4 := to_BinDirectSums A (C2 (i - 1 + 1 + 1)) DS3).
      set (DS5 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
      set (DS6 := to_BinDirectSums A (C2 (i + 1 - 1 + 1)) DS5).
      rewrite to_premor_linear'.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite <- transport_target_to_binop. rewrite <- transport_target_to_binop.
      rewrite transport_target_postcompose. rewrite transport_target_postcompose.
      rewrite transport_target_postcompose. rewrite transport_target_postcompose.
      rewrite (to_commax'
                 A _
                 (to_Pr2 A DS1 · Diff C2 i · transportf (precategory_morphisms (C2 (i + 1)))
                         (@maponpaths
                            hz A (λ i0 : pr1 hz,
                                         to_BinDirectSums
                                           A (C2 (i0 + 1))
                                           (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                            _ _ (hzrplusminus i 1))
                         (transportf (λ x' : A, A ⟦ x', DS6 ⟧)
                                     (maponpaths C2 (hzrminusplus (i + 1) 1))
                                     (to_In1 A DS6)))).
      rewrite to_assoc.
      rewrite (to_commax'
                 A (to_Pr2 A DS1 · transportf (λ x' : A, A ⟦ x', DS3 ⟧)
                           (maponpaths C2 (hzrminusplus i 1)) (to_In2 A DS3) ·
                           transportf (precategory_morphisms DS3)
                           (@maponpaths
                              hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                     A (C2 (i0 + 1))
                                                     (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                              _ _ (hzrminusplus i 1)) (to_In2 A DS4))).
      rewrite <- to_assoc. rewrite <- to_assoc. rewrite to_assoc.
      rewrite <- (@to_lunax''
                   A (Additive.to_Zero A) _ _
                   (to_binop DS1 DS2 (to_In2 A DS2)
                             (to_inv
                                (to_binop DS1 DS2
                                          (to_Pr1 A DS1 · to_inv (f (i + 1)) · to_In1 A DS2)
                                          (to_Pr1 A DS1 · to_In1 A DS1 · to_In2 A DS2))))).
      use to_binop_eq.
      + rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
        rewrite PreAdditive_invrcomp. rewrite <- to_premor_linear'.
        rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (to_Pr2 A DS1 · Diff C2 i)).
        apply cancel_precomposition.
        unfold DS2. unfold DS1.
        rewrite <- (@to_linvax'
                     A (Additive.to_Zero A) _ _
                     ((transportf (precategory_morphisms (C2 (i + 1)))
                                  (@maponpaths
                                     hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                            A (C2 (i0 + 1))
                                                            (to_BinDirectSums
                                                               A (C1 (i0 + 1)) (C2 i0)))
                                     _ _ (hzrplusminus i 1))
                                  (transportf (λ x' : A, A ⟦ x', DS6 ⟧)
                                              (maponpaths
                                                 C2 (hzrminusplus (i + 1) 1)) (to_In1 A DS6))))).
        use to_lrw. apply maponpaths.
        unfold DS4, DS3, DS6, DS5.
        set (tmp := @transport_hz_to_In1
                      A (λ i0 : hz, C2 (i0 + 1))
                      (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                      _ _ (hzrminusplus i 1)).
        cbn in tmp.
        assert (e : (maponpaths C2 (maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrminusplus i 1))) =
                    (maponpaths (λ i0 : pr1 hz, C2 (i0 + 1)) (hzrminusplus i 1))).
        {
          induction (hzrminusplus i 1). apply idpath.
        }
        cbn in e. rewrite e. clear e. use (pathscomp0 (! tmp)). clear tmp.
        set (tmp := @transport_hz_to_In1
                      A (λ i0 : hz, C2 (i0 + 1))
                      (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                      _ _ (hzrplusminus i 1)).
        cbn in tmp. use (pathscomp0 tmp). clear tmp.
        apply maponpaths.
        assert (e : (maponpaths (λ i0 : pr1 hz, C2 (i0 + 1)) (hzrplusminus i 1)) =
                    (maponpaths C2 (hzrminusplus (i + 1) 1))).
        {
          assert (e' : maponpaths (λ i0 : pr1 hz, C2 (i0 + 1)) (hzrplusminus i 1) =
                       maponpaths C2 (maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e'. apply maponpaths. apply isasethz.
        }
        rewrite e. apply idpath.
      + rewrite <- to_binop_inv_inv.
        rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp. rewrite inv_inv_eq.
        rewrite <- to_assoc. rewrite (to_commax' A (to_In2 A DS2)). rewrite to_assoc.
        use to_binop_eq.
        * apply cancel_precomposition.
          set (tmp := @transport_hz_to_In1
                        A (λ i0 : hz, C2 (i0 + 1))
                        (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                        _ _ (hzrplusminus i 1)).
          cbn in tmp. unfold DS2, DS1. use (pathscomp0 _ (! tmp)). clear tmp.
          apply maponpaths. unfold DS6, DS5.
          assert (e : (maponpaths (λ i0 : pr1 hz, C2 (i0 + 1)) (hzrplusminus i 1)) =
                      (maponpaths C2 (hzrminusplus (i + 1) 1))).
          {
            assert (e' : (maponpaths (λ i0 : pr1 hz, C2 (i0 + 1)) (hzrplusminus i 1)) =
                         (maponpaths C2 (maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrplusminus i 1)))).
            {
              induction (hzrplusminus i 1). apply idpath.
            }
            rewrite e'. apply maponpaths. apply isasethz.
          }
          rewrite e. apply idpath.
        * assert (e : to_binop DS1 DS2 (to_In2 A DS2)
                               (to_inv (to_Pr1 A DS1 · to_In1 A DS1 · to_In2 A DS2)) =
                      to_binop DS1 DS2 (identity _ · to_In2 A DS2)
                               (to_inv (to_Pr1 A DS1 · to_In1 A DS1 · to_In2 A DS2))).
          {
            rewrite id_left. apply idpath.
          }
          rewrite e. clear e. rewrite <- (to_BinOpId A DS1). rewrite to_postmor_linear'.
          rewrite to_commax'. rewrite <- to_assoc. rewrite (@to_linvax' A (Additive.to_Zero A)).
          rewrite to_lunax''. rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
          unfold DS4, DS3, DS2, DS1. induction (hzrminusplus i 1). apply idpath.
  Qed.

  Lemma RotMorphism_comm {C1 C2 : Complex A} (f : Morphism C1 C2) :
    # (ComplexHomotFunctor A) (((MappingConePr1 A f)
                                : (ComplexPreCat_Additive A)⟦_, _⟧) · RotMorphism f) =
    # (ComplexHomotFunctor A) (MappingConeIn2 A (MappingConeIn2 A f)).
  Proof.
    apply pathsinv0.
    use ComplexHomotFunctor_rel_mor'.
    - exact (RotMorphismCommHomot f).
    - exact (RotMorphism_comm' f).
  Qed.

  Lemma RotMorphism_comm2 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    to_inv (# (TranslationFunctor A) f) =
    (RotMorphism f : (ComplexPreCat_Additive A)⟦_, _⟧) · MappingConePr1 A (MappingConeIn2 A f).
  Proof.
    use MorphismEq. intros i. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C2 (i + 1)) DS1).
    rewrite to_postmor_linear'. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn1 A DS2). rewrite id_right. rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_right. rewrite to_runax''. apply idpath.
  Qed.

End rotation_mapping_cone.


(** * Inverse rotation *)
(** ** Introduction
We prove results that are needed to prove that inverse rotation of a distinguished triangle in
K(A) is a distinguished triangle. More precisely, we construct h in the following diagram
                      C(f)[-1]  -->  X  -->C(-p1[-1])--> C(f)
                          |          |       h |           |
                      C(f)[-1]  -->  X  -->    Y   -->   C(f)
here p1[-1] : C(f)[-1] --> X is the first projection. Also, we show that h is an isomorphism in K(A)
and that the above diagram is commutative in K(A).
*)
Section inv_rotation_mapping_cone.

  Variable A : Additive.

  Definition InvRotMorphismMor {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A ⟦ (MappingCone
           A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                     · z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1))) i, C2 i ⟧.
  Proof.
    cbn.
    use to_binop.
    + use compose.
      * exact (C1 i).
      * exact (to_Pr2 A (to_BinDirectSums A (to_BinDirectSums
                                               A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i))).
      * exact (f i).
    + use compose.
      * exact (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
      * exact (to_Pr1 A (to_BinDirectSums A (to_BinDirectSums
                                               A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i))).
      * exact (transportf (precategory_morphisms _) (maponpaths C2 (hzrplusminus i 1))
                          (to_Pr2 A (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))))).
  Defined.

  Lemma InvRotMorphismComm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    InvRotMorphismMor f i · Diff C2 i =
    MappingConeDiff
      A (MorphismComp
           (MorphismOp_inv A
                           (InvTranslationMorphism
                              A (MappingCone A f) (TranslationComplex A C1) (MappingConePr1 A f)))
           (TranslationEquivUnitInv A C1)) i · InvRotMorphismMor f (i + 1).
  Proof.
    unfold InvRotMorphismMor. unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    unfold DiffTranslationComplex. unfold InvTranslationComplex. cbn. unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    unfold DiffTranslationComplex. unfold InvTranslationComplex. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS2 := to_BinDirectSums A DS1 (C1 i)).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1 - 1 + 1)) (C2 (i + 1 + 1 - 1))).
    set (DS4 := to_BinDirectSums A DS3 (C1 (i + 1))).
    set (DS5 := to_BinDirectSums A (C1 (i + 1 - 1 + 1 + 1)) (C2 (i + 1 - 1 + 1))).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_Unel2' DS4). rewrite (to_IdIn2 A DS4). rewrite id_right. rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite to_runax''. rewrite <- transport_target_postcompose.
    rewrite <- transport_target_postcompose. rewrite <- transport_target_postcompose.
    rewrite id_right. rewrite transport_target_to_inv. rewrite inv_inv_eq.
    rewrite <- transport_target_postcompose.
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite <- (assoc _ (to_In1 A DS4)). rewrite (to_Unel1' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- transport_target_to_inv. rewrite <- to_assoc. rewrite to_commax'.
    rewrite <- (assoc _ (Diff C1 i)). rewrite <- (MComm f i). rewrite assoc.
    use to_binop_eq.
    - rewrite transport_target_postcompose. rewrite transport_target_postcompose.
      rewrite transport_target_postcompose. rewrite <- transport_target_to_binop.
      rewrite PreAdditive_invrcomp. rewrite PreAdditive_invrcomp.
      rewrite transport_target_postcompose. rewrite <- transport_target_to_binop.
      rewrite transport_target_postcompose. rewrite transport_target_postcompose.
      rewrite <- (assoc (to_Pr1 A DS2)). rewrite <- (assoc (to_Pr1 A DS2)).
      rewrite <- (assoc (to_Pr1 A DS2)). rewrite <- (assoc (to_Pr1 A DS2)).
      rewrite <- (assoc (to_Pr1 A DS2)). rewrite <- (assoc (to_Pr1 A DS2)).
      rewrite <- (assoc (to_Pr1 A DS2)). rewrite <- (assoc (to_Pr1 A DS2)).
      rewrite <- to_premor_linear'. rewrite <- to_premor_linear'.
      rewrite <- (assoc (to_Pr1 A DS2)). rewrite <- to_premor_linear'.
      apply cancel_precomposition. rewrite <- to_assoc.
      rewrite (to_commax'
                 A _
                 (((to_Pr2 A DS1) · (Diff C2 (i + 1 - 1))
                                  · (transportf
                                        (precategory_morphisms (C2 (i + 1 - 1 + 1)))
                                        (@maponpaths
                                           hz A
                                           (λ i0 : pr1 hz, to_BinDirectSums
                                                             A (C1 (i0 + 1)) (C2 i0))
                                           _ _ (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))
                                        (to_In2 A DS5))))).
      rewrite to_postmor_linear'. rewrite to_assoc.
      set (tmp := @to_runax'' A (Additive.to_Zero A) _ _
                              (transportf (precategory_morphisms DS1)
                                          (maponpaths C2 (hzrplusminus i 1)) (to_Pr2 A DS1) ·
                                          Diff C2 i)).
      use (pathscomp0 (! tmp)). clear tmp.
      use to_binop_eq.
      + rewrite transport_compose. rewrite <- assoc. rewrite <- assoc.
        apply cancel_precomposition. rewrite <- transport_target_postcompose.
        rewrite <- transport_target_postcompose. rewrite assoc.
        rewrite <- transport_target_postcompose.
        rewrite <- maponpathsinv0.
        set (tmp := transport_hz_section A C2 1 (Diff C2) _ _ (hzrplusminus i 1)).
        use (pathscomp0 (! tmp)). clear tmp. apply pathsinv0.
        rewrite transport_target_postcompose. rewrite transport_compose.
        rewrite <- (id_right (Diff C2 (i + 1 - 1))). rewrite transport_target_postcompose.
        rewrite id_right. rewrite <- assoc. apply cancel_precomposition.
        rewrite <- (to_IdIn2 A DS5). rewrite transport_target_postcompose.
        apply cancel_precomposition.
        assert (e : ! (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                   _ _ (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1)) =
                    @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                _ _ (! (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))).
        {
          rewrite maponpathsinv0. apply idpath.
        }
        rewrite e. clear e. unfold DS5.
        set (tmp := transport_hz_double_section
                      A (λ (i0 : hz), to_BinDirectSums
                                         A (C1 (i0 + 1 - 1 + 1 + 1)) (C2 (i0 + 1 - 1 + 1)))
                      (λ (i0 : hz), C2 (i0 + 1 - 1 + 1))
                      (λ (i0 : hz),
                         to_Pr2 A (to_BinDirectSums
                                     A (C1 (i0 + 1 - 1 + 1 + 1)) (C2 (i0 + 1 - 1 + 1))))
                      _ _ (! (hzrplusminus i 1))).
        cbn in tmp.
        set (e1 := maponpaths C2 (hzplusradd (i + 1 - 1) i 1 (hzrplusminus i 1))).
        set (e2 := maponpaths (λ i0 : pr1 hz, C2 (i0 + 1 - 1 + 1)) (! hzrplusminus i 1)).
        cbn in e1, e2.

        set (tmp' := transport_hz_double_section
                      A (λ (i0 : hz), to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                      C2
                      (λ (i0 : hz),
                         to_Pr2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                      _ _ (hzplusradd (i + 1 - 1) i 1 (hzrplusminus i 1))).
        cbn in tmp'. unfold e1.
        use (pathscomp0 _ (! tmp')). clear tmp'. unfold DS3.

        set (tmp' := transport_hz_double_section
                      A (λ (i0 : hz), to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                      C2
                      (λ (i0 : hz),
                         to_Pr2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                      _ _ (hzrplusminus (i + 1) 1)). cbn in tmp'.
        rewrite tmp'. clear tmp'. rewrite transport_f_f.
        assert (e : (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)) _ _
                                 (! hzrplusminus (i + 1) 1) @
                                 @maponpaths hz A  (λ i0 : pr1 hz, to_BinDirectSums
                                                                     A (C1 (i0 + 1)) (C2 i0)) _ _
                                 (! (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))) =
                    @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                _ _ (! hzplusradd (i + 1 - 1) i 1 (hzrplusminus i 1))).
        {
          set (tmp' := @maponpathscomp0
                         _ _ _ _ _
                         (λ i0 : pr1 hz,
                                 BinDirectSumOb _ (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                         (! hzrplusminus (i + 1) 1)
                         (! (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))).
          use (pathscomp0 (! tmp')). clear tmp'. apply maponpaths. apply isasethz.
        }
        cbn in e. cbn. rewrite e. clear e. apply idpath.
      + rewrite to_postmor_linear'. rewrite to_assoc. rewrite to_commax'.
        rewrite <- (@to_runax''
                     A (Additive.to_Zero A) _ _ (ZeroArrow (Additive.to_Zero A) DS1 (C2 (i + 1)))).
        use to_binop_eq.
        * rewrite <- PreAdditive_invlcomp.
          assert (e : (to_Pr1 A DS1 · f (i + 1 - 1 + 1)
                              · transportf (precategory_morphisms (C2 (i + 1 - 1 + 1)))
                              (@maponpaths
                                 hz A(λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                 _ _ (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))
                              (to_In2 A DS5) · transportf (precategory_morphisms DS3)
                              (maponpaths C2 (hzrplusminus (i + 1) 1))
                              (to_Pr2 A DS3)) =
                      (transportf (precategory_morphisms DS1)
                                  (maponpaths C1 (hzrminusplus (i + 1) 1))
                                  (to_Pr1 A DS1) · f (i + 1))).
          {
            rewrite transport_compose. rewrite <- assoc. rewrite <- assoc.
            apply cancel_precomposition.
            set (tmp := transport_hz_double_section A C1 C2 f _ _ (hzrminusplus (i + 1) 1)).
            rewrite <- maponpathsinv0. use (pathscomp0 _ tmp). clear tmp.
            rewrite <- (id_right (f (i + 1 - 1 + 1))). rewrite transport_target_postcompose.
            rewrite id_right. apply cancel_precomposition.
            rewrite <- (to_IdIn2 A DS5). rewrite transport_target_postcompose.
            rewrite transport_compose. apply cancel_precomposition.
            assert (e : ! (@maponpaths
                             hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                             _ _ (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1)) =
                        @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                    _ _ (! (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))).
            {
              rewrite maponpathsinv0. apply idpath.
            }
            rewrite e. clear e.
            unfold DS5.
            set (tmp' := transport_hz_double_section
                           A (λ (i0 : hz), to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                           C2
                           (λ (i0 : hz),
                              to_Pr2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                           _ _ (hzrminusplus (i + 1) 1)).
            cbn in tmp'.
            use (pathscomp0 _ (! tmp')). clear tmp'. unfold DS3.
            set (tmp' := transport_hz_double_section
                           A (λ (i0 : hz), to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                           C2
                           (λ (i0 : hz),
                              to_Pr2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                           _ _ (hzrplusminus (i + 1) 1)). cbn in tmp'.
            cbn. cbn in tmp'. rewrite tmp'. clear tmp'. rewrite transport_f_f.
            assert (e : (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                     _ _ (! hzrplusminus (i + 1) 1) @
                                     @maponpaths
                                     hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                     _ _ (! (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))) =
                        @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                    _ _ (! hzrminusplus (i + 1) 1)).
            {
              set (tmp' := @maponpathscomp0
                             _ _ _ _ _
                             (λ i0 : pr1 hz,
                                     BinDirectSumOb _ (to_BinDirectSums
                                                             A (C1 (i0 + 1)) (C2 i0)))
                             (! hzrplusminus (i + 1) 1)
                             (! (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))).
              use (pathscomp0 (! tmp')). clear tmp'. apply maponpaths. apply isasethz.
            }
            cbn in e. cbn. rewrite e. clear e. apply idpath.
          }
          apply (maponpaths
                   (λ g : _, to_binop _ _ g
                                       (to_inv
                                          (transportf (precategory_morphisms DS1)
                                                      (maponpaths C1 (hzrminusplus (i + 1) 1))
                                                      (to_Pr1 A DS1) · f (i + 1))))) in
              e.
          use (pathscomp0 _ (! e)). clear e. rewrite (@to_rinvax' A (Additive.to_Zero A)).
          apply idpath.
        * rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (to_Pr1 A DS1 · Diff C1 (i + 1 - 1 + 1))).
          rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
          apply cancel_precomposition. rewrite transport_compose.
          rewrite <- PreAdditive_invlcomp. rewrite <- to_inv_zero. apply maponpaths.
          set (DS6 := to_BinDirectSums A (C1 (i + 1 - 1 + 1 + 1)) (C2 (i + 1))).
          rewrite <- (to_Unel1' DS6). rewrite <- transport_compose. unfold DS3.
          set (tmp' := transport_hz_double_section
                         A (λ (i0 : hz), to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                         C2
                         (λ (i0 : hz),
                            to_Pr2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                         _ _ (hzrplusminus (i + 1) 1)). cbn in tmp'.
          rewrite tmp'. clear tmp'. rewrite transport_compose. rewrite transport_f_f.

          set (e := @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                _ _ (hzrplusminus (i + 1) 1)). cbn in e.
          unfold DS6. unfold DS5.
          set (e' := @maponpaths
                       hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i + 1 - 1 + 1 + 1)) (C2 i0))
                       _ _ (hzrminusplus (i + 1) 1)). cbn in e'.
          set (tmp := @transport_compose'
                        A _ _ _ _
                        (to_In1 A (to_BinDirectSums A (C1 (i + 1 - 1 + 1 + 1)) (C2 (i + 1))))
                        (to_Pr2 A (to_BinDirectSums A (C1 (i + 1 - 1 + 1 + 1)) (C2 (i + 1))))
                        (! e')).
          use (pathscomp0 (! tmp)). clear tmp. fold DS5 DS6. clear e.
          assert (e : transportf
                        (precategory_morphisms (C1 (i + 1 - 1 + 1 + 1))) (! e') (to_In1 A DS6) =
                      to_In1 A DS5).
          {
            unfold e'. unfold DS6, DS5. induction (hzrminusplus (i + 1) 1). apply idpath.
          }
          apply (maponpaths
                   (postcompose (transportf (λ x' : A, A ⟦ x', C2 (i + 1) ⟧) (! e')
                                            (to_Pr2 A DS6))))
            in  e.
          use (pathscomp0 e). clear e. unfold postcompose.
          apply cancel_precomposition.
          unfold e'. clear e'. unfold DS6.
          set (e1 := (! @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                           A (C1 (i + 1 - 1 + 1 + 1)) (C2 i0))
                        _ _ (hzrminusplus (i + 1) 1))).
          set (e2 := (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)) _ _
                                  (! hzrplusminus (i + 1) 1) @
                                  ! @maponpaths
                                  hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                  _ _ (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))).
          cbn in e1, e2. induction (hzrminusplus (i + 1) 1). cbn. unfold idfun. fold DS5.
          clear e1 e2.
          assert (e : (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                   _ _ (! hzrplusminus (i + 1 - 1 + 1) 1) @
                                   ! @maponpaths
                                   hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                   _ _ (! hzrplusminus (i + 1 - 1 + 1) 1)) = idpath _).
          {
            rewrite maponpathsinv0. rewrite <- pathscomp_inv. rewrite pathsinv0l. apply idpath.
          }
          apply (maponpaths
                   (λ g : _, transportf (λ x : A, A ⟦ x, C2 (i + 1 - 1 + 1) ⟧) g (to_Pr2 A DS5)))
            in e.
          use (pathscomp0 _ (! e)). apply idpath.
    - apply idpath.
  Qed.

  Definition InvRotMorphism {C1 C2 : Complex A} (f : Morphism C1 C2) :
    Morphism (MappingCone
                A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                          · z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1))) C2.
  Proof.
    use mk_Morphism.
    - intros i. exact (InvRotMorphismMor f i).
    - intros i. exact (InvRotMorphismComm f i).
  Defined.

  (** Commutativity of the middle square *)
  Lemma InvRotMorphismComm2 {C1 C2 : Complex A} (f : Morphism C1 C2 ) :
    ((MappingConeIn2 A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                               · z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1))
      : (ComplexPreCat_Additive A)⟦_, _⟧)) · InvRotMorphism f = f.
  Proof.
    use MorphismEq. intros i. cbn. unfold InvRotMorphismMor.
    set (DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS2 := to_BinDirectSums A DS1 (C1 i)).
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn2 A DS2). rewrite id_left. rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_left. rewrite to_runax''. apply idpath.
  Qed.

  (** Commutativity of the right square *)
  Definition InvRotMorphismComm3Homot {C1 C2 : Complex A} (f : Morphism C1 C2 ) :
    ComplexHomot
      A (MappingCone A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                               · z_iso_inv_mor
                               (AddEquivUnitIso (TranslationEquiv A) C1))) (MappingCone A f).
  Proof.
    intros i. cbn.
    use compose.
    - exact (C1 i).
    - exact (to_Pr2 A (to_BinDirectSums
                         A (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i))).
    - exact (transportf (λ x' : ob A, precategory_morphisms
                                         x' (to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))))
                        (maponpaths C1 (hzrminusplus i 1))
                        (to_In1 A (to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))))).
  Defined.

  Lemma InvRotMorphismComm3' {C1 C2 : Complex A} (f : Morphism C1 C2) :
    MorphismOp A (MorphismComp (InvRotMorphism f) (MappingConeIn2 A f))
               (MorphismOp_inv
                  A
                  (MorphismComp
                     (MappingConePr1
                        A
                        (MorphismComp
                           (MorphismOp_inv
                              A
                              (InvTranslationMorphism
                                 A (MappingCone A f) (TranslationComplex A C1)
                                 (MappingConePr1 A f)))
                           (TranslationEquivUnitInv A C1)))
                     (InvTranslationTranslationNatTrans_Mor A (MappingCone A f)))) =
    ComplexHomotMorphism A (InvRotMorphismComm3Homot f).
  Proof.
    use MorphismEq. intros i. cbn.
    unfold InvRotMorphismMor.
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    cbn. unfold InvRotMorphismComm3Homot. unfold DiffTranslationComplex. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS2 := to_BinDirectSums A DS1 (C1 i)).
    set (DS3 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS4 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
    set (DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
    set (DS6 := to_BinDirectSums A (C1 (i + 1 + 1 - 1 + 1)) (C2 (i + 1 + 1 - 1))).
    set (DS7 := to_BinDirectSums A DS6 (C1 (i + 1))).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- transport_target_postcompose. rewrite <- transport_target_postcompose.
    rewrite <- transport_target_postcompose. rewrite id_right. rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite <- (assoc _ _ (to_Pr2 A DS4)).
    rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
    rewrite (to_Unel1' DS4). rewrite (to_IdIn1 A DS4).
    rewrite transport_source_ZeroArrow. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS7)). rewrite <- (assoc _ _ (to_Pr2 A DS7)).
    rewrite (to_Unel1' DS7). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite (to_IdIn2 A DS7). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS7)). rewrite (to_IdIn2 A DS7). rewrite id_right.
    rewrite <- (assoc _ _ (to_inv (Diff C1 (i - 1 + 1)))).
    rewrite <- transport_source_precompose. rewrite id_left.
    rewrite <- (assoc _ _ (f (i - 1 + 1))).
    rewrite <- transport_source_precompose. rewrite id_left.
    rewrite <- transport_target_to_binop. rewrite <- transport_target_to_binop.
    rewrite transport_target_postcompose. rewrite transport_target_postcompose.
    rewrite transport_target_postcompose. rewrite transport_target_postcompose.
    rewrite transport_target_postcompose. rewrite transport_target_postcompose.
    cbn.
    rewrite (to_commax'
               A _ ((to_Pr2 A DS2 · transportf (λ x' : A, A ⟦ x', C2 (i - 1 + 1) ⟧)
                            (maponpaths C1 (hzrminusplus i 1))
                            (f (i - 1 + 1)) · transportf (precategory_morphisms (C2 (i - 1 + 1)))
                            (@maponpaths hz A
                                         (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                         _ _ (hzrminusplus i 1)) (to_In2 A DS5)))).
    rewrite to_assoc. rewrite to_assoc.
    use to_binop_eq.
    - rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
      set (tmp := @transport_hz_double_section A C1 C2 f _ _ (! hzrminusplus i 1)).
      rewrite pathsinv0inv0 in tmp. rewrite <- tmp. clear tmp.
      rewrite transport_compose. apply cancel_precomposition.
      rewrite maponpathsinv0. rewrite pathsinv0inv0. unfold DS3, DS5.
      induction (hzrminusplus i 1). apply idpath.
    - rewrite <- transport_target_to_inv. rewrite <- transport_source_to_inv.
      rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
      rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
      rewrite (to_commax'
                 A _ (to_Pr2 A DS2 · Diff C1 i · transportf (precategory_morphisms (C1 (i + 1)))
                             (@maponpaths
                                hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                _ _ (hzrplusminus i 1))
                             (transportf (λ x' : A, A ⟦ x', DS1 ⟧)
                                         (maponpaths C1 (hzrminusplus (i + 1) 1))
                                         (to_In1 A DS1)))).
      rewrite <- to_assoc.
      assert (e : (to_Pr2 A DS2 · transportf (λ x' : A, A ⟦ x', C1 (i - 1 + 1 + 1) ⟧)
                          (maponpaths C1 (hzrminusplus i 1)) (Diff C1 (i - 1 + 1)) ·
                          transportf (precategory_morphisms (C1 (i - 1 + 1 + 1)))
                          (@maponpaths
                             hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                    A (C1 (i0 + 1)) (C2 i0)) _ _
                             (hzrminusplus i 1))
                          (to_In1 A DS5)) =
                  (to_Pr2 A DS2 · Diff C1 i
                          · transportf (precategory_morphisms (C1 (i + 1)))
                          (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                              A (C1 (i0 + 1)) (C2 i0))
                                       _ _ (hzrplusminus i 1))
                          (transportf (λ x' : A, A ⟦ x', DS1 ⟧)
                                      (maponpaths C1 (hzrminusplus (i + 1) 1))
                                      (to_In1 A DS1)))).
      {
        rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
        set (tmp := @transport_hz_section A C1 1 (Diff C1) _ _ (! hzrminusplus i 1)).
        rewrite pathsinv0inv0 in tmp. rewrite <- tmp. clear tmp.
        rewrite transport_compose. apply cancel_precomposition.
        rewrite transport_source_target_comm. unfold DS5. unfold DS1.
        rewrite <- maponpathsinv0.
        assert (e : maponpaths C1 (! hzplusradd i (i - 1 + 1) 1 (! hzrminusplus i 1)) =
                    maponpaths C1 (hzplusradd (i - 1 + 1) i 1 (hzrminusplus i 1))).
        {
          apply maponpaths. apply isasethz.
        }
        rewrite e. clear e.
        set (tmp := @transport_hz_double_section_source_target
                      A (λ i0 : hz, C1 (i0 + 1))
                      (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                      (λ i0 : hz, to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                      _ _ (hzrminusplus i 1)). cbn in tmp.
        assert (e : maponpaths (λ i0 : pr1 hz, C1 (i0 + 1)) (hzrminusplus i 1) =
                    maponpaths C1 (hzplusradd (i - 1 + 1) i 1 (hzrminusplus i 1))).
        {
          induction (hzrminusplus i 1). apply idpath.
        }
        rewrite e in tmp. clear e. use (pathscomp0 (! tmp)). clear tmp.
        set (tmp := @transport_hz_double_section_source_target
                      A (λ i0 : hz, C1 (i0 + 1))
                      (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                      (λ i0 : hz, to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                      _ _ (hzrplusminus i 1)). cbn in tmp.
        use (pathscomp0 tmp). clear tmp. apply maponpaths.
        assert (e : maponpaths (λ i0 : pr1 hz, C1 (i0 + 1)) (hzrplusminus i 1) =
                    maponpaths C1 (hzrminusplus (i + 1) 1)).
        {
          assert (e' : maponpaths (λ i0 : pr1 hz, C1 (i0 + 1)) (hzrplusminus i 1) =
                       maponpaths C1 (maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrplusminus i 1))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e'. apply maponpaths. apply isasethz.
        }
        rewrite e. apply idpath.
      }
      apply (maponpaths
               (λ g : _,
                  to_binop DS2 (to_BinDirectSums A (C1 (i + 1)) (C2 i))
                           (to_inv
                              (to_Pr2 A DS2
                                      · transportf (λ x' : A, A ⟦ x', C1 (i - 1 + 1 + 1) ⟧)
                                      (maponpaths C1 (hzrminusplus i 1)) (Diff C1 (i - 1 + 1)) ·
                                      transportf (precategory_morphisms (C1 (i - 1 + 1 + 1)))
                                      (@maponpaths
                                         hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                                A (C1 (i0 + 1)) (C2 i0))
                                         _ _ (hzrminusplus i 1))
                                      (to_In1 A DS5))) g)) in e.
      apply (maponpaths
               (λ g : _,
                  to_binop DS2 (to_BinDirectSums A (C1 (i + 1)) (C2 i)) g
                           ((to_inv ((to_Pr1 A DS2)
                                       · (transportf
                                             (precategory_morphisms DS1)
                                             (maponpaths C1 (hzrminusplus (i + 1) 1))
                                             (to_Pr1 A DS1))
                                       · transportf (precategory_morphisms (C1 (i + 1)))
                                       (@maponpaths
                                          hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                                 A (C1 (i0 + 1)) (C2 i0))
                                          _ _ (hzrplusminus i 1))
                                       (transportf (λ x' : A, A ⟦ x', DS1 ⟧)
                                                   (maponpaths C1 (hzrminusplus (i + 1) 1))
                                                   (to_In1 A DS1))))))) in e.
      use (pathscomp0 _ e). clear e.
      rewrite (@to_linvax' A (Additive.to_Zero A)). rewrite to_lunax''.
      rewrite <- (id_right (to_Pr1 A DS2)). rewrite transport_target_postcompose.
      rewrite PreAdditive_invrcomp. rewrite id_right. rewrite <- assoc.
      rewrite <- assoc. rewrite PreAdditive_invrcomp.
      rewrite <- to_premor_linear'. apply cancel_precomposition.
      rewrite to_binop_inv_comm_2. apply maponpaths.
      rewrite <- (to_BinOpId A DS1).
      rewrite (to_commax' A (to_Pr1 A DS1 · to_In1 A DS1) _).
      rewrite <- transport_target_to_binop. rewrite <- to_assoc.
      assert (e : transportf (precategory_morphisms DS1) (maponpaths C2 (hzrplusminus i 1))
                             (to_Pr2 A DS1) ·  to_In2 A DS3 =
                  (transportf (precategory_morphisms DS1)
                              (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                                  A (C1 (i0 + 1)) (C2 i0))
                                           _ _ (hzrplusminus i 1))
                              (to_Pr2 A DS1 · to_In2 A DS1))).
      {
        rewrite transport_compose. rewrite transport_target_postcompose.
        apply cancel_precomposition. unfold DS1, DS3. induction (hzrplusminus i 1). apply idpath.
      }
      cbn in e. rewrite e. clear e. rewrite (@to_linvax' A (Additive.to_Zero A)).
      rewrite to_lunax''. rewrite transport_compose. rewrite transport_target_postcompose.
      apply cancel_precomposition. rewrite transport_source_target_comm.
      apply maponpaths. rewrite <- maponpathsinv0. rewrite transport_f_f.
      rewrite <- maponpathscomp0. rewrite pathsinv0r. apply idpath.
  Qed.

  Lemma InvRotMorphismComm3 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    # (ComplexHomotFunctor A) (((InvRotMorphism f) : (ComplexPreCat_Additive A)⟦_, _⟧)
                                 · (MappingConeIn2 A f)) =
    # (ComplexHomotFunctor A)
      (((MappingConePr1 A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                                  · z_iso_inv_mor
                                  (AddEquivUnitIso (TranslationEquiv A) C1)))
        : (ComplexPreCat_Additive A)⟦_, _⟧)
         · (AddEquivCounitIso (TranslationEquiv A) (MappingCone A f))).
  Proof.
    use ComplexHomotFunctor_rel_mor'.
    - exact (InvRotMorphismComm3Homot f).
    - exact (InvRotMorphismComm3' f).
  Qed.

  Definition InvRotMorphismMorInv {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A ⟦ C2 i, to_BinDirectSums
                A (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i) ⟧.
  Proof.
    use compose.
    - exact (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    - exact (transportf
               (λ x' : ob A, precategory_morphisms
                                x' (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))))
               (maponpaths C2 (hzrplusminus i 1))
               (to_In2 A (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))))).
    - exact (to_In1 A (to_BinDirectSums A (to_BinDirectSums
                                             A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i))).
  Defined.

  Lemma InvRotMorphismMorInvComm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (InvRotMorphismMorInv f i)
      · (MappingConeDiff A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f)) ·
                                    z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1)) i) =
    Diff C2 i · InvRotMorphismMorInv f (i + 1).
  Proof.
    unfold InvRotMorphismMorInv. unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    unfold DiffTranslationComplex. unfold InvTranslationComplex. cbn.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    unfold DiffTranslationComplex. unfold InvTranslationComplex. cbn.
    unfold InvRotMorphismMorInv.
    set (DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS2 := to_BinDirectSums A DS1 (C1 i)).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1 - 1 + 1)) (C2 (i + 1 + 1 - 1))).
    set (DS4 := to_BinDirectSums A DS3 (C1 (i + 1))).
    set (DS5 := to_BinDirectSums A (C1 (i + 1 - 1 + 1 + 1)) (C2 (i + 1 - 1 + 1))).
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite <- (assoc _ (to_In1 A DS2)). rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite (to_Unel1' DS2). rewrite (to_IdIn1 A DS2). rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite <- transport_source_precompose.
    rewrite <- transport_source_precompose.
    rewrite <- transport_source_precompose.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invrcomp.
    rewrite (to_Unel2' DS1). rewrite to_inv_zero.
    rewrite transport_source_ZeroArrow. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite <- transport_target_to_inv. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- transport_source_to_inv. rewrite <- transport_source_to_inv. rewrite inv_inv_eq.
    rewrite transport_source_precompose. apply cancel_postcomposition.
    rewrite <- transport_target_postcompose. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invrcomp. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn2 A DS1). rewrite id_left. rewrite (to_Unel2' DS1). rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_inv_zero. rewrite to_lunax''. rewrite to_lunax''.
    rewrite transport_target_postcompose. rewrite transport_source_precompose.
    set (tmp := @transport_compose'
                  A _ _ _ _ (Diff C2 i)
                  (transportf (λ x' : A, A ⟦ x', DS3 ⟧) (maponpaths C2 (hzrplusminus (i + 1) 1))
                              (to_In2 A DS3))
                  (maponpaths C2 (! hzrminusplus (i + 1) 1))).
    use (pathscomp0 _ tmp). clear tmp.
    set (tmp := transport_hz_section A C2 1 (Diff C2) _ _ (! hzrplusminus i 1)).
    assert (e : maponpaths C2 (hzplusradd i (i + 1 - 1) 1 (! hzrplusminus i 1)) =
                maponpaths C2 (! hzrminusplus (i + 1) 1)).
    {
      apply maponpaths. apply isasethz.
    }
    rewrite <- e. clear e. rewrite tmp. clear tmp. rewrite pathsinv0inv0.
    apply cancel_precomposition. rewrite transport_f_f. unfold DS5, DS3.
    rewrite <- maponpathscomp0.
    set (tmp := @transport_hz_double_section
                  A C2 (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                  (λ i0 : hz, to_In2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))) _ _
                  (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1)).
    cbn in tmp. use (pathscomp0 tmp).
    assert (e : (maponpaths C2 (! (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))) =
                (maponpaths
                   C2 (hzrplusminus (i + 1) 1 @ hzplusradd i (i + 1 - 1) 1 (! hzrplusminus i 1)))).
    {
      apply maponpaths. apply isasethz.
    }
    cbn in e. rewrite e. clear e. apply idpath.
  Qed.

  Definition InvRotMorphismInv {C1 C2 : Complex A} (f : Morphism C1 C2) :
    Morphism C2 (MappingCone A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f)) ·
                                       z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1))).
  Proof.
    use mk_Morphism.
    - intros i. exact (InvRotMorphismMorInv f i).
    - intros i. exact (InvRotMorphismMorInvComm f i).
  Defined.

  Lemma InvRotMorphism_is_iso_with_inv_eq1 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    # (ComplexHomotFunctor A) (((InvRotMorphismInv f) : (ComplexPreCat_Additive A)⟦_, _⟧)
                                 · InvRotMorphism f) =
    # (ComplexHomotFunctor A) (identity (C2 : (ComplexPreCat_Additive A))).
  Proof.
    apply maponpaths. unfold InvRotMorphismInv. unfold InvRotMorphism.
    use MorphismEq. intros i. cbn. unfold InvRotMorphismMorInv. unfold InvRotMorphismMor.
    set (DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS2 := to_BinDirectSums A DS1 (C1 i)).
    rewrite to_premor_linear'. rewrite assoc. rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite (to_Unel1' DS2). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite assoc. rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite (to_IdIn1 A DS2). rewrite id_right. induction (hzrplusminus i 1).
    cbn. unfold idfun. exact (to_IdIn2 A DS1).
  Qed.

  Definition InvRotMorphismIsoHomot {C1 C2 : Complex A} (f : Morphism C1 C2) :
    ComplexHomot
      A (MappingCone
           A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                     · z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1)))
      (MappingCone
         A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                   · z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1))).
  Proof.
    intros i. cbn.
    use compose.
    - exact (C1 i).
    - exact (to_Pr2 A (to_BinDirectSums
                         A (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i))).
    - use compose.
      + exact (to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 - 1))).
      + exact (transportf (λ x' : ob A, precategory_morphisms
                                           x' (to_BinDirectSums
                                                 A (C1 (i - 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 - 1))))
                          (maponpaths C1 (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))
                          (to_In1 A (to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1))
                                                      (C2 (i - 1 + 1 - 1))))).
      + exact (to_In1 A (to_BinDirectSums A (to_BinDirectSums
                                               A (C1 (i - 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 - 1)))
                                          (C1 (i - 1)))).
  Defined.

  Local Lemma InvRotMorphismIso'_eq2_1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1)) in
    let DS2 := to_BinDirectSums A DS1 (C1 i) in
    let DS3 := to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 - 1)) in
    let DS4 := to_BinDirectSums A DS3 (C1 (i - 1)) in
    let DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 + 1 - 1)) in
    let DS6 := to_BinDirectSums A DS5 (C1 (i - 1 + 1)) in
    let DS7 := to_BinDirectSums A (C1 (i + 1 + 1 - 1 + 1)) (C2 (i + 1 + 1 - 1)) in
    let DS8 := to_BinDirectSums A DS7 (C1 (i + 1)) in
    let DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1 - 1 + 1)) (C2 (i + 1 - 1 + 1 - 1)) in
    let DS10 := to_BinDirectSums A DS9 (C1 (i + 1 - 1)) in
    let DS11 := to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1 + 1)) (C2 (i - 1 + 1 - 1 + 1)) in
    to_inv
      (transportf
         (precategory_morphisms (C1 i))
         (@maponpaths
            hz A (λ i0 : pr1 hz,
                         to_BinDirectSums
                           A (to_BinDirectSums A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1))) (C1 i0))
            _ _ (hzrplusminus i 1))
         (Diff C1 i · (transportf
                          (λ x' : A, A ⟦ x', DS9 ⟧)
                          (maponpaths C1 (hzrminusplus (i + 1 - 1 + 1) 1 @ hzrminusplus (i + 1) 1))
                          (to_In1 A DS9) · to_In1 A DS10))) =
    to_inv
      (transportf
         (precategory_morphisms (C1 i))
         (@maponpaths
            hz A (λ i0 : pr1 hz,
                         to_BinDirectSums
                           A (to_BinDirectSums A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1))) (C1 i0))
            _ _ (hzrminusplus i 1))
         (transportf
            (λ x' : A, A ⟦ x', DS6 ⟧)
            (maponpaths C1 (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))
            (Diff C1 (i - 1 + 1 - 1 + 1) · to_In1 A DS11 · transportf (λ x' : A, A ⟦ x', DS6 ⟧)
                  (! @maponpaths
                     hz A (λ i0 : pr1 hz,
                                  to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                     _ _ (hzrminusplus (i - 1 + 1) 1 @
                                       ! hzrplusminus (i - 1 + 1) 1))
                  (to_In1 A DS6)))).
  Proof.
    intros DS1 DS2 DS3 DS4 DS5 DS6 DS7 DS8 DS9 DS10 DS11. cbn.
    apply maponpaths. rewrite transport_target_postcompose.
    rewrite transport_target_postcompose.
    rewrite transport_source_precompose.
    rewrite transport_source_precompose.
    rewrite transport_target_postcompose.
    set (tmp := @transport_hz_section
                  A C1 1 (Diff C1) _ _ (! (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))).
    rewrite pathsinv0inv0 in tmp. cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite transport_compose. rewrite <- assoc. apply cancel_precomposition.
    assert (e : (! maponpaths C1 (hzplusradd i (i - 1 + 1 - 1 + 1) 1
                                             (! (hzrminusplus (i - 1 + 1) 1 @
                                                              hzrminusplus i 1)))) =
                maponpaths C1 (hzplusradd (i - 1 + 1 - 1 + 1) i 1 (hzrminusplus (i - 1 + 1) 1 @
                                                                                hzrminusplus i 1))).
    {
      rewrite <- maponpathsinv0. apply maponpaths. apply isasethz.
    }
    cbn in e. rewrite e. clear e.

    set (tmp := @transport_hz_double_section
                  A (λ i0 : pr1 hz, C1 (i0 + 1))
                  (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                  (λ i0 : pr1 hz, to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                  _ _ (! (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))).
    cbn in tmp. unfold DS11. cbn. rewrite pathsinv0inv0 in tmp.
    assert (e : (maponpaths (λ i0 : pr1 hz, C1 (i0 + 1)) (hzrminusplus (i - 1 + 1) 1
                                                                       @ hzrminusplus i 1)) =
                (maponpaths C1 (hzplusradd (i - 1 + 1 - 1 + 1) i 1
                                           (hzrminusplus (i - 1 + 1) 1
                                                         @ hzrminusplus i 1)))).
    {
      induction (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1).
      apply idpath.
    }
    cbn in e. rewrite e in tmp. clear e. rewrite <- tmp. clear tmp.
    rewrite transport_compose.
    rewrite transport_source_target_comm. rewrite transport_f_f.
    set (tmp := @transport_hz_double_section
                  A (λ i0 : pr1 hz, C1 (i0 + 1))
                  (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                  (λ i0 : pr1 hz, to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                  _ _ (! (hzrplusminus (i + 1 - 1) 1 @ hzrplusminus i 1))).
    rewrite pathsinv0inv0 in tmp. unfold DS9.
    assert (e : (maponpaths C1 (hzrminusplus (i + 1 - 1 + 1) 1 @ hzrminusplus (i + 1) 1)) =
                (maponpaths (λ i0 : pr1 hz, C1 (i0 + 1)) (hzrplusminus (i + 1 - 1) 1
                                                                       @ hzrplusminus i 1))).
    {
      assert (e' : maponpaths (λ i0 : pr1 hz, C1 (i0 + 1)) (hzrplusminus (i + 1 - 1) 1
                                                                         @ hzrplusminus i 1) =
                   maponpaths C1 (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                             (hzrplusminus (i + 1 - 1) 1
                                                           @ hzrplusminus i 1))).
      {
        induction (hzrplusminus (i + 1 - 1) 1 @ hzrplusminus i 1).
        apply idpath.
      }
      rewrite e'. apply maponpaths. apply isasethz.
    }
    cbn in e. rewrite e. clear e. cbn. cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite transport_compose. apply cancel_precomposition.
    rewrite transport_source_target_comm.
    rewrite maponpathsinv0. rewrite pathsinv0inv0.
    rewrite maponpathsinv0. rewrite pathsinv0inv0.

    assert (e : (! @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                   _ _ (hzrminusplus (i - 1 + 1) 1 @ ! hzrplusminus (i - 1 + 1) 1) @
                   @maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                   _ _ (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1)) =
                (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                             _ _ (hzrplusminus (i - 1 + 1) 1 @ hzrminusplus i 1))).
    {
      rewrite maponpathscomp0.
      rewrite pathscomp_inv. rewrite maponpathsinv0. rewrite pathsinv0inv0.
      rewrite maponpathscomp0. rewrite maponpathscomp0.
      rewrite path_assoc.
      rewrite <- (path_assoc _ _ (@maponpaths
                                   hz A (λ i0 : pr1 hz,
                                                to_BinDirectSums
                                                  A (C1 (i0 + 1)) (C2 i0)) _ _
                                   (hzrminusplus (i - 1 + 1) 1))).
      rewrite pathsinv0l. rewrite pathscomp0rid. apply idpath.
    }
    apply (maponpaths
             (λ ee : _,
                transportf
                  (precategory_morphisms (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                  (@maponpaths
                     hz A (λ i0 : pr1 hz, to_BinDirectSums
                                            A (to_BinDirectSums
                                                 A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                            (C1 i0))
                     _ _ (hzrminusplus i 1))
                  (transportf (λ x' : A, A ⟦ x', DS6 ⟧) ee (to_In1 A DS6)))) in e.
    use (pathscomp0 _ (! e)). clear e.
    assert (e : (transportf
                   (λ x' : A, A ⟦ x', DS6 ⟧)
                   (@maponpaths hz A
                                (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                _ _ (hzrplusminus (i - 1 + 1) 1 @ hzrminusplus i 1))
                   (to_In1 A DS6)) =
                (transportf (λ x' : A, A ⟦ x', DS6 ⟧)
                            (@maponpaths hz A
                                         (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                         _ _ (hzrminusplus i 1))
                            (transportf (λ x' : A, A ⟦ x', DS6 ⟧)
                                        (@maponpaths
                                           hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                                  A (C1 (i0 + 1)) (C2 i0))
                                           _ _ (hzrplusminus (i - 1 + 1) 1))
                                        (to_In1 A DS6)))).
    {
      rewrite transport_f_f.
      rewrite maponpathscomp0.
      apply idpath.
    }
    apply (maponpaths
             (λ ee : _,
                transportf
                  (precategory_morphisms (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                  (@maponpaths
                     hz A (λ i0 : pr1 hz, to_BinDirectSums
                                            A (to_BinDirectSums
                                                 A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                            (C1 i0))
                     _ _ (hzrminusplus i 1)) ee)) in e.
    use (pathscomp0 _ (! e)). clear e.
    set (m1 := to_In1 A DS2). unfold DS2, DS1 in m1.
    set (e := @maponpaths hz A
                          (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                          _ _ (hzrplusminus i 1)).
    cbn in e.
    apply pathsinv0.

    use pathscomp0.
    - exact (transportf
               (λ x' : ob A, precategory_morphisms x' _)
               e
               (to_In1 A DS2)).
    - unfold DS10, DS9, DS6, DS5, DS2, DS1. unfold e.
      induction (hzrminusplus i 1). cbn. unfold idfun.
      apply idpath.
    - unfold DS10, DS9, DS6, DS5, DS2, DS1. unfold e. clear e.
      set (tmp := @transport_hz_to_In1'
                    A (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                    (λ i0 : hz, C1 i) _ _ (hzrplusminus i 1)).
      cbn in tmp. use (pathscomp0 (! tmp)). clear tmp.
      set (e := (@maponpaths
                   hz A (λ i0 : pr1 hz,
                                to_BinDirectSums
                                  A (to_BinDirectSums
                                       A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1))) (C1 i0))
                   _ _ (hzrplusminus i 1))). cbn in e.
      use transport_target_path.
      + exact (to_BinDirectSums
                 A (to_BinDirectSums
                      A (C1 (i + 1 - 1 + 1 - 1 + 1)) (C2 (i + 1 - 1 + 1 - 1)))
                 (C1 (i + 1 - 1))).
      + exact (! e).
      + unfold e. rewrite transport_f_f. rewrite transport_f_f.
        rewrite pathsinv0r. cbn. unfold idfun.

        set (tmp := @transport_hz_to_In1'
                      A (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                      (λ i0 : hz, C1 (i + 1 - 1)) _ _
                      (hzrplusminus (i + 1 - 1) 1 @ hzrplusminus i 1)).
        cbn in tmp. use (pathscomp0 _ tmp). clear tmp. clear e. clear m1.
        assert (e : @maponpaths
                      hz A (λ i0 : pr1 hz,
                                   to_BinDirectSums
                                     A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)) (C1 i))
                      _ _ (! hzrplusminus i 1) @
                      ! @maponpaths
                      hz A (λ i0 : pr1 hz,
                                   to_BinDirectSums
                                     A (to_BinDirectSums
                                          A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1))) (C1 i0))
                      _ _ (hzrplusminus i 1) =
                    ! (@maponpaths
                         hz A (λ i0 : pr1 hz,
                                      to_BinDirectSums
                                        A (to_BinDirectSums
                                             A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                        (C1 (i + 1 - 1)))
                         _ _ (hzrplusminus i 1) @
                         @maponpaths
                         hz A (λ i0 : pr1 hz,
                                      to_BinDirectSums
                                        A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)) (C1 i0))
                         _ _ (hzrplusminus i 1))).
        {
          rewrite maponpathsinv0.
          rewrite <- pathscomp_inv.
          apply maponpaths.
          set (tmp := @transport_to_BinDirectSums
                        A (λ i0 : hz, to_BinDirectSums
                                         A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                        (λ i0 : hz, C1 i0) _ _ (hzrplusminus i 1)).
          cbn in tmp.
          apply (maponpaths
                   (λ g : _, g @ @maponpaths
                                hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                       A (to_BinDirectSums
                                                            A (C1 (i0 + 1)) (C2 i0)) (C1 i))
                                _ _ (hzrplusminus i 1))) in tmp.
          cbn in tmp.
          use (pathscomp0 tmp). clear tmp. rewrite <- path_assoc.
          set (tmp := @transport_to_BinDirectSums_comm
                        A (λ i0 : hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                        (λ i0 : hz, C1 i0) _ _ (hzrplusminus i 1)).
          cbn in tmp.
          apply (maponpaths
                   (λ g : _, @maponpaths
                                hz A
                                (λ i0 : pr1 hz,
                                        to_BinDirectSums
                                          A (to_BinDirectSums
                                               A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                          (C1 (i + 1 - 1)))
                                _ _ (hzrplusminus i 1)@ g)) in tmp.
          use (pathscomp0 (! tmp)). clear tmp.
          apply maponpaths.
          set (tmp := @transport_to_BinDirectSums
                        A (λ i0 : hz, to_BinDirectSums
                                         A (C1 (i0 + 1)) (C2 i0))
                        (λ i0 : hz, C1 i0) _ _ (hzrplusminus i 1)).
          cbn in tmp. exact (! tmp).
        }
        cbn in e. rewrite e. clear e.
        rewrite pathscomp_inv. rewrite <- transport_f_f.
        set (tmp := @transport_to_BinDirectSums
                      A (λ i0 : hz, to_BinDirectSums
                                       A (C1 (i0 + 1)) (C2 i0))
                      (λ i0 : hz, C1 i0) _ _ (hzrplusminus i 1)).
        cbn in tmp. rewrite tmp. clear tmp. rewrite pathscomp_inv. rewrite <- transport_f_f.
        assert (e : transportf
                      (precategory_morphisms (to_BinDirectSums A (C1 (i + 1)) (C2 i)))
                      (@maponpaths hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                          A (to_BinDirectSums
                                                               A (C1 (i + 1)) (C2 i)) (C1 i0))
                                   _ _ (! hzrplusminus i 1))
                      (to_In1 A (to_BinDirectSums A (to_BinDirectSums
                                                       A (C1 (i + 1)) (C2 i)) (C1 i))) =
                    (to_In1 A (to_BinDirectSums
                                 A (to_BinDirectSums A (C1 (i + 1)) (C2 i)) (C1 (i + 1 - 1))))).
        {
          induction (hzrplusminus i 1). apply idpath.
        }
        rewrite maponpathsinv0 in e. cbn in e. rewrite e. clear e. rewrite transport_f_f.
        assert (e : (! @maponpaths
                       hz A
                       (λ i0 : pr1 hz, to_BinDirectSums
                                         A (to_BinDirectSums
                                              A (C1 (i0 + 1)) (C2 i0)) (C1 (i + 1 - 1)))
                       _ _ (hzrplusminus i 1) @
                       ! @maponpaths
                       hz A (λ i0 : pr1 hz,
                                    to_BinDirectSums
                                      A (to_BinDirectSums
                                           A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                      (C1 (i + 1 - 1)))
                       _ _ (hzrplusminus i 1)) =
                    (@maponpaths
                       hz A
                       (λ i0 : pr1 hz, to_BinDirectSums
                                         A (to_BinDirectSums
                                              A (C1 (i0 + 1)) (C2 i0)) (C1 (i + 1 - 1)))
                       _ _ (! (hzrplusminus (i + 1 - 1) 1 @ hzrplusminus i 1)))).
        {
          rewrite <- pathscomp_inv.
          assert (e' : @maponpaths
                         hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                A (to_BinDirectSums
                                                     A (C1 (i0 + 1)) (C2 i0)) (C1 (i + 1 - 1)))
                         _ _ (! (hzrplusminus (i + 1 - 1) 1 @ hzrplusminus i 1)) =
                       ! @maponpaths
                         hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                A (to_BinDirectSums
                                                     A (C1 (i0 + 1)) (C2 i0)) (C1 (i + 1 - 1)))
                         _ _ ((hzrplusminus (i + 1 - 1) 1 @ hzrplusminus i 1))).
          {
            rewrite maponpathsinv0. apply idpath.
          }
          use (pathscomp0 _ (! e')). clear e'.
          apply maponpaths.
          rewrite maponpathscomp0.
          assert (e' : @maponpaths
                         hz A
                         (λ i0 : pr1 hz,
                                 to_BinDirectSums
                                   A (to_BinDirectSums
                                        A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                   (C1 (i + 1 - 1)))
                         _ _ (hzrplusminus i 1) =
                       @maponpaths
                         hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                A (to_BinDirectSums
                                                     A (C1 (i0 + 1)) (C2 i0)) (C1 (i + 1 - 1)))
                         _ _ (hzrplusminus (i + 1 - 1) 1)).
          {
            assert (e'' : @maponpaths
                            hz A
                            (λ i0 : pr1 hz,
                                    to_BinDirectSums
                                      A (to_BinDirectSums
                                           A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                      (C1 (i + 1 - 1)))
                            _ _ (hzrplusminus i 1) =
                          @maponpaths
                            hz A (λ i0 : pr1 hz,
                                         to_BinDirectSums
                                           A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                           (C1 (i + 1 - 1)))
                            _ _ (maponpaths (λ i1 : hz, i1 + 1 - 1) (hzrplusminus i 1))).
            {
              induction (hzrplusminus i 1). apply idpath.
            }
            rewrite e''. clear e''. apply maponpaths. apply isasethz.
          }
          apply (maponpaths
                   (λ g : _, g @ (@maponpaths
                                     hz A (λ i0 : pr1 hz, to_BinDirectSums
                                                            A (to_BinDirectSums
                                                                 A (C1 (i0 + 1)) (C2 i0))
                                                            (C1 (i + 1 - 1)))
                                     _ _ (hzrplusminus i 1)))) in e'.
          exact e'.
        }
        cbn in e. rewrite e. apply idpath.
  Qed.

  Lemma InvRotMorphismIso'_eq2_2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1)) in
    let DS2 := to_BinDirectSums A DS1 (C1 i) in
    let DS3 := to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 - 1)) in
    let DS4 := to_BinDirectSums A DS3 (C1 (i - 1)) in
    let DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 + 1 - 1)) in
    let DS6 := to_BinDirectSums A DS5 (C1 (i - 1 + 1)) in
    let DS7 := to_BinDirectSums A (C1 (i + 1 + 1 - 1 + 1)) (C2 (i + 1 + 1 - 1)) in
    let DS8 := to_BinDirectSums A DS7 (C1 (i + 1)) in
    let DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1 - 1 + 1)) (C2 (i + 1 - 1 + 1 - 1)) in
    let DS10 := to_BinDirectSums A DS9 (C1 (i + 1 - 1)) in
    let DS11 := to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1 + 1)) (C2 (i - 1 + 1 - 1 + 1)) in
    to_inv
      (to_Pr2 A DS2 · (f i · transportf (λ x' : A, A ⟦ x', DS1 ⟧)
                          (maponpaths C2 (hzrplusminus i 1))
                          (to_In2 A DS1) · to_In1 A DS2)) =
    to_binop
        DS2 (to_BinDirectSums A (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i))
        (to_inv
           (to_Pr2 A DS2 · transportf (precategory_morphisms (C1 i))
                   (@maponpaths
                      hz A (λ i0 : pr1 hz,
                                   to_BinDirectSums
                                     A (to_BinDirectSums
                                          A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                     (C1 i0)) _ _ (hzrminusplus i 1))
                   (transportf (λ x' : A, A ⟦ x', DS6 ⟧)
                               (maponpaths C1 (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))
                               (transportf
                                  (precategory_morphisms (C1 (i - 1 + 1 - 1 + 1)))
                                  (@maponpaths
                                     hz A (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                                     _ _
                                     (hzrminusplus (i - 1 + 1) 1 @ ! hzrplusminus (i - 1 + 1) 1))
                                           (to_binop (C1 (i - 1 + 1 - 1 + 1)) DS11
                                                     (to_inv (Diff C1 (i - 1 + 1 - 1 + 1)) ·
                                                             to_In1 A DS11)
                                                     (f (i - 1 + 1 - 1 + 1) · to_In2 A DS11)) ·
                                           to_In1 A DS6))))
        (to_inv
           (to_Pr2 A DS2 · Diff C1 i · transportf (λ x' : A, A ⟦ x', DS9 ⟧)
                   (maponpaths C1
                               (hzrminusplus (i + 1 - 1 + 1) 1 @ hzrminusplus (i + 1) 1))
                   (to_In1 A DS9) · transportf (precategory_morphisms DS9)
                   (@maponpaths
                      hz A (λ i0 : pr1 hz,
                                   to_BinDirectSums A
                                                    (to_BinDirectSums A
                                                                      (C1 (i0 + 1 - 1 + 1))
                                                                      (C2 (i0 + 1 - 1)))
                                                    (C1 i0)) _ _ (hzrplusminus i 1))
                   (to_In1 A DS10))).
  Proof.
    intros DS1 DS2 DS3 DS4 DS5 DS6 DS7 DS8 DS9 DS10 DS11.
    cbn. rewrite to_binop_inv_inv. apply maponpaths. rewrite <- assoc. rewrite <- assoc.
    rewrite <- assoc. rewrite <- to_premor_linear'. apply cancel_precomposition.
    rewrite transport_compose. rewrite to_postmor_linear'.
    rewrite <- transport_source_to_binop. rewrite <- transport_target_to_binop.
    rewrite <- transport_target_postcompose. rewrite <- transport_target_postcompose.
    rewrite to_assoc. rewrite to_commax'. rewrite to_assoc.
    use (pathscomp0 (! (@to_runax''
                          A (Additive.to_Zero A) _ _
                          (f i · (transportf (λ x' : A, A ⟦ x', DS1 ⟧)
                                              (maponpaths C2 (hzrplusminus i 1))
                                              (to_In2 A DS1) ·
                                              to_In1 A DS2))))).
    use to_binop_eq.
    - rewrite <- transport_compose.
      rewrite transport_source_precompose.
      use (transport_target_path
             _ _ (! (@maponpaths
                       hz A
                       (λ i0 : pr1 hz, to_BinDirectSums
                                         A (to_BinDirectSums
                                              A (C1 (i0 + 1 - 1 + 1))
                                              (C2 (i0 + 1 - 1))) (C1 i0))
                       _ _ (hzrminusplus i 1)))).
      rewrite transport_f_f. rewrite pathsinv0r. cbn. unfold idfun.
      rewrite transport_target_postcompose. rewrite transport_target_postcompose.
      rewrite transport_target_postcompose. rewrite transport_source_precompose.
      set (tmp := @transport_hz_double_section
                    A C1 C2 f _ _ (! (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))).
      rewrite pathsinv0inv0 in tmp. cbn. cbn in tmp. rewrite <- tmp. clear tmp.
      rewrite transport_compose. rewrite <- assoc. apply cancel_precomposition.
      rewrite <- transport_source_precompose. rewrite <- transport_target_postcompose.
      rewrite transport_source_target_comm.
      rewrite <- maponpathsinv0. rewrite pathsinv0inv0.
      unfold DS11. unfold DS6, DS5, DS2, DS1.
      induction (hzrminusplus i 1). cbn. unfold idfun.
      fold DS11 DS6 DS5 DS2 DS1.
      rewrite transport_source_precompose. apply cancel_postcomposition.
      rewrite pathscomp0rid. unfold DS11, DS5. induction (hzrplusminus (i - 1 + 1) 1).
      cbn. unfold idfun. fold DS5. rewrite pathscomp0rid.
      set (tmp := @transport_hz_double_section_source_target
                    A (λ i0 : pr1 hz, C2 i0)
                    (λ i0 : pr1 hz, to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))
                    (λ i0 : pr1 hz, to_In2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                    _ _ (hzrminusplus (i - 1 + 1 + 1 - 1) 1)).
      cbn in tmp. unfold DS5. use (pathscomp0 tmp). clear tmp.
      rewrite transport_source_target_comm. apply idpath.
    - rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
      rewrite <- transport_source_to_inv. rewrite <- transport_target_to_inv.
      use (pathscomp0
             (! (@to_rinvax'
                   A (Additive.to_Zero A) _ _
                   (transportf (precategory_morphisms (C1 i))
                               (@maponpaths hz A
                                            (λ i0 : pr1 hz,
                                                    to_BinDirectSums
                                                      A (to_BinDirectSums
                                                           A (C1 (i0 + 1 - 1 + 1))
                                                           (C2 (i0 + 1 - 1))) (C1 i0))
                                            _ _ (hzrplusminus i 1))
                               (Diff C1 i
                                     · (transportf (λ x' : A, A ⟦ x', DS9 ⟧)
                                                    (maponpaths
                                                       C1 ((hzrminusplus (i + 1 - 1 + 1) 1)
                                                             @ hzrminusplus (i + 1) 1))
                                                    (to_In1 A DS9) · to_In1 A DS10)))))).
      use to_binop_eq.
      + apply idpath.
      + exact (InvRotMorphismIso'_eq2_1 f i).
  Qed.

  Lemma InvRotMorphismIso'_eq2' {C1 C2 : Complex A} (f : Morphism C1 C2) :
    MorphismOp
      A (MorphismComp (InvRotMorphism f) (InvRotMorphismInv f))
      (MorphismOp_inv
         A
         (IdMor
            (MappingCone
               A
               (MorphismComp
                  (MorphismOp_inv
                     A
                     (InvTranslationMorphism
                        A (MappingCone A f) (TranslationComplex A C1) (MappingConePr1 A f)))
                  (TranslationEquivUnitInv A C1))))) =
    ComplexHomotMorphism A (InvRotMorphismIsoHomot f).
  Proof.
    use MorphismEq. intros i. cbn.
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex, InvTranslationComplex. unfold InvRotMorphismIsoHomot.
    unfold DiffTranslationComplex. unfold InvRotMorphismMor, InvRotMorphismMorInv. cbn.
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS2 := to_BinDirectSums A DS1 (C1 i)).
    set (DS3 := to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 - 1))).
    set (DS4 := to_BinDirectSums A DS3 (C1 (i - 1))).
    set (DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 + 1 - 1))).
    set (DS6 := to_BinDirectSums A DS5 (C1 (i - 1 + 1))).
    set (DS7 := to_BinDirectSums A (C1 (i + 1 + 1 - 1 + 1)) (C2 (i + 1 + 1 - 1))).
    set (DS8 := to_BinDirectSums A DS7 (C1 (i + 1))).
    set (DS9 := to_BinDirectSums A (C1 (i + 1 - 1 + 1 - 1 + 1)) (C2 (i + 1 - 1 + 1 - 1))).
    set (DS10 := to_BinDirectSums A DS9 (C1 (i + 1 - 1))).
    set (DS11 := to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1 + 1)) (C2 (i - 1 + 1 - 1 + 1))).
    set (DS12 := to_BinDirectSums A (C1 (i + 1 - 1 + 1 + 1)) (C2 (i + 1 - 1 + 1))).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_Unel1' DS4). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite <- (assoc _ _ (to_inv (to_Pr1 A DS3))). rewrite <- transport_source_precompose.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- transport_source_to_inv. rewrite (to_IdIn1 A DS3). rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- (assoc (to_Pr2 A DS2)).
    rewrite <- (assoc (to_Pr2 A DS2)). rewrite <- (assoc (to_Pr2 A DS2)).
    rewrite <- (assoc (to_Pr2 A DS2)). rewrite <- (assoc (to_Pr2 A DS2)).
    rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
    rewrite <- transport_source_precompose. rewrite id_left.
    rewrite <- PreAdditive_invlcomp. rewrite <- (assoc (to_Pr2 A DS2)).
    rewrite <- transport_source_precompose.
    rewrite <- (assoc _ (to_In1 A DS8)). rewrite (to_Unel1' DS8).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite <- transport_target_postcompose.
    rewrite <- transport_target_postcompose. rewrite <- transport_target_postcompose.
    rewrite id_right. rewrite <- (assoc _ (to_In2 A DS8)). rewrite <- (assoc _ (to_In2 A DS8)).
    rewrite (to_IdIn2 A DS8). rewrite id_right. rewrite id_right.
    rewrite <- transport_target_to_binop. rewrite <- transport_target_to_binop.
    rewrite transport_target_postcompose. rewrite transport_target_postcompose.
    rewrite transport_target_postcompose. rewrite transport_target_postcompose.
    rewrite transport_target_postcompose.
    rewrite <- transport_target_to_inv. rewrite <- transport_target_to_inv.
    rewrite <- transport_target_to_inv. rewrite <- transport_target_to_inv.
    rewrite transport_target_postcompose. rewrite transport_target_postcompose.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- transport_source_to_inv.
    rewrite <- transport_target_to_inv. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq.
    rewrite <- (transport_target_postcompose (to_In1 A DS3)).
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite (assoc (to_In1 A DS3)). rewrite (assoc (to_In1 A DS3)).
    rewrite (assoc (to_In1 A DS3)). rewrite (assoc (to_In1 A DS3)).
    rewrite (assoc (to_In1 A DS3)). rewrite (assoc (to_In1 A DS3)).
    rewrite (to_Unel1' DS3). rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite (to_IdIn1 A DS3). rewrite id_left. rewrite id_left.
    unfold DiffTranslationComplex.
    rewrite <- (to_BinOpId A DS2).
    rewrite to_binop_inv_comm_2. rewrite to_binop_inv_comm_2.
    rewrite to_binop_inv_comm_1. rewrite to_binop_inv_comm_1.
    rewrite inv_inv_eq. rewrite to_binop_inv_comm_2.
    apply maponpaths. rewrite <- to_binop_inv_inv. rewrite to_assoc.
    assert (e : (to_binop DS2 DS2
                          (to_inv
                             (to_Pr1 A DS2 · transportf (precategory_morphisms DS1)
                                     (maponpaths C2 (hzrplusminus i 1))
                                     (to_Pr2 A DS1) · transportf (λ x' : A, A ⟦ x', DS1 ⟧)
                                     (maponpaths C2 (hzrplusminus i 1))
                                     (to_In2 A DS1) · to_In1 A DS2))
                          (to_binop DS2 DS2 (to_Pr1 A DS2 · to_In1 A DS2)
                                    (to_Pr2 A DS2 · to_In2 A DS2))) =
                to_binop DS2 DS2
                         (to_Pr1 A DS2 · to_Pr1 A DS1 · to_In1 A DS1 · to_In1 A DS2)
                         (to_Pr2 A DS2 · to_In2 A DS2)).
    {
      rewrite <- to_assoc.
      use to_binop_eq.
      - assert (e1 : to_Pr1 A DS2 · to_In1 A DS2 =
                     to_binop DS2 DS2
                              (to_Pr1 A DS2 · to_Pr1 A DS1 · to_In1 A DS1 · to_In1 A DS2)
                              (to_Pr1 A DS2 · to_Pr2 A DS1 · to_In2 A DS1 · to_In1 A DS2)).
        {
          rewrite <- to_postmor_linear'. rewrite <- assoc. rewrite <- assoc.
          rewrite <- to_premor_linear'. apply cancel_postcomposition.
          rewrite (to_BinOpId A DS1). rewrite id_right. apply idpath.
        }
        rewrite e1. clear e1.
        set (tmp := @to_lunax'' A (Additive.to_Zero A)  _ _
                                (to_Pr1 A DS2 · to_Pr1 A DS1 · to_In1 A DS1 · to_In1 A DS2)).
        use (pathscomp0 _ tmp). clear tmp.
        rewrite (to_commax' A (to_Pr1 A DS2 · to_Pr1 A DS1 · to_In1 A DS1 · to_In1 A DS2)).
        rewrite <- to_assoc.
        use to_binop_eq.
        + set (tmp := @to_linvax' A (Additive.to_Zero A) _ _
                                  (to_Pr1 A DS2 · to_Pr2 A DS1 · to_In2 A DS1 · to_In1 A DS2)).
          use (pathscomp0 _ tmp). clear tmp.
          use to_binop_eq.
          * apply maponpaths. apply cancel_postcomposition.
            rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
            rewrite transport_compose'. apply idpath.
          * apply idpath.
        + apply idpath.
      - apply idpath.
    }
    cbn in e. rewrite e. clear e.
    rewrite (to_commax'
               A _ (to_Pr2 A DS2 · transportf (precategory_morphisms (C1 i))
                           (@maponpaths
                              hz A
                              (λ i0 : pr1 hz,
                                      to_BinDirectSums
                                        A (to_BinDirectSums
                                             A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1)))
                                        (C1 i0)) _ _ (hzrminusplus i 1))
                           (transportf
                              (λ x' : A, A ⟦ x', DS6 ⟧)
                              (maponpaths C1 (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))
                              (transportf (precategory_morphisms (C1 (i - 1 + 1 - 1 + 1)))
                                          (maponpaths C1 (hzrminusplus (i - 1 + 1) 1))
                                          (identity (C1 (i - 1 + 1 - 1 + 1))) · to_In2 A DS6)))).
    rewrite (to_commax' A _ (to_Pr2 A DS2 · to_In2 A DS2)). rewrite <- to_assoc.
    rewrite (to_commax' A _ (to_Pr2 A DS2 · to_In2 A DS2)). rewrite to_assoc.
    rewrite to_assoc.
    use to_binop_eq.
    - apply cancel_precomposition. rewrite transport_source_precompose.
      unfold DS2, DS6. rewrite transport_source_target_comm. unfold DS1, DS5.
      induction (hzrminusplus i 1). cbn. unfold idfun. rewrite pathscomp0rid.
      induction (hzrminusplus (i - 1 + 1) 1). cbn. unfold idfun.
      rewrite id_left. apply idpath.
    - fold DS1 DS2. fold DS5 DS6. rewrite <- to_binop_inv_comm_2.
      rewrite to_commax'. rewrite <- to_assoc.
      rewrite (to_commax'
                 A _ (to_Pr1 A DS2 · transportf (precategory_morphisms DS1)
                             (maponpaths C1 (hzrminusplus (i + 1) 1))
                             (to_Pr1 A DS1) · transportf (λ x' : A, A ⟦ x', DS9 ⟧)
                             (maponpaths
                                C1 (hzrminusplus (i + 1 - 1 + 1) 1 @ hzrminusplus (i + 1) 1))
                             (to_In1 A DS9) · transportf (precategory_morphisms DS9)
                             (@maponpaths
                                hz A
                                (λ i0 : pr1 hz,
                                        to_BinDirectSums
                                          A (to_BinDirectSums
                                               A (C1 (i0 + 1 - 1 + 1))
                                               (C2 (i0 + 1 - 1)))
                                          (C1 i0)) _ _ (hzrplusminus i 1))
                             (to_In1 A DS10))).
      rewrite to_assoc.
      use to_binop_eq.
      + rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
        apply cancel_precomposition. rewrite transport_compose.
        apply cancel_precomposition. rewrite transport_source_precompose.
        rewrite transport_f_f. rewrite <- maponpathsinv0. rewrite <- maponpathscomp0.
        rewrite <- path_assoc. rewrite pathsinv0r. rewrite pathscomp0rid.
        rewrite <- transport_source_precompose.
        rewrite <- transport_target_postcompose.
        rewrite transport_source_target_comm.
        set (e := hzrplusminus (i + 1 - 1) 1).
        set (tmp := @transport_hz_double_section_source_target
                      A (λ i0 : hz, C1 (i0 + 1 - 1 + 1))
                      (λ i0 : hz, to_BinDirectSums
                                     A (to_BinDirectSums
                                          A (C1 (i0 + 1 - 1 + 1)) (C2 (i0 + 1 - 1))) (C1 i0))
                      (λ i0 : hz, (to_In1 A (to_BinDirectSums
                                                A (C1 (i0 + 1 - 1  + 1)) (C2 (i0 + 1 - 1))))
                                     · (to_In1 A (to_BinDirectSums
                                                     A (to_BinDirectSums
                                                          A (C1 (i0 + 1 - 1 + 1))
                                                          (C2 (i0 + 1 - 1))) (C1 i0))))
                      _ _ (hzrplusminus i 1)).
        cbn in tmp. unfold DS2, DS1.
        use (pathscomp0 tmp). clear tmp.
        unfold DS10, DS9. apply maponpaths.
        assert (e' : (maponpaths (λ i0 : pr1 hz, C1 (i0 + 1 - 1 + 1)) (hzrplusminus i 1)) =
                     (maponpaths C1 (hzrminusplus (i + 1 - 1 + 1) 1))).
        {
          cbn.
          assert (e'' : maponpaths (λ i0 : pr1 hz, C1 (i0 + 1 - 1 + 1)) (hzrplusminus i 1) =
                        maponpaths C1 (maponpaths (λ i0 : pr1 hz, i0 + 1 - 1 + 1)
                                                  (hzrplusminus i 1))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e''. apply maponpaths. apply isasethz.
        }
        rewrite e'. apply idpath.
      + exact (InvRotMorphismIso'_eq2_2 f i).
  Qed.

  Lemma InvRotMorphism_is_iso_with_inv_eq2 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    # (ComplexHomotFunctor A) (((InvRotMorphism f) : (ComplexPreCat_Additive A)⟦_, _⟧)
                                 · InvRotMorphismInv f) =
    # (ComplexHomotFunctor A) (identity _).
  Proof.
    use ComplexHomotFunctor_rel_mor'.
    - exact (InvRotMorphismIsoHomot f).
    - exact (InvRotMorphismIso'_eq2' f).
  Qed.

  Lemma InvRotMorphism_is_z_isomorphism_inverses {C1 C2 : Complex A} (f : Morphism C1 C2) :
    is_inverse_in_precat (# (ComplexHomotFunctor A) (InvRotMorphismInv f))
                         (# (ComplexHomotFunctor A) (InvRotMorphism f)).
  Proof.
    use mk_is_inverse_in_precat.
    - cbn beta. rewrite <- functor_comp. rewrite <- functor_id.
      exact (InvRotMorphism_is_iso_with_inv_eq1 f).
    - cbn beta. rewrite <- functor_comp. rewrite <- functor_id.
      exact (InvRotMorphism_is_iso_with_inv_eq2 f).
  Qed.

  Definition InvRotMorphism_is_z_isomorphism {C1 C2 : Complex A} (f : Morphism C1 C2) :
    @is_z_isomorphism (ComplexHomot_Additive A) _ _
                      (# (ComplexHomotFunctor A)
                         (((InvRotMorphismInv f) : (ComplexPreCat_Additive A)⟦_, _⟧))).
  Proof.
    use mk_is_z_isomorphism.
    - exact (# (ComplexHomotFunctor A) (InvRotMorphism f)).
    - exact (InvRotMorphism_is_z_isomorphism_inverses f).
  Defined.

  Definition InvRotMorphismInvComm1Homot {C1 C2 : Complex A} (f : Morphism C1 C2)  :
    ComplexHomot A C1 (MappingCone
                         A ((to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f)))
                              · (z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1)))).
  Proof.
    intros i. cbn.
    use compose.
    - exact (to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1)) (C2 (i - 1 + 1 - 1))).
    - exact (transportf (λ x' : ob A, precategory_morphisms x' _)
                        (maponpaths C1 (hzrminusplus (i - 1 + 1) 1 @ hzrminusplus i 1))
                        (to_In1 A (to_BinDirectSums A (C1 (i - 1 + 1 - 1 + 1))
                                                    (C2 (i - 1 + 1 - 1))))).
    - exact (to_In1 A _).
  Defined.

  Definition InvRotMorphismInvComm1 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    # (ComplexHomotFunctor A) ((f : (ComplexPreCat_Additive A)⟦_, _⟧) · InvRotMorphismInv f) =
    # (ComplexHomotFunctor A)
      (MappingConeIn2 A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f))
                                · (z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1)))).
  Proof.
    use (post_comp_with_z_iso_inv_is_inj (InvRotMorphism_is_z_isomorphism f)).
    unfold is_z_isomorphism_mor. unfold InvRotMorphism_is_z_isomorphism.
    set (tmp := functor_comp (ComplexHomotFunctor A)
                             ((f : (ComplexPreCat_Additive A)⟦_, _⟧) · InvRotMorphismInv f)
                             (InvRotMorphism f)).
    use (pathscomp0 (! tmp)). clear tmp. rewrite <- assoc.
    set (tmp := functor_comp (ComplexHomotFunctor A)
                             ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                             (((InvRotMorphismInv f) : (ComplexPreCat_Additive A)⟦_, _⟧)
                                · (InvRotMorphism f))).
    use (pathscomp0 tmp). clear tmp.
    set (tmp := is_inverse_in_precat1 (InvRotMorphism_is_z_isomorphism f)).
    cbn beta in tmp. cbn beta.
    set (tmp' := functor_comp (ComplexHomotFunctor A)
                              (((InvRotMorphismInv f) : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (((InvRotMorphism f) : (ComplexPreCat_Additive A)⟦_, _⟧))).
    cbn beta in tmp'. rewrite tmp'. clear tmp'.
    apply (maponpaths (λ g : _, # (ComplexHomotFunctor A) f · g)) in tmp.
    use (pathscomp0 tmp). clear tmp. rewrite id_right.
    set (tmp := InvRotMorphismComm2 f). cbn beta in tmp.
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
    use (pathscomp0 (! tmp)). clear tmp. rewrite functor_comp. apply idpath.
  Qed.

  Local Opaque precategory_morphisms compose identity.
  Definition InvRotMorphismInvComm2 {C1 C2 : Complex A} (f : Morphism C1 C2) :
    ((MappingConeIn2 A f) : (ComplexPreCat_Additive A)⟦_, _⟧)
      · (TranslationEquivCounitInv A (MappingCone A f)) =
    ((InvRotMorphismInv f) : (ComplexPreCat_Additive A)⟦_, _⟧)
      · MappingConePr1 A (to_inv (# (InvTranslationFunctor A) (MappingConePr1 A f)) ·
                                  z_iso_inv_mor (AddEquivUnitIso (TranslationEquiv A) C1)).
  Proof.
    use (post_comp_with_z_iso_is_inj
           (AddEquivCounitIso (TranslationEquiv A) (MappingCone A f))).
    rewrite <- assoc.
    set (tmp := is_inverse_in_precat2 (AddEquivCounitIso (TranslationEquiv A) (MappingCone A f))).
    cbn in tmp. cbn. rewrite tmp. clear tmp.
    use (pathscomp0 (@id_right (ComplexPreCat_Additive A) _ _
                               ((MappingConeIn2 A f) : (ComplexPreCat_Additive A)⟦_, _⟧))).
    use MorphismEq. Local Transparent compose. intros i. cbn.
    unfold InvRotMorphismMorInv. cbn. rewrite <- transport_source_precompose.
    rewrite <- transport_source_precompose. rewrite <- assoc.
    rewrite (to_IdIn1 A (to_BinDirectSums
                           A (to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))) (C1 i))).
    rewrite id_right. induction (hzrplusminus i 1). cbn. unfold idfun. rewrite id_right.
    apply idpath.
  Qed.

End inv_rotation_mapping_cone.


(** Different fibers of the same morphism give isomorphic mapping cones *)
Section fiber_ext.

  Variable A : Additive.

  Definition FiberExtMor {C1 C2 : Complex A} (f g : Morphism C1 C2) (H : ComplexHomot A C1 C2)
             (i : hz) : A ⟦ (MappingCone A f) i, (MappingCone A g) i ⟧.
  Proof.
    cbn.
    use to_binop.
    - use compose.
      + exact (C1 (i + 1)).
      + exact (to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + exact (to_In1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
    - use to_binop.
      + use compose.
        * exact (C1 (i + 1)).
        * exact (to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
        * use compose.
          -- exact (C2 i).
          -- exact (transportf (precategory_morphisms (C1 (i + 1)))
                               (maponpaths C2 (hzrplusminus i 1)) (H (i + 1))).
          -- exact (to_In2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + use compose.
        * exact (C2 i).
        * exact (to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
        * exact (to_In2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
  Defined.

  Lemma FiberExtComm {C1 C2 : Complex A} (f g : Morphism C1 C2) (H : ComplexHomot A C1 C2)
             (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
                     ComplexHomotMorphism A H) (i : hz) :
    FiberExtMor f g H i · Diff (MappingCone A g) i =
    Diff (MappingCone A f) i · FiberExtMor f g H (i + 1).
  Proof.
    set (Comm' := MorphismEq' A _ _ Comm). cbn in Comm'. cbn.
    unfold FiberExtMor. unfold MappingConeDiff. cbn.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    unfold FiberExtMor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS4 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite <- (assoc _ _ (to_Pr2 A DS4)).
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite (to_IdIn2 A DS4).
    rewrite (to_Unel1' DS4). rewrite (to_Unel2' DS4). unfold DiffTranslationComplex.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite id_right. rewrite id_right. rewrite id_right.
    rewrite to_lunax''. rewrite to_runax''. rewrite to_runax''. rewrite to_lunax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS1)). rewrite <- (assoc _ _ (to_Pr2 A DS1)).
    rewrite <- (assoc _ _ (to_Pr2 A DS1)).
    rewrite <- (assoc _ _ (to_Pr1 A DS1)). rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite (to_IdIn1 A DS1). rewrite (to_IdIn2 A DS1).
    rewrite (to_Unel1' DS1). rewrite (to_Unel2' DS1).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite id_right. rewrite id_right. rewrite id_right.
    rewrite to_runax''. rewrite to_runax''. rewrite to_runax''. rewrite to_lunax''.
    apply maponpaths.
    rewrite <- to_postmor_linear'. rewrite <- to_postmor_linear'.
    rewrite <- to_postmor_linear'. rewrite <- to_postmor_linear'.
    rewrite <- to_postmor_linear'. apply cancel_postcomposition.
    rewrite <- to_assoc. rewrite to_postmor_linear'.
    rewrite to_commax'. rewrite (to_commax' _ _ (to_Pr2 A DS1 · Diff C2 i)).
    rewrite (to_commax' _ _ (to_Pr2 A DS1 · Diff C2 i)).
    rewrite to_assoc. apply maponpaths.
    rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'. rewrite <- to_premor_linear'.
    apply cancel_precomposition.
    apply (to_rcan A (to_inv (g (i + 1)))). rewrite to_assoc. rewrite to_assoc.
    rewrite (Comm' (i + 1)). rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_runax''.
    rewrite <- transport_target_postcompose. rewrite <- PreAdditive_invlcomp.
    rewrite <- transport_target_to_inv. rewrite to_commax'. rewrite to_assoc.
    rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_runax''.
    rewrite transport_compose. rewrite transport_target_postcompose.
    apply cancel_precomposition.
    set (tmp := transport_hz_section A C2 1 (Diff C2) _ _ (hzrplusminus i 1)).
    rewrite <- maponpathsinv0.
    use (pathscomp0 (! tmp)). clear tmp. use transportf_paths.
    apply maponpaths. apply isasethz.
  Qed.

  Definition FiberExt {C1 C2 : Complex A} (f g : Morphism C1 C2) (H : ComplexHomot A C1 C2)
    (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
                     ComplexHomotMorphism A H) :
    Morphism (MappingCone A f) (MappingCone A g).
  Proof.
    use mk_Morphism.
    - intros i. exact (FiberExtMor f g H i).
    - intros i. exact (FiberExtComm f g H Comm i).
  Defined.

  Definition InvHomot {C1 C2 : Complex A} (H : ComplexHomot A C1 C2) :
    ComplexHomot A C1 C2.
  Proof.
    intros i. exact (to_inv (H i)).
  Defined.

  Lemma InvHomotEq {C1 C2 : Complex A} (f g : Morphism C1 C2) (H : ComplexHomot A C1 C2)
    (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
            ComplexHomotMorphism A H) :
    to_binop _ _ ((g : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((f : (ComplexPreCat_Additive A)⟦_, _⟧))) =
    ComplexHomotMorphism A (InvHomot H).
  Proof.
    set (Comm' := MorphismEq' A _ _ Comm). cbn in Comm'.
    use MorphismEq. intros i. cbn. unfold InvHomot.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- transport_target_to_inv. rewrite <- transport_target_to_inv.
    rewrite to_binop_inv_inv. rewrite <- (Comm' i).
    rewrite <- to_binop_inv_comm_1. rewrite to_commax'. apply idpath.
  Qed.

  Lemma FiberExt_eq1 {C1 C2 : Complex A} (f g : Morphism C1 C2) (H : ComplexHomot A C1 C2)
    (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
            ComplexHomotMorphism A H) :
    (((FiberExt f g H Comm) : (ComplexPreCat_Additive A)⟦_, _⟧)
       · ((FiberExt g f (InvHomot H) (InvHomotEq f g H Comm)) :
             (ComplexPreCat_Additive A)⟦_, _⟧)) = (identity _).
  Proof.
    use MorphismEq. intros i. cbn. unfold FiberExtMor. unfold InvHomot. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS4 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite <- (to_BinOpId A DS1).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS1)). rewrite <- (assoc _ _ (to_Pr2 A DS1)).
    rewrite <- (assoc _ _ (to_Pr2 A DS1)). rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite <- (assoc _ _ (to_Pr1 A DS1)). rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite (to_IdIn1 A DS1). rewrite (to_IdIn2 A DS1).
    rewrite (to_Unel1' DS1). rewrite (to_Unel2' DS1). unfold DiffTranslationComplex.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite id_right. rewrite id_right. rewrite id_right.
    rewrite to_runax''. rewrite to_runax''. rewrite to_runax''. rewrite to_lunax''.
    apply maponpaths. rewrite <- transport_target_to_inv. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- to_assoc.
    rewrite (@to_linvax' A (Additive.to_Zero A)). rewrite to_lunax''. apply idpath.
  Qed.

  Lemma FiberExt_eq2 {C1 C2 : Complex A} (f g : Morphism C1 C2) (H : ComplexHomot A C1 C2)
    (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
            ComplexHomotMorphism A H) :
    (((FiberExt g f (InvHomot H) (InvHomotEq f g H Comm)) : (ComplexPreCat_Additive A)⟦_, _⟧)
       · ((FiberExt f g H Comm) : (ComplexPreCat_Additive A)⟦_, _⟧)) = (identity _).
  Proof.
    use MorphismEq. intros i. cbn. unfold FiberExtMor. unfold InvHomot. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS4 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite <- (to_BinOpId A DS1).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS1)). rewrite <- (assoc _ _ (to_Pr2 A DS1)).
    rewrite <- (assoc _ _ (to_Pr2 A DS1)). rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite <- (assoc _ _ (to_Pr1 A DS1)). rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite (to_IdIn1 A DS1). rewrite (to_IdIn2 A DS1).
    rewrite (to_Unel1' DS1). rewrite (to_Unel2' DS1). unfold DiffTranslationComplex.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite id_right. rewrite id_right. rewrite id_right.
    rewrite to_runax''. rewrite to_runax''. rewrite to_runax''. rewrite to_lunax''.
    apply maponpaths. rewrite <- transport_target_to_inv. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- to_assoc.
    rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_lunax''. apply idpath.
  Qed.

  Lemma FiberExt_inverses' {C1 C2 : Complex A} (f g : Morphism C1 C2)
             (H : ComplexHomot A C1 C2)
             (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
            ComplexHomotMorphism A H) :
    @is_inverse_in_precat (ComplexPreCat_Additive A) _ _ ((FiberExt f g H Comm))
                          ((FiberExt g f (InvHomot H) (InvHomotEq f g H Comm))).
  Proof.
    use mk_is_inverse_in_precat.
    - exact (FiberExt_eq1 f g H Comm).
    - exact (FiberExt_eq2 f g H Comm).
  Qed.

  Lemma FiberExt_inverses {C1 C2 : Complex A} (f g : Morphism C1 C2)
             (H : ComplexHomot A C1 C2)
             (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
            ComplexHomotMorphism A H) :
    is_inverse_in_precat (# (ComplexHomotFunctor A) (FiberExt f g H Comm))
                         (# (ComplexHomotFunctor A) (FiberExt g f (InvHomot H)
                                                              (InvHomotEq f g H Comm))).
  Proof.
    use mk_is_inverse_in_precat.
    - rewrite <- functor_id. rewrite <- functor_comp. apply maponpaths.
      exact (FiberExt_eq1 f g H Comm).
    - rewrite <- functor_id. rewrite <- functor_comp. apply maponpaths.
      exact (FiberExt_eq2 f g H Comm).
  Qed.

  Definition FiberExt_is_z_isomorphism {C1 C2 : Complex A} (f g : Morphism C1 C2)
             (H : ComplexHomot A C1 C2)
             (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                              (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
            ComplexHomotMorphism A H) :
    @is_z_isomorphism (ComplexHomot_Additive A) _ _
                      (# (ComplexHomotFunctor A)
                         (((FiberExt f g H Comm) : (ComplexPreCat_Additive A)⟦_, _⟧))).
  Proof.
    use mk_is_z_isomorphism.
    - exact (# (ComplexHomotFunctor A) ((FiberExt g f (InvHomot H) (InvHomotEq f g H Comm)) :
                                          (ComplexPreCat_Additive A)⟦_, _⟧)).
    - exact (FiberExt_inverses f g H Comm).
  Defined.

  Lemma FiberExt_Comm2 {C1 C2 : Complex A} (f g : Morphism C1 C2)
        (H : ComplexHomot A C1 C2)
        (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                         (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
                ComplexHomotMorphism A H) :
    ((MappingConeIn2 A f) : (ComplexPreCat_Additive A)⟦_, _⟧) · (FiberExt f g H Comm) =
    (MappingConeIn2 A g).
  Proof.
    use MorphismEq. intros i. cbn.
    unfold FiberExtMor.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn2 A DS1). rewrite (to_Unel2' DS1).
    rewrite id_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''. rewrite to_lunax''.
    apply idpath.
  Qed.

  Lemma FiberExt_Comm2H {C1 C2 : Complex A} (f g : Morphism C1 C2)
        (H : ComplexHomot A C1 C2)
        (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                         (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
                ComplexHomotMorphism A H) :
    (# (ComplexHomotFunctor A) (MappingConeIn2 A f))
      · (# (ComplexHomotFunctor A) (FiberExt f g H Comm)) =
    # (ComplexHomotFunctor A) (MappingConeIn2 A g).
  Proof.
    rewrite <- functor_comp. apply maponpaths. exact (FiberExt_Comm2 f g H Comm).
  Qed.

  Lemma FiberExt_Comm3 {C1 C2 : Complex A} (f g : Morphism C1 C2)
        (H : ComplexHomot A C1 C2)
        (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                         (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
                ComplexHomotMorphism A H) :
    ((MappingConePr1 A f) : (ComplexPreCat_Additive A)⟦_, _⟧) =
    ((FiberExt f g H Comm) : (ComplexPreCat_Additive A)⟦_, _⟧) · (MappingConePr1 A g).
  Proof.
    use MorphismEq. intros i. cbn.
    unfold FiberExtMor.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn1 A DS1). rewrite (to_Unel2' DS1).
    rewrite id_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right. rewrite to_lunax''. rewrite to_runax''.
    apply idpath.
  Qed.

  Lemma FiberExt_Comm3H {C1 C2 : Complex A} (f g : Morphism C1 C2)
        (H : ComplexHomot A C1 C2)
        (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧))
                         (to_inv ((g : (ComplexPreCat_Additive A)⟦_, _⟧))) =
                ComplexHomotMorphism A H) :
    # (ComplexHomotFunctor A) (MappingConePr1 A f) =
    # (ComplexHomotFunctor A) (FiberExt f g H Comm)
      · # (ComplexHomotFunctor A) (MappingConePr1 A g).
  Proof.
    rewrite <- functor_comp. apply maponpaths. exact (FiberExt_Comm3 f g H Comm).
  Qed.

End fiber_ext.


(** * Extension of morphisms *)
(** ** Introduction
Suppose you have morphisms f1 : X1 --> Y1, f2 : X2 --> Y2, g1 : X1 --> X2, and g2 : Y1 --> Y2, such
that f1 · g2 = f2 · g1 in K(A). We construct a morphism h : C(f1) --> C(f2) such that the
following squares are commutative in K(A)
                   Y1 --> C(f1)                   C(f1) --> X1[1]
                   |        |                       |         |
                   Y2 --> C(f2)                   C(f2) --> X2[1]
*)
Section mapping_cone_ext.

  Variable A : Additive.

  Definition MappingConeMorExtMor {C1 C1' C2 C2' : Complex A} (f : Morphism C1 C2)
             (f' : Morphism C1' C2') (g1 : Morphism C1 C1') (g2 : Morphism C2 C2')
             (H : ComplexHomot A C1 C2') (i : hz) :
    A ⟦ (MappingCone A f) i, (MappingCone A f') i ⟧.
  Proof.
    cbn.
    use to_binop.
    - use compose.
      + exact (C1 (i + 1)).
      + exact (to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
      + use compose.
        * exact (C1' (i + 1)).
        * exact (g1 (i + 1)).
        * exact (to_In1 A (to_BinDirectSums A (C1' (i + 1)) (C2' i))).
    - use to_binop.
      + use compose.
        * exact (C1 (i + 1)).
        * exact (to_Pr1 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
        * use compose.
          -- exact (C2' i).
          -- exact (transportf (precategory_morphisms (C1 (i + 1)))
                               (maponpaths C2' (hzrplusminus i 1)) (H (i + 1))).
          -- exact (to_In2 A (to_BinDirectSums A (C1' (i + 1)) (C2' i))).
      + use compose.
        * exact (C2 i).
        * exact (to_Pr2 A (to_BinDirectSums A (C1 (i + 1)) (C2 i))).
        * use compose.
          -- exact (C2' i).
          -- exact (g2 i).
          -- exact (to_In2 A (to_BinDirectSums A (C1' (i + 1)) (C2' i))).
  Defined.

  Lemma MappingConeMorExtComm {C1 C1' C2 C2' : Complex A}
        (f : Morphism C1 C2) (f' : Morphism C1' C2')
        (g1 : Morphism C1 C1') (g2 : Morphism C2 C2')
        (H : ComplexHomot A C1 C2')
        (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧) · g2)
                         (to_inv ((g1 : (ComplexPreCat_Additive A)⟦_, _⟧) · f')) =
                ComplexHomotMorphism A H) (i : hz) :
    MappingConeMorExtMor f f' g1 g2 H i · MappingConeDiff A f' i =
    MappingConeDiff A f i · MappingConeMorExtMor f f' g1 g2 H (i + 1).
  Proof.
    set (Comm' := MorphismEq' A _ _ Comm). cbn in Comm'.
    unfold MappingConeMorExtMor. unfold MappingConeDiff. cbn.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3. cbn.
    unfold MappingConeMorExtMor. cbn.
    set (DS1 := to_BinDirectSums A (C1' (i + 1)) (C2' i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS3 := to_BinDirectSums A (C1' (i + 1 + 1)) (C2' (i + 1))).
    set (DS4 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite <- (assoc _ _ (to_Pr2 A DS4)).
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite (to_IdIn2 A DS4).
    rewrite (to_Unel1' DS4). rewrite (to_Unel2' DS4). unfold DiffTranslationComplex.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite id_right. rewrite id_right. rewrite id_right.
    rewrite to_lunax''. rewrite to_runax''. rewrite to_runax''.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS1)). rewrite <- (assoc _ _ (to_Pr2 A DS1)).
    rewrite <- (assoc _ _ (to_Pr2 A DS1)).
    rewrite <- (assoc _ _ (to_Pr1 A DS1)). rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite (to_IdIn1 A DS1). rewrite (to_IdIn2 A DS1).
    rewrite (to_Unel1' DS1). rewrite (to_Unel2' DS1).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite id_right. rewrite id_right. rewrite id_right.
    rewrite to_runax''. rewrite to_runax''. rewrite to_runax''. rewrite to_lunax''.
    use to_binop_eq.
    - apply cancel_postcomposition. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. rewrite <- PreAdditive_invlcomp.
      rewrite <- PreAdditive_invrcomp. apply maponpaths.
      exact (MComm g1 (i + 1)).
    - rewrite <- to_assoc. rewrite <- to_assoc.
      use to_binop_eq.
      + rewrite <- to_postmor_linear'. rewrite <- to_postmor_linear'. apply cancel_postcomposition.
        rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
        rewrite <- to_premor_linear'. rewrite <- to_premor_linear'. apply cancel_precomposition.
        rewrite <- PreAdditive_invlcomp. rewrite <- transport_target_postcompose.
        assert (e : (transportf (precategory_morphisms (C1 (i + 1)))
                                (maponpaths C2' (hzrplusminus i 1)) (H (i + 1)) ·
                                Diff C2' i) =
                    (transportf (precategory_morphisms (C1 (i + 1)))
                                (maponpaths C2' (hzrminusplus (i + 1) 1))
                                (H (i + 1) · Diff C2' (i + 1 - 1)))).
        {
          rewrite transport_target_postcompose.
          rewrite transport_compose. apply cancel_precomposition.
          apply pathsinv0. rewrite <- maponpathsinv0.
          use (pathscomp0 _ (transport_hz_section A C2' 1 (Diff C2') _ _ (hzrplusminus i 1))).
          use transportf_paths. apply maponpaths. apply isasethz.
        }
        cbn in e. rewrite e. clear e.
        use (to_lcan A (transportf (precategory_morphisms (C1 (i + 1)))
                                   (maponpaths C2' (hzrplusminus (i + 1) 1))
                                   (Diff C1 (i + 1) · H (i + 1 + 1)))).
        rewrite <- to_assoc. rewrite <- to_assoc. rewrite (@to_rinvax' A (Additive.to_Zero A)).
        rewrite to_lunax''. rewrite to_commax'. rewrite <- to_assoc.
        use (to_rcan A (to_inv (g1 (i + 1) · f' (i + 1)))). rewrite to_assoc.
        rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_runax''.
        apply pathsinv0. exact (Comm' (i + 1)).
      + apply cancel_postcomposition. rewrite <- assoc. rewrite <- assoc.
        apply cancel_precomposition. exact (MComm g2 i).
  Qed.

  Definition MappingConeMorExt {C1 C1' C2 C2' : Complex A}
             (f : Morphism C1 C2) (f' : Morphism C1' C2')
             (g1 : Morphism C1 C1') (g2 : Morphism C2 C2') (H : ComplexHomot A C1 C2')
             (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧) · g2)
                              (to_inv ((g1 : (ComplexPreCat_Additive A)⟦_, _⟧) · f')) =
                     ComplexHomotMorphism A H) :
    Morphism (MappingCone A f) (MappingCone A f').
  Proof.
    use mk_Morphism.
    - intros i. exact (MappingConeMorExtMor f f' g1 g2 H i).
    - intros i. exact (MappingConeMorExtComm f f' g1 g2 H Comm i).
  Defined.

  Lemma MappingConeMorExtComm1 {C1 C1' C2 C2' : Complex A}
        (f : Morphism C1 C2) (f' : Morphism C1' C2')
        (g1 : Morphism C1 C1') (g2 : Morphism C2 C2') (H : ComplexHomot A C1 C2')
        (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧) · g2)
                         (to_inv ((g1 : (ComplexPreCat_Additive A)⟦_, _⟧) · f')) =
                ComplexHomotMorphism A H) :
    (MappingConeIn2 A f : (ComplexPreCat_Additive A)⟦_, _⟧)
      · (MappingConeMorExt f f' g1 g2 H Comm) =
    (g2 : (ComplexPreCat_Additive A)⟦_, _⟧)
      · (MappingConeIn2 A f' : (ComplexPreCat_Additive A)⟦_, _⟧).
  Proof.
    use MorphismEq. intros i. cbn. unfold MappingConeMorExtMor. cbn.
    set (DS1 := to_BinDirectSums A (C1' (i + 1)) (C2' i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn2 A DS2). rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite id_left. rewrite to_lunax''. rewrite to_lunax''. apply idpath.
  Qed.

  Lemma MappingConeMorExtComm2 {C1 C1' C2 C2' : Complex A}
        (f : Morphism C1 C2) (f' : Morphism C1' C2')
        (g1 : Morphism C1 C1') (g2 : Morphism C2 C2') (H : ComplexHomot A C1 C2')
        (Comm : to_binop _ _ ((f : (ComplexPreCat_Additive A)⟦_, _⟧) · g2)
                         (to_inv ((g1 : (ComplexPreCat_Additive A)⟦_, _⟧) · f')) =
                ComplexHomotMorphism A H) :
    ((MappingConePr1 A f) : (ComplexPreCat_Additive A)⟦_, _⟧) · (# (TranslationFunctor A) g1) =
    ((MappingConeMorExt f f' g1 g2 H Comm) : (ComplexPreCat_Additive A)⟦_, _⟧)
      · (MappingConePr1 A f').
  Proof.
    use MorphismEq. intros i. cbn. unfold MappingConeMorExtMor. cbn.
    set (DS1 := to_BinDirectSums A (C1' (i + 1)) (C2' i)).
    set (DS2 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS1)). rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite <- (assoc _ _ (to_Pr1 A DS1)).
    rewrite (to_IdIn1 A DS1). rewrite (to_Unel2' DS1). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right.
    rewrite id_right. rewrite to_lunax''. rewrite to_runax''.
    apply idpath.
  Qed.

End mapping_cone_ext.


(** * Octahedral axiom for K(A) *)
Section mapping_cone_octa.

  Context {A : Additive}.

  Local Lemma KAOctaMor1_comm {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) (i : hz) :
    to_binop (to_BinDirectSums A (x (i + 1)) (y i)) (to_BinDirectSums A (x (i + 1)) (z i))
             (to_Pr1 A (to_BinDirectSums A (x (i + 1)) (y i))
                     · to_In1 A (to_BinDirectSums A (x (i + 1)) (z i)))
             (to_Pr2 A (to_BinDirectSums A (x (i + 1)) (y i)) · f2 i · to_In2 A
                     (to_BinDirectSums A (x (i + 1)) (z i))) ·
             MappingConeDiff A (MorphismComp f1 f2) i =
    (MappingConeDiff A f1 i)
      · to_binop (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1)))
      (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1)))
      (to_Pr1 A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))) ·
              to_In1 A (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))))
      (to_Pr2 A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))) ·
              f2 (i + 1) · to_In2 A (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1)))).
  Proof.
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn. cbn in x, y, z.
    set (DS1 := to_BinDirectSums A (x (i + 1)) (y i)).
    set (DS2 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS3 := to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))).
    set (DS4 := to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc.
    (* DS2 *)
    rewrite <- (assoc _ (to_In1 A DS2)). rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite (to_IdIn1 A DS2). rewrite (to_Unel1' DS2). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite id_right.
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite (to_IdIn2 A DS2). rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite id_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''.
    (* DS4 *)
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite (to_Unel1' DS4). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite id_right.
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_IdIn2 A DS4). rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite id_right.
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_IdIn2 A DS4). rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''. rewrite id_right.
    (* binop_eq *)
    rewrite to_assoc.
    use to_binop_eq.
    + apply idpath.
    + use to_binop_eq.
      * apply idpath.
      * apply cancel_postcomposition.
        rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
        exact (MComm f2 i).
  Qed.

  (** The following morphism is used in the octahedral axiom for K(A) *)
  Definition KAOctaMor1 {x y z : ob (ComplexPreCat_Additive A)} (f1 : x --> y) (f2 : y --> z) :
    Morphism (MappingCone A f1) (MappingCone A (f1 · f2)).
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      use to_binop.
      + exact (to_Pr1 A _ · to_In1 A _).
      + exact (to_Pr2 A _ · ((f2 : Morphism _ _) i) · to_In2 A _).
    - intros i. exact (KAOctaMor1_comm f1 f2 i).
  Defined.

  Local Lemma KAOctaMor2_comm {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) (i : hz) :
    to_binop (to_BinDirectSums A (x (i + 1)) (z i)) (to_BinDirectSums A (y (i + 1)) (z i))
             (to_Pr1 A (to_BinDirectSums A (x (i + 1)) (z i)) · f1 (i + 1) · to_In1 A
                     (to_BinDirectSums A (y (i + 1)) (z i)))
             (to_Pr2 A (to_BinDirectSums A (x (i + 1)) (z i))
                     · to_In2 A (to_BinDirectSums A (y (i + 1)) (z i)))
             · MappingConeDiff A f2 i =
    (MappingConeDiff A (MorphismComp f1 f2) i)
      · (to_binop (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1)))
                   (to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1)))
                   (to_Pr1 A (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))) ·
                           f1 (i + 1 + 1) · to_In1 A
                           (to_BinDirectSums A
                                             (y (i + 1 + 1))
                                             (z (i + 1))))
                   (to_Pr2 A (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))) ·
                           to_In2 A (to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1))))).
  Proof.
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn. cbn in x, y, z.
    set (DS1 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (y (i + 1)) (z i)).
    set (DS3 := to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1))).
    set (DS4 := to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    (* DS2 *)
    rewrite <- (assoc _ (to_In1 A DS2)). rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite (to_IdIn1 A DS2). rewrite (to_Unel1' DS2). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite id_right.
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite (to_IdIn2 A DS2). rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite id_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    (* DS4 *)
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite (to_Unel1' DS4). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite id_right.
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_IdIn2 A DS4). rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite id_right.
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_IdIn2 A DS4). rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite id_right.
    (* to_binop_eq *)
    rewrite to_assoc. use to_binop_eq.
    - apply cancel_postcomposition. rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition. rewrite <- PreAdditive_invlcomp.
      rewrite <- PreAdditive_invrcomp. apply maponpaths.
      exact (MComm f1 (i + 1)).
    - apply idpath.
  Qed.

  Definition KAOctaMor2 {x y z : ob (ComplexPreCat_Additive A)} (f1 : x --> y) (f2 : y --> z) :
    Morphism (MappingCone A (f1 · f2)) (MappingCone A f2).
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      use to_binop.
      + exact (to_Pr1 A _ · ((f1 : Morphism _ _) (i + 1)) · to_In1 A _).
      + exact (to_Pr2 A _ · to_In2 A _).
    - intros i. exact (KAOctaMor2_comm f1 f2 i).
  Defined.

  Local Lemma KAOctaMor3_comm {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) (i : hz) :
    to_binop (to_BinDirectSums A (y (i + 1)) (z i))
             (to_BinDirectSums A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1)))
                               (to_BinDirectSums A (x (i + 1)) (z i)))
             (to_Pr1 A (to_BinDirectSums A (y (i + 1)) (z i))
                     · to_In2 A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1)))
                     · to_In1 A (to_BinDirectSums
                                    A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1)))
                                    (to_BinDirectSums A (x (i + 1)) (z i))))
             (to_Pr2 A (to_BinDirectSums A (y (i + 1)) (z i))
                     · to_In2 A (to_BinDirectSums A (x (i + 1)) (z i))
                     · to_In2 A (to_BinDirectSums
                                    A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1)))
                                    (to_BinDirectSums A (x (i + 1)) (z i))))
             · MappingConeDiff A (KAOctaMor1 f1 f2) i =
    (MappingConeDiff A f2 i)
      · to_binop (to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1)))
      (to_BinDirectSums A (to_BinDirectSums A (x (i + 1 + 1 + 1)) (y (i + 1 + 1)))
                        (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))))
      (to_Pr1 A (to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1))) ·
              to_In2 A (to_BinDirectSums A (x (i + 1 + 1 + 1)) (y (i + 1 + 1))) ·
              to_In1 A
              (to_BinDirectSums A (to_BinDirectSums A (x (i + 1 + 1 + 1)) (y (i + 1 + 1)))
                                (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1)))))
      (to_Pr2 A (to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1))) ·
              to_In2 A (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))) ·
              to_In2 A
              (to_BinDirectSums A (to_BinDirectSums A (x (i + 1 + 1 + 1)) (y (i + 1 + 1)))
                                (to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))))).
  Proof.
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn. cbn in x, y, z.
    set (DS1 := to_BinDirectSums A (y (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))).
    set (DS3 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS4 := to_BinDirectSums A DS2 DS3).
    set (DS5 := to_BinDirectSums A (x (i + 1 + 1 + 1)) (y (i + 1 + 1))).
    set (DS6 := to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))).
    set (DS7 := to_BinDirectSums A DS5 DS6).
    set (DS8 := to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1))).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    (* DS4 *)
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite (to_Unel1' DS4). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    (* DS2 *)
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite (to_IdIn2 A DS2). rewrite id_right.
    rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    (* DS4 *)
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_IdIn2 A DS4). rewrite id_right.
    rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''. rewrite to_lunax''.
    (* DS8 *)
    rewrite <- (assoc _ (to_In2 A DS8)). rewrite <- (assoc _ (to_In2 A DS8)).
    rewrite <- (assoc _ (to_In2 A DS8)). rewrite <- (assoc _ (to_In2 A DS8)).
    rewrite (to_IdIn2 A DS8). rewrite id_right. rewrite id_right.
    rewrite (to_Unel2' DS8). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite <- (assoc _ (to_In1 A DS8)). rewrite <- (assoc _ (to_In1 A DS8)).
    rewrite (to_IdIn1 A DS8). rewrite id_right.
    rewrite (to_Unel1' DS8). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    (* remove one sum *)
    rewrite (to_commax' _ _ (to_Pr1 A DS1 · f2 (i + 1) · to_In2 A DS6 · to_In2 A DS7)).
    rewrite to_assoc.
    rewrite <- (to_assoc _ _ (to_Pr1 A DS1 · f2 (i + 1) · to_In2 A DS6 · to_In2 A DS7)).
    rewrite (to_commax' _ _ (to_Pr1 A DS1 · f2 (i + 1) · to_In2 A DS6 · to_In2 A DS7)).
    rewrite to_assoc.
    use to_binop_eq.
    - apply idpath.
    - unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
      unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
      fold DS1 DS2 DS3 DS4 DS5 DS6 DS7 DS8.
      rewrite to_premor_linear'. rewrite to_premor_linear'.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      (* DS3 *)
      rewrite <- (assoc _ (to_In2 A DS3)). rewrite <- (assoc _ (to_In2 A DS3)).
      rewrite (to_IdIn2 A DS3). rewrite id_right.
      rewrite (to_Unel2' DS3). rewrite ZeroArrow_comp_right.
      rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
      rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
      rewrite to_lunax''. rewrite to_lunax''.
      use to_binop_eq.
      + apply cancel_postcomposition. rewrite <- assoc. rewrite <- assoc.
        rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
        apply cancel_precomposition. rewrite <- PreAdditive_invrcomp.
        rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
        rewrite <- PreAdditive_invrcomp. rewrite to_binop_inv_comm_1.
        rewrite <- PreAdditive_invrcomp. rewrite inv_inv_eq.
        rewrite <- to_binop_inv_inv. rewrite to_premor_linear'.
        rewrite to_premor_linear'. rewrite <- PreAdditive_invrcomp.
        rewrite <- PreAdditive_invrcomp. rewrite assoc. rewrite assoc. rewrite assoc.
        rewrite assoc. rewrite assoc. rewrite assoc.
        rewrite (to_IdIn2 A DS2). rewrite id_left.
        rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_left.
        rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
        rewrite to_lunax''. rewrite to_binop_inv_inv.  rewrite to_lunax''.
        apply idpath.
      + apply idpath.
  Qed.

  Definition KAOctaMor3 {x y z : ob (ComplexPreCat_Additive A)} (f1 : x --> y) (f2 : y --> z) :
    Morphism (MappingCone A f2) (MappingCone A (KAOctaMor1 f1 f2)).
  Proof.
    use mk_Morphism.
    - intros i. cbn.
      use to_binop.
      + exact (to_Pr1 A _ · to_In2 A _ · to_In1 A _).
      + exact (to_Pr2 A _ · to_In2 A _ · to_In2 A _).
    - intros i. exact (KAOctaMor3_comm f1 f2 i).
  Defined.

  Definition KAOctaMor3InvMor {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    ∏ i : hz, A ⟦ (MappingCone A (KAOctaMor1 f1 f2)) i, (MappingCone A f2) i ⟧.
  Proof.
    intros i. cbn.
    use to_binop.
    - exact (to_Pr1 A _ · to_Pr2 A _ · to_In1 A _).
    - use to_binop.
      + exact (to_Pr2 A _ · to_Pr1 A _ · f1 (i + 1) · to_In1 A _).
      + exact (to_Pr2 A _ · to_Pr2 A _ · to_In2 A _).
  Defined.

  Local Lemma KAOctaMor3InvComm {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z)
        (i : hz) :
    KAOctaMor3InvMor f1 f2 i · Diff (MappingCone A f2) i =
    Diff (MappingCone A (KAOctaMor1 f1 f2)) i · KAOctaMor3InvMor f1 f2 (i + 1).
  Proof.
    cbn. unfold KAOctaMor3InvMor, MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
    set (DS1 := to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))).
    set (DS2 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS3 := to_BinDirectSums A DS1 DS2).
    set (DS4 := to_BinDirectSums A (y (i + 1)) (z i)).
    set (DS5 := to_BinDirectSums A (y (i + 1 + 1)) (z (i + 1))).
    set (DS6 := to_BinDirectSums A (x (i + 1 + 1 + 1)) (y (i + 1 + 1))).
    set (DS7 := to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))).
    set (DS8 := to_BinDirectSums A DS6 DS7).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    (* DS4 *)
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite (to_Unel1' DS4). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite (to_IdIn2 A DS4). rewrite id_right.
    rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''.
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite (to_Unel1' DS4). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    (* DS8 *)
    rewrite <- (assoc _ (to_In2 A DS8)). rewrite <- (assoc _ (to_In2 A DS8)).
    rewrite <- (assoc _ (to_In2 A DS8)). rewrite <- (assoc _ (to_In1 A DS8)).
    rewrite <- (assoc _ (to_In1 A DS8)).
    rewrite (to_IdIn1 A DS8). rewrite (to_IdIn2 A DS8). rewrite id_right. rewrite id_right.
    rewrite (to_Unel2' DS8). rewrite (to_Unel1' DS8).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_lunax''. rewrite to_runax''.
    (* DS7 *)
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc _ (to_In1 A DS7)). rewrite <- (assoc _ (to_In2 A DS7)).
    rewrite <- (assoc _ (to_In1 A DS7)). rewrite <- (assoc _ (to_In2 A DS7)).
    rewrite (to_IdIn1 A DS7). rewrite (to_IdIn2 A DS7). rewrite id_right. rewrite id_right.
    rewrite (to_Unel1' DS7). rewrite (to_Unel2' DS7).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''.
    (* DS8 *)
    rewrite <- (assoc _ (to_In2 A DS8)). rewrite <- (assoc _ (to_In2 A DS8)).
    rewrite (to_IdIn2 A DS8). rewrite id_right.
    (* MappingConeDiff *)
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6 DS7 DS8.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. cbn.
    (* DS8 *)
    rewrite <- (assoc _ (to_In2 A DS8)). rewrite <- (assoc _ (to_In2 A DS8)).
    rewrite <- (assoc _ (to_In2 A DS8)). rewrite (to_Unel2' DS8).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_lunax''. rewrite to_lunax''.
    (* DS7 *)
    rewrite <- (assoc _ (to_In2 A DS7)). rewrite <- (assoc _ (to_In2 A DS7)).
    rewrite <- (assoc _ (to_In2 A DS7)). rewrite (to_IdIn2 A DS7). rewrite (to_Unel2' DS7).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_runax''. rewrite id_right.
    rewrite <- (assoc _ (to_In1 A DS7)). rewrite <- (assoc _ (to_In1 A DS7)).
    rewrite (to_IdIn1 A DS7). rewrite (to_Unel1' DS7).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite id_right.
    rewrite <- (assoc _ (to_In2 A DS7)). rewrite (to_IdIn2 A DS7). rewrite id_right.
    (* DS6 *)
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite to_premor_linear'. rewrite to_postmor_linear'. rewrite to_premor_linear'.
    rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In1 A DS6)). rewrite <- (assoc _ (to_In2 A DS6)).
    rewrite <- (assoc _ (to_In2 A DS6)). rewrite (to_IdIn2 A DS6). rewrite id_right.
    rewrite id_right. rewrite (to_Unel1' DS6).
    rewrite ZeroArrow_comp_right. rewrite to_lunax''.
    rewrite <- PreAdditive_invlcomp. rewrite to_postmor_linear'.
    rewrite <- to_binop_inv_inv.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    (* binop_eq *)
    rewrite (to_commax'
               _ _ (to_inv (to_Pr1 A DS3 · to_Pr2 A DS1 · Diff y (i + 1) · to_In1 A DS5))).
    rewrite to_assoc. rewrite to_assoc. rewrite to_assoc.
    apply maponpaths.
    rewrite to_assoc.
    rewrite <- (to_assoc
                 _ (to_inv (to_Pr1 A DS3 · to_Pr1 A DS1 · f1 (i + 1 + 1) · to_In1 A DS5))).
    rewrite (@to_linvax' A (Additive.to_Zero A)). rewrite to_lunax''.
    apply maponpaths.
    rewrite <- (assoc _ (f1 (i + 1))). rewrite (MComm f1 (i + 1)). rewrite assoc.
    apply idpath.
  Qed.

  Definition KAOctaMor3Inv {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    Morphism (MappingCone A (KAOctaMor1 f1 f2)) (MappingCone A f2).
  Proof.
    use mk_Morphism.
    - exact (KAOctaMor3InvMor f1 f2).
    - exact (KAOctaMor3InvComm f1 f2).
  Defined.

  Lemma KAOctaMor3Iso1 {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) (i : hz) :
    (MorphismComp (KAOctaMor3 f1 f2) (KAOctaMor3Inv f1 f2)) i = (IdMor (MappingCone A f2)) i.
  Proof.
    unfold KAOctaMor3, KAOctaMor3Inv, KAOctaMor3InvMor. cbn.
    set (DS1 := to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))).
    set (DS2 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS3 := to_BinDirectSums A DS1 DS2).
    set (DS4 := to_BinDirectSums A (y (i + 1)) (z i)).
    rewrite to_postmor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc.
    (* DS3 *)
    rewrite <- (assoc _ (to_In1 A DS3)). rewrite <- (assoc _ (to_In1 A DS3)).
    rewrite <- (assoc _ (to_In2 A DS3)). rewrite <- (assoc _ (to_In2 A DS3)).
    rewrite (to_IdIn1 A DS3). rewrite (to_IdIn2 A DS3). rewrite id_right. rewrite id_right.
    rewrite (to_Unel1' DS3). rewrite (to_Unel2' DS3).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_lunax''. rewrite to_runax''.
    (* DS2 *)
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite (to_IdIn2 A DS2). rewrite id_right. rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''.
    (* DS1 *)
    rewrite <- (assoc _ (to_In2 A DS1)). rewrite (to_IdIn2 A DS1). rewrite id_right.
    exact (to_BinOpId A DS4).
  Qed.

  Definition KAOctaMor3InvHomot {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    ComplexHomot A (MappingCone A (KAOctaMor1 f1 f2)) (MappingCone A (KAOctaMor1 f1 f2)).
  Proof.
    intros i. cbn.
    use compose.
    - exact (x (i + 1)).
    - exact (to_Pr2 A _ · to_Pr1 A _).
    - use compose.
      + exact (to_BinDirectSums A (x (i - 1 + 1 + 1)) (y (i - 1 + 1))).
      + exact (to_inv (transportf (λ x' : ob A, precategory_morphisms x' _)
                                  (maponpaths
                                     x (maponpaths (λ i0 : hz, (i0 + 1)) (hzrminusplus i 1)))
                                  (to_In1 A (to_BinDirectSums A (x (i - 1 + 1 + 1))
                                                              (y (i - 1 + 1)))))).
      + exact (to_In1 A _).
  Defined.

  Lemma KAOctaMor3Iso2 {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    (@to_binop (ComplexPreCat_Additive A)
               (MappingCone A (KAOctaMor1 f1 f2)) (MappingCone A (KAOctaMor1 f1 f2))
               (MorphismComp (KAOctaMor3Inv f1 f2) (KAOctaMor3 f1 f2))
               (to_inv ((IdMor (MappingCone A (KAOctaMor1 f1 f2)))
                        : (ComplexPreCat_Additive A)⟦_, _⟧))) =
    (ComplexHomotMorphism A (KAOctaMor3InvHomot f1 f2)).
  Proof.
    use MorphismEq. intros i.
    unfold KAOctaMor3, KAOctaMor3Inv, KAOctaMor3InvMor.
    unfold KAOctaMor3InvHomot, MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
    set (DS1 := to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))).
    set (DS2 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS3 := to_BinDirectSums A DS1 DS2).
    set (DS4 := to_BinDirectSums A (y (i + 1)) (z i)).
    set (DS5 := to_BinDirectSums A (x (i - 1 + 1 + 1)) (y (i - 1 + 1))).
    set (DS6 := to_BinDirectSums A (x (i - 1 + 1)) (z (i - 1))).
    set (DS7 := to_BinDirectSums A DS5 DS6).
    set (DS8 := to_BinDirectSums A (x (i + 1 + 1 + 1)) (y (i + 1 + 1))).
    set (DS9 := to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))).
    set (DS10 := to_BinDirectSums A DS8 DS9).
    set (DS11 := to_BinDirectSums A (x (i + 1 - 1 + 1 + 1)) (y (i + 1 - 1 + 1))).
    set (DS12 := to_BinDirectSums A (x (i + 1 - 1 + 1)) (z (i + 1 - 1))).
    set (DS13 := to_BinDirectSums A DS11 DS12).
    set (DS14 := to_BinDirectSums A (x (i - 1 + 1 + 1 + 1)) (y (i - 1 + 1 + 1))).
    set (DS15 := to_BinDirectSums A (x (i - 1 + 1 + 1)) (z (i - 1 + 1))).
    set (DS16 := to_BinDirectSums A DS14 DS15).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    (* DS4 *)
    rewrite <- (assoc _ (to_In2 A DS4)). rewrite <- (assoc _ (to_In2 A DS4)).
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In1 A DS4)).
    rewrite <- (assoc _ (to_In1 A DS4)). rewrite <- (assoc _ (to_In1 A DS4)).
    rewrite (to_Unel1' DS4). rewrite (to_Unel2' DS4). rewrite (to_IdIn1 A DS4).
    rewrite (to_IdIn2 A DS4). rewrite id_right. rewrite id_right. rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_runax''. rewrite to_runax''.
    (* DS7 *)
    rewrite <- (assoc _ (to_In1 A DS7)). rewrite <- (assoc _ (to_In1 A DS7)).
    rewrite (to_IdIn1 A DS7). rewrite (to_Unel1' DS7). rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    (* DS5 *)
    rewrite <- (assoc _ _ (to_Pr1 A DS5)). rewrite <- (assoc _ _ (to_Pr2 A DS5)).
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
    rewrite (to_IdIn1 A DS5). rewrite (to_Unel1' DS5).
    rewrite transport_source_ZeroArrow. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_binop_inv_inv. rewrite to_runax''.
    (* DS10 *)
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'.
    rewrite <- (assoc _ (to_In1 A DS10)). rewrite <- (assoc _ (to_In2 A DS10)).
    rewrite <- (assoc _ (to_In2 A DS10)). rewrite <- (assoc _ (to_In2 A DS10)).
    rewrite (to_Unel1' DS10). rewrite (to_IdIn2 A DS10). rewrite id_right. rewrite id_right.
    rewrite id_right. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''.
    (* DS9 *)
    rewrite <- (assoc _ (to_In1 A DS9)). rewrite <- (assoc _ (to_In2 A DS9)).
    rewrite (to_Unel2' DS9). rewrite (to_IdIn1 A DS9). rewrite id_right.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    (* MappingConeDiff *)
    unfold MappingConeDiff.
    unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6 DS7 DS8 DS9 DS10 DS11 DS12 DS13 DS14 DS15 DS16.
    rewrite inv_inv_eq. rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite to_binop_inv_inv.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    (* DS9 *)
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- (assoc _ (to_In2 A DS9)). rewrite <- (assoc _ (to_In2 A DS9)).
    rewrite (to_Unel2' DS9).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ (to_In1 A DS9)). rewrite (to_IdIn1 A DS9). rewrite id_right.
    (* DS5 *)
    rewrite <- (assoc _ _ (to_Pr1 A DS5)). rewrite <- (assoc _ _ (to_Pr2 A DS5)).
    rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
    rewrite (to_IdIn1 A DS5). rewrite (to_Unel1' DS5).
    rewrite transport_source_ZeroArrow.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    (* manipulate to_binops *)
    rewrite <- transport_target_to_binop. rewrite <- transport_target_to_binop.
    rewrite <- to_assoc.
    rewrite (to_commax'
               _ _ (to_Pr2 A DS3 · to_Pr1 A DS2 · f1 (i + 1) · to_In2 A DS1 · to_In1 A DS3)).
    rewrite to_assoc. rewrite to_assoc.
    rewrite <- transport_target_to_inv. rewrite <- transport_target_to_inv.
    rewrite <- to_binop_inv_comm_1.
    rewrite (to_commax'
               _ (to_inv
                    (transportf
                       (precategory_morphisms DS3)
                       (@maponpaths
                          hz A (λ i0 : pr1 hz,
                                       to_BinDirectSums
                                         A (to_BinDirectSums A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                         (to_BinDirectSums A (x (i0 + 1)) (z i0)))
                          _ _ (hzrminusplus i 1))
                       (to_Pr2 A DS3 · to_Pr1 A DS2
                               · transportf (λ x' : A, A ⟦ x', x (i - 1 + 1 + 1) ⟧)
                               (maponpaths
                                  x (maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrminusplus i 1)))
                               (identity (x (i - 1 + 1 + 1))) ·
                               Diff x (i - 1 + 1 + 1) · to_In1 A DS14 · to_In1 A DS16)))).
    rewrite to_assoc. rewrite to_assoc.
    (* binop_eq *)
    use to_binop_eq.
    - rewrite transport_target_postcompose. rewrite <- assoc. rewrite <- assoc.
      rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      rewrite <- assoc. apply cancel_precomposition. apply cancel_precomposition.
      rewrite <- transport_source_precompose. rewrite id_left.
      unfold DS3, DS2, DS1. unfold DS16, DS15, DS14.
      induction (hzrminusplus i 1). apply idpath.
    - rewrite <- (to_BinOpId A DS3). rewrite <- to_binop_inv_inv.
      assert (e1 : (to_Pr1 A DS3 · to_In1 A DS3) = (to_Pr1 A DS3 · identity _ · to_In1 A DS3)).
      {
        rewrite id_right. apply idpath.
      }
      rewrite e1. clear e1.
      assert (e2 : (to_Pr2 A DS3 · to_In2 A DS3) = (to_Pr2 A DS3 · identity _ · to_In2 A DS3)).
      {
        rewrite id_right. apply idpath.
      }
      rewrite e2. clear e2.
      rewrite <- (to_BinOpId A DS1). rewrite <- (to_BinOpId A DS2).
      rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_postmor_linear'.
      rewrite to_postmor_linear'.
      rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
      rewrite <- to_binop_inv_inv. rewrite <- to_binop_inv_inv.
      rewrite (to_commax' _ (to_Pr2 A DS3 · to_Pr2 A DS2 · to_In2 A DS2 · to_In2 A DS3)).
      rewrite <- to_assoc. rewrite <- to_assoc. rewrite <- to_assoc.
      rewrite to_assoc. rewrite to_assoc. rewrite to_assoc.
      rewrite (@to_linvax' A (Additive.to_Zero A)). rewrite to_runax''.
      rewrite (to_commax'
                 _ _ (to_inv (to_Pr1 A DS3 · to_Pr2 A DS1 · to_In2 A DS1 · to_In1 A DS3))).
      rewrite <- to_assoc. rewrite <- to_assoc.
      rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_lunax''.
      rewrite <- to_assoc. rewrite (to_commax' _ _ (transportf (precategory_morphisms DS3) _ _)).
      rewrite <- transport_target_to_binop.
      rewrite to_assoc.
      use to_binop_eq.
      + rewrite <- transport_target_to_inv. apply maponpaths.
        rewrite transport_target_postcompose. rewrite <- assoc.
        rewrite <- (assoc _ (transportf (λ x' : A, A ⟦ x', DS11 ⟧)
                                       (maponpaths
                                          x (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                                        (hzrminusplus (i + 1) 1)))
                                       (to_In1 A DS11))).
        apply cancel_precomposition.
        rewrite <- transport_target_postcompose. rewrite <- transport_source_precompose.
        set (tmp := transport_hz_double_section_source_target
                        A (λ i0 : hz, x (i0 + 1 + 1))
                        (λ i0 : hz, to_BinDirectSums
                                       A (to_BinDirectSums A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))
                        (λ i0 : hz, ((to_In1 A (to_BinDirectSums
                                                   A (x (i0 + 1 + 1)) (y (i0 + 1))))
                                        · to_In1 A (to_BinDirectSums
                                                       A (to_BinDirectSums
                                                            A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))))
                        _ _ (hzrplusminus i 1)).
        cbn in tmp. unfold DS3, DS2, DS1. use (pathscomp0 tmp). clear tmp.
        apply maponpaths.
        assert (e : (maponpaths (λ i0 : pr1 hz, x (i0 + 1 + 1)) (hzrplusminus i 1)) =
                    (maponpaths x (maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrminusplus (i + 1) 1)))).
        {
          assert (e1 : (maponpaths (λ i0 : pr1 hz, x (i0 + 1 + 1)) (hzrplusminus i 1)) =
                       (maponpaths x (maponpaths (λ i0 : pr1 hz, i0 + 1 + 1) (hzrplusminus i 1)))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e1. apply maponpaths. apply isasethz.
        }
        rewrite e. apply idpath.
      + rewrite <- to_assoc. rewrite to_commax'.
        rewrite <- (@to_runax'' A (Additive.to_Zero A)
                               _ _ (to_inv (to_Pr2 A DS3 · to_Pr1 A DS2
                                                   · to_In1 A DS2 · to_In2 A DS3))).
        use to_binop_eq.
        * apply maponpaths. rewrite transport_target_postcompose.
          rewrite <- assoc.
          rewrite <- (assoc _ (transportf (λ x' : A, A ⟦ x', x (i - 1 + 1 + 1) ⟧)
                                         (maponpaths x (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                                                   (hzrminusplus i 1)))
                                         (identity (x (i - 1 + 1 + 1))))).
          rewrite <- transport_source_precompose. rewrite id_left.
          rewrite <- (assoc _ (transportf (λ x' : A, A ⟦ x', DS15 ⟧)
                                         (maponpaths x (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                                                   (hzrminusplus i 1)))
                                         (to_In1 A DS15))).
          apply cancel_precomposition.
          rewrite <- transport_target_postcompose. rewrite <- transport_source_precompose.
          unfold DS3, DS2, DS1, DS16, DS15, DS14. induction (hzrminusplus i 1). apply idpath.
        * rewrite <- (assoc _ _ (Diff x (i - 1 + 1 + 1))).
          rewrite <- transport_source_precompose. rewrite id_left.
          unfold DS3, DS2, DS1.
          rewrite <- (@to_rinvax'
                       A (Additive.to_Zero A)
                       _ _ ((transportf
                               (precategory_morphisms
                                  (to_BinDirectSums
                                     A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1)))
                                     (to_BinDirectSums A (x (i + 1)) (z i))))
                               (@maponpaths
                                  hz A (λ i0 : pr1 hz,
                                               to_BinDirectSums
                                                 A (to_BinDirectSums
                                                      A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                                 (to_BinDirectSums A (x (i0 + 1)) (z i0)))
                                  _ _ (hzrplusminus i 1))
                               (to_Pr2 A
                                       (to_BinDirectSums
                                          A (to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1)))
                                          (to_BinDirectSums A (x (i + 1)) (z i)))
                                       · to_Pr1 A (to_BinDirectSums A (x (i + 1)) (z i)) ·
                                       Diff x (i + 1) · transportf (λ x' : A, A ⟦ x', DS11 ⟧)
                                       (maponpaths x (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                                                 (hzrminusplus (i + 1) 1)))
                                       (to_In1 A DS11) · to_In1 A DS13)))).
          apply maponpaths. apply maponpaths.
          fold DS1 DS2 DS3. rewrite transport_target_postcompose.
          rewrite transport_target_postcompose. rewrite <- assoc.
          rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
          apply cancel_precomposition. apply cancel_precomposition.
          set (tmp := transport_hz_section
                        A (λ i0 : hz, x (i0 + 1)) 1
                        (λ i0 : hz, Diff x (i0 + 1)) _ _ (! hzrminusplus i 1)).
          cbn in tmp. rewrite pathsinv0inv0 in tmp.
          assert (e : (maponpaths (λ i0 : pr1 hz, x (i0 + 1)) (hzrminusplus i 1)) =
                      (maponpaths x (maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrminusplus i 1)))).
          {
            induction (hzrminusplus i 1). apply idpath.
          }
          rewrite e in tmp. clear e. rewrite <- tmp. clear tmp.
          rewrite transport_compose. apply cancel_precomposition.
          assert (e : (! maponpaths (λ i0 : pr1 hz, x (i0 + 1))
                         (hzplusradd i (i - 1 + 1) 1 (! hzrminusplus i 1))) =
                      (maponpaths (λ i0 : pr1 hz, x (i0 + 1))
                                  (hzplusradd _ _ 1 (hzrminusplus i 1)))).
          {
            induction (hzrminusplus i 1). apply idpath.
          }
          cbn in e. rewrite e. clear e.
          rewrite <- transport_target_postcompose. rewrite <- transport_target_postcompose.
          rewrite <- transport_source_precompose.
          rewrite transport_source_target_comm.
          set (tmp := transport_hz_double_section_source_target
                        A (λ i0 : hz, x (i0 + 1 + 1))
                        (λ i0 : hz, to_BinDirectSums
                                       A (to_BinDirectSums A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))
                        (λ i0 : hz, ((to_In1 A (to_BinDirectSums
                                                   A (x (i0 + 1 + 1)) (y (i0 + 1))))
                                        · to_In1 A (to_BinDirectSums
                                                       A (to_BinDirectSums
                                                            A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))))
                        _ _ (hzrminusplus i 1)).
          cbn in tmp. unfold DS16, DS15, DS14.
          assert (e : (maponpaths (λ i0 : pr1 hz, x (i0 + 1 + 1)) (hzrminusplus i 1)) =
                      (maponpaths (λ i0 : pr1 hz, x (i0 + 1))
                                  (hzplusradd (i - 1 + 1) i 1 (hzrminusplus i 1)))).
          {
            induction (hzrminusplus i 1). apply idpath.
          }
          rewrite e in tmp. clear e.  use (pathscomp0 _ tmp). clear tmp.
          set (tmp := transport_hz_double_section_source_target
                        A (λ i0 : hz, x (i0 + 1 + 1))
                        (λ i0 : hz, to_BinDirectSums
                                       A (to_BinDirectSums A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))
                        (λ i0 : hz, ((to_In1 A (to_BinDirectSums
                                                   A (x (i0 + 1 + 1)) (y (i0 + 1))))
                                        · to_In1 A (to_BinDirectSums
                                                       A (to_BinDirectSums
                                                            A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))))
                        _ _ (hzrplusminus i 1)).
          use (pathscomp0 _ (! tmp)). clear tmp. apply maponpaths.
          assert (e : (maponpaths x (maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrminusplus (i + 1) 1))) =
                      (maponpaths (λ i0 : hz, x (i0 + 1 + 1)) (hzrplusminus i 1))).
          {
            use pathscomp0.
            - exact (maponpaths x (maponpaths (λ i0 : hz, i0 + 1 + 1) (hzrplusminus i 1))).
            - apply maponpaths. apply isasethz.
            - induction (hzrplusminus i 1). apply idpath.
          }
          rewrite e. clear e. apply idpath.
  Qed.

  Definition KAOctaMor3IsoInverses {x y z : ob (ComplexPreCat_Additive A)}
             (f1 : x --> y) (f2 : y --> z) :
    is_inverse_in_precat (# (ComplexHomotFunctor A) (KAOctaMor3 f1 f2))
                         (# (ComplexHomotFunctor A) (KAOctaMor3Inv f1 f2)).
  Proof.
    use mk_is_inverse_in_precat.
    - rewrite <- functor_comp. rewrite <- functor_id. apply maponpaths.
      use MorphismEq. exact (KAOctaMor3Iso1 f1 f2).
    - rewrite <- functor_comp. rewrite <- functor_id.
      use ComplexHomotFunctor_rel_mor'.
      + exact (KAOctaMor3InvHomot f1 f2).
      + exact (KAOctaMor3Iso2 f1 f2).
  Defined.

  Definition KAOctaMor3Iso {x y z : ob (ComplexPreCat_Additive A)} (f1 : x --> y) (f2 : y --> z) :
    is_z_isomorphism
      (# (ComplexHomotFunctor A) ((KAOctaMor3 f1 f2) : (ComplexPreCat_Additive A)⟦_, _⟧)).
  Proof.
    use mk_is_z_isomorphism.
    - exact (# (ComplexHomotFunctor A) (KAOctaMor3Inv f1 f2)).
    - exact (KAOctaMor3IsoInverses f1 f2).
  Defined.

  Definition KAOctaComm2Homot {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    ComplexHomot A (MappingCone A (MorphismComp f1 f2)) (MappingCone A (KAOctaMor1 f1 f2)).
  Proof.
    intros i. cbn.
    use compose.
    - exact (x (i + 1)).
    - exact (to_Pr1 A _).
    - use compose.
      + exact (to_BinDirectSums A (x (i - 1 + 1 + 1)) (y (i - 1 + 1))).
      + exact (to_inv (transportf (λ x' : ob A, A⟦x', _⟧)
                                  (maponpaths x (hzplusradd _ _ 1 (hzrminusplus i 1)))
                                  (to_In1 A _))).
      + exact (to_In1 A _).
  Defined.

  Local Lemma KAOctaComm2Eq {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    @to_binop (ComplexPreCat_Additive A)
              (MappingCone A (MorphismComp f1 f2)) (MappingCone A (KAOctaMor1 f1 f2))
              (MorphismComp (KAOctaMor2 f1 f2) (KAOctaMor3 f1 f2))
              (to_inv ((MappingConeIn2 A (KAOctaMor1 f1 f2))
                       : ((ComplexPreCat_Additive A)⟦_, _⟧))) =
    ComplexHomotMorphism A (KAOctaComm2Homot f1 f2).
  Proof.
    use MorphismEq. intros i. cbn. unfold KAOctaComm2Homot.
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
    set (DS1 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (y (i + 1)) (z i)).
    set (DS3 := to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))).
    set (DS4 := to_BinDirectSums A DS3 DS1).
    set (DS5 := to_BinDirectSums A ((MappingCone A f1) (i - 1 + 1))
                                 ((MappingCone A (MorphismComp f1 f2)) (i - 1))).
    set (DS6 := to_BinDirectSums A (x (i - 1 + 1 + 1)) (y (i - 1 + 1))).
    set (DS7 := to_BinDirectSums A ((MappingCone A f1) (i - 1 + 1 + 1))
                                 ((MappingCone A (MorphismComp f1 f2)) (i - 1 + 1))).
    set (DS8 := to_BinDirectSums A (x (i - 1 + 1)) (z (i - 1))).
    set (DS9 := to_BinDirectSums A DS6 DS8).
    set (DS10 := to_BinDirectSums A (x (i + 1 + 1)) (z (i + 1))).
    set (DS11 := to_BinDirectSums A (x (i - 1 + 1 + 1)) (z (i - 1 + 1))).
    set (DS12 := to_BinDirectSums A (x (i - 1 + 1 + 1 + 1)) (y (i - 1 + 1 + 1))).
    set (DS13 := to_BinDirectSums A DS12 DS11).
    set (DS14 := to_BinDirectSums A (x (i + 1 - 1 + 1 + 1)) (y (i + 1 - 1 + 1))).
    set (DS15 := to_BinDirectSums A (x (i + 1 - 1 + 1)) (z (i + 1 - 1))).
    set (DS16 := to_BinDirectSums A DS14 DS15).
    rewrite to_premor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    (* DS2 *)
    rewrite <- (assoc _ (to_In1 A DS2)). rewrite <- (assoc _ (to_In1 A DS2)).
    rewrite <- (assoc _ (to_In2 A DS2)). rewrite <- (assoc _ (to_In2 A DS2)).
    rewrite (to_IdIn1 A DS2). rewrite (to_IdIn2 A DS2). rewrite id_right. rewrite id_right.
    rewrite (to_Unel1' DS2). rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite to_lunax''.
    (* DS9 *)
    rewrite <- (assoc _ (to_In1 A DS9)). rewrite <- (assoc _ (to_In1 A DS9)).
    rewrite (to_IdIn1 A DS9). rewrite id_right. rewrite (to_Unel1' DS9).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    (* DS10 *)
    rewrite <- (assoc _ (to_In1 A DS10)).
    rewrite <- (assoc _ (to_In2 A DS10)). rewrite <- (assoc _ (to_In2 A DS10)).
    rewrite (to_IdIn1 A DS10). rewrite id_right.
    rewrite (to_Unel2' DS10).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''. rewrite to_runax''.
    (* DS6 *)
    rewrite <- (assoc (to_Pr1 A DS1)). rewrite <- (assoc (to_Pr1 A DS1)).
    rewrite <- (assoc (to_Pr1 A DS1)). rewrite <- (assoc (to_Pr1 A DS1)).
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
    rewrite to_premor_linear'.
    rewrite <- (assoc (to_Pr1 A DS1)). rewrite <- (assoc (to_Pr1 A DS1)).
    rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn1 A DS6). rewrite id_left. rewrite (to_Unel1' DS6).
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite transport_source_ZeroArrow. rewrite ZeroArrow_comp_right.
    rewrite to_runax''.
    (* unfold MappingConeDiff *)
    unfold MappingConeDiff. unfold MappingConeDiff1, MappingConeDiff2, MappingConeDiff3.
    unfold TranslationComplex. unfold DiffTranslationComplex. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6 DS7 DS8 DS9 DS10 DS11 DS12 DS13 DS14 DS15 DS16.
    rewrite <- PreAdditive_invrcomp. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn1 A DS6). rewrite id_left. rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn1 A DS6). rewrite id_left.
    rewrite (to_Unel1' DS6). rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    (* DS4 *)
    rewrite <- (id_left (to_inv (to_In2 A DS4))). rewrite <- (to_BinOpId A DS1).
    rewrite to_postmor_linear'. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invrcomp.
    rewrite (to_commax' _ _ (to_inv (to_Pr2 A DS1 · to_In2 A DS1 · to_In2 A DS4))).
    rewrite to_assoc.
    rewrite <- (to_assoc _ _ (to_inv (to_Pr2 A DS1 · to_In2 A DS1 · to_In2 A DS4))).
    rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_lunax''.
    (* Cancel to_Pr1 A DS1 *)
    rewrite PreAdditive_invrcomp.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite <- to_premor_linear'. rewrite inv_inv_eq. rewrite PreAdditive_invrcomp.
    rewrite <- to_premor_linear'.
    rewrite transport_target_postcompose. rewrite transport_target_postcompose.
    rewrite <- assoc. rewrite <- to_premor_linear'. apply cancel_precomposition.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- transport_target_to_inv.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp. rewrite inv_inv_eq.
    rewrite to_commax'.
    rewrite (to_commax'
               _ _ (to_inv
                      (transportf (λ x' : A, A ⟦ x', DS13 ⟧)
                                  (maponpaths x (hzplusradd (i - 1 + 1) i 1 (hzrminusplus i 1)))
                                  (to_In1 A DS11 · to_In2 A DS13)))).
    rewrite <- transport_target_to_binop.
    rewrite to_assoc.
    (* binop_eq *)
    use to_binop_eq.
    - rewrite <- transport_target_to_inv. apply maponpaths.
      unfold DS4, DS3, DS1. unfold DS13, DS12, DS11. induction (hzrminusplus i 1). cbn.
      unfold idfun. apply idpath.
    - rewrite to_postmor_linear'.
      rewrite (to_commax' _ _ (f1 (i - 1 + 1 + 1) · to_In2 A DS12 · to_In1 A DS13)).
      rewrite <- transport_source_to_binop. rewrite <- transport_target_to_binop.
      rewrite to_assoc.
      rewrite <- (@to_runax'' A (Additive.to_Zero A) _ _
                             (f1 (i + 1) · (to_In2 A DS3 · to_In1 A DS4))).
      use to_binop_eq.
      + unfold DS4, DS3, DS1. unfold DS13, DS12, DS11. induction (hzrminusplus i 1). cbn.
        unfold idfun. rewrite assoc. apply idpath.
      + rewrite <- PreAdditive_invlcomp.
        rewrite <- transport_source_to_inv. rewrite <- transport_target_to_inv.
        rewrite transport_source_precompose. rewrite transport_source_precompose.
        unfold DS4, DS3, DS1.
        rewrite <- (@to_linvax'
                     A (Additive.to_Zero A) _ _
                     ((transportf (precategory_morphisms (x (i + 1)))
                                  (@maponpaths
                                     hz A
                                     (λ i0 : pr1 hz,
                                             to_BinDirectSums
                                               A (to_BinDirectSums A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                               (to_BinDirectSums A (x (i0 + 1)) (z i0))) _ _
                                     (hzrminusplus i 1))
                                  (transportf (λ x' : A, A ⟦ x', x (i - 1 + 1 + 1 + 1) ⟧)
                                              (maponpaths x (hzplusradd (i - 1 + 1) i 1
                                                                        (hzrminusplus i 1)))
                                              (Diff x (i - 1 + 1 + 1)) ·
                                              to_In1 A DS12 · to_In1 A DS13)))).
        use to_binop_eq.
        * apply idpath.
        * rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
          set (tmp := transport_hz_double_section_source_target
                        A (λ i0 : hz, x (i0 + 1))
                        (λ i0 : hz, to_BinDirectSums
                                       A (to_BinDirectSums A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))
                        (λ i0 : hz, ((Diff x (i0 + 1))
                                        · to_In1 A (to_BinDirectSums
                                                       A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                        · to_In1 A (to_BinDirectSums
                                                       A (to_BinDirectSums
                                                            A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))))
                        _ _ (hzrminusplus i 1)).
          cbn in tmp.
          assert (e : (maponpaths (λ i0 : pr1 hz, x (i0 + 1)) (hzrminusplus i 1)) =
                      (maponpaths x (hzplusradd (i - 1 + 1) i 1 (hzrminusplus i 1)))).
          {
            induction (hzrminusplus i 1). apply idpath.
          }
          rewrite e in tmp. clear e. use (pathscomp0 (! tmp)). clear tmp. rewrite <- assoc.
          apply cancel_precomposition.
          rewrite <- transport_source_precompose.
          unfold DS16, DS15, DS14.
          set (tmp := transport_hz_double_section_source_target
                        A (λ i0 : hz, x (i0 + 1 + 1))
                        (λ i0 : hz, to_BinDirectSums
                                       A (to_BinDirectSums A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                       (to_BinDirectSums A (x (i0 + 1)) (z i0)))
                        (λ i0 : hz, (to_In1 A (to_BinDirectSums
                                                  A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                             · to_In1 A (to_BinDirectSums
                                                            A (to_BinDirectSums
                                                                 A (x (i0 + 1 + 1)) (y (i0 + 1)))
                                                            (to_BinDirectSums
                                                               A (x (i0 + 1)) (z i0)))))
                        _ _ (hzrplusminus i 1)).
          cbn in tmp. use (pathscomp0 tmp). clear tmp. apply maponpaths.
          assert (e : (maponpaths (λ i0 : pr1 hz, x (i0 + 1 + 1)) (hzrplusminus i 1)) =
                      (maponpaths x (hzplusradd (i + 1 - 1 + 1) (i + 1) 1
                                                (hzrminusplus (i + 1) 1)))).
          {
            assert (e' : maponpaths (λ i0 : pr1 hz, x (i0 + 1 + 1)) (hzrplusminus i 1) =
                         maponpaths x (maponpaths (λ i0 : pr1 hz, (i0 + 1 + 1))
                                                  (hzrplusminus i 1))).
            {
              induction (hzrplusminus i 1). apply idpath.
            }
            use (pathscomp0 e'). apply maponpaths. apply isasethz.
          }
          rewrite e. apply idpath.
  Qed.

  Lemma KAOctaComm2 {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    # (ComplexHomotFunctor A) (MorphismComp (KAOctaMor2 f1 f2) (KAOctaMor3 f1 f2)) =
    # (ComplexHomotFunctor A) (MappingConeIn2 A (KAOctaMor1 f1 f2)).
  Proof.
    use ComplexHomotFunctor_rel_mor'.
    - exact (KAOctaComm2Homot f1 f2).
    - exact (KAOctaComm2Eq f1 f2).
  Qed.

  Lemma KAOctaComm3 {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    MorphismComp (KAOctaMor3 f1 f2) (MappingConePr1 A (KAOctaMor1 f1 f2)) =
    MorphismComp (MappingConePr1 A f2) (# (TranslationFunctor A) (MappingConeIn2 A f1)).
  Proof.
    use MorphismEq. intros i. cbn.
    set (DS1 := to_BinDirectSums A (y (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (x (i + 1 + 1)) (y (i + 1))).
    set (DS3 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS4 := to_BinDirectSums A DS2 DS3).
    rewrite to_postmor_linear'. rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right.
    rewrite to_runax''. apply idpath.
  Qed.

  Lemma KAOctaComm4 {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    MorphismComp (KAOctaMor2 f1 f2) (MappingConePr1 A f2) =
    MorphismComp (MappingConePr1 A (MorphismComp f1 f2)) (# (TranslationFunctor A) f1).
  Proof.
    use MorphismEq. intros i. cbn. unfold TranslationMorphism_mor.
    set (DS1 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (y (i + 1)) (z i)).
    rewrite to_postmor_linear'. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn1 A DS2). rewrite id_right. rewrite <- assoc.
    rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_right.
    rewrite to_runax''. apply idpath.
  Qed.

  Lemma KAOctaComm5 {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    MorphismComp f2 (MappingConeIn2 A (MorphismComp f1 f2)) =
    MorphismComp (MappingConeIn2 A f1) (KAOctaMor1 f1 f2).
  Proof.
    use MorphismEq. intros i. cbn.
    set (DS1 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (x (i + 1)) (y i)).
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn2 A DS2). rewrite id_left.
    rewrite (to_Unel2' DS2). rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. apply idpath.
  Qed.

  Lemma KAOctaComm2' {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    (identity ((ComplexHomotFunctor A) (MappingCone A (MorphismComp f1 f2))))
      · # (ComplexHomotFunctor A) (MappingConeIn2 A (KAOctaMor1 f1 f2)) =
    # (ComplexHomotFunctor A) (KAOctaMor2 f1 f2)
      · # (ComplexHomotFunctor A) (KAOctaMor3 f1 f2).
  Proof.
    rewrite id_left.
    use (pathscomp0 _ ((functor_comp (ComplexHomotFunctor A) _ _))).
    exact (! (KAOctaComm2 f1 f2)).
  Qed.

  Lemma KAOctaComm3' {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    # (ComplexHomotFunctor A) (KAOctaMor3 f1 f2)
      · # (ComplexHomotFunctor A) (MappingConePr1 A (KAOctaMor1 f1 f2)) =
    # (ComplexHomotFunctor A) (MappingConePr1 A f2)
      · # (AddEquiv1 (TranslationHEquiv A))
      (# (ComplexHomotFunctor A) (MappingConeIn2 A f1))
      · # (AddEquiv1 (TranslationHEquiv A))
      (identity ((ComplexHomotFunctor A) (MappingCone A f1))).
  Proof.
    rewrite functor_id. rewrite id_right.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A)  _ _))).
    set (tmp := KAOctaComm3 f1 f2).
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
    use (pathscomp0 tmp). clear tmp.
    use (pathscomp0 ((functor_comp (ComplexHomotFunctor A) _ _))).
    apply cancel_precomposition.
    unfold AddEquiv1, TranslationHEquiv. cbn. apply pathsinv0.
    use TranslationFunctorHImEq. apply idpath.
  Qed.

  Lemma KAOctaComm4' {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    # (ComplexHomotFunctor A) (KAOctaMor2 f1 f2)
      · # (ComplexHomotFunctor A) (MappingConePr1 A f2) =
    # (ComplexHomotFunctor A) (MappingConePr1 A (MorphismComp f1 f2))
      · # (AddEquiv1 (TranslationHEquiv A)) (# (ComplexHomotFunctor A) f1).
  Proof.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _))).
    set (tmp := (KAOctaComm4 f1 f2)).
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
    use (pathscomp0 tmp). clear tmp.
    use (pathscomp0 ((functor_comp (ComplexHomotFunctor A) _ _))).
    apply cancel_precomposition. unfold AddEquiv1, TranslationHEquiv. cbn. apply pathsinv0.
    use TranslationFunctorHImEq. apply idpath.
  Qed.

  Lemma KAOctaComm5' {x y z : Complex A} (f1 : Morphism x y) (f2 : Morphism y z) :
    # (ComplexHomotFunctor A) (MappingConeIn2 A f1)
      · # (ComplexHomotFunctor A) (KAOctaMor1 f1 f2) =
    # (ComplexHomotFunctor A) f2
      · # (ComplexHomotFunctor A) (MappingConeIn2 A (MorphismComp f1 f2)).
  Proof.
    use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _))).
    use (pathscomp0 _ ((functor_comp (ComplexHomotFunctor A) _ _))).
    apply maponpaths. exact (! (KAOctaComm5 f1 f2)).
  Qed.

  Lemma KAOctaMor1Comm {x y z : Complex A} (f1 : Morphism x y) (g1 : Morphism y z) :
    ((KAOctaMor1 f1 g1) : ((ComplexPreCat_Additive A)⟦_, _⟧))
      · MappingConePr1 A ((f1 : ((ComplexPreCat_Additive A)⟦_, _⟧)) · g1) = MappingConePr1 A f1.
  Proof.
    use MorphismEq. intros i. cbn.
    set (DS1 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (x (i + 1)) (y i)).
    rewrite to_postmor_linear'. rewrite <- assoc. rewrite (to_IdIn1 A DS1). rewrite id_right.
    rewrite <- assoc. rewrite (to_Unel2' DS1). rewrite ZeroArrow_comp_right.
    rewrite to_runax''. apply idpath.
  Qed.

  Lemma KAOctaMor2Comm {x y z : Complex A} (f1 : Morphism x y) (g1 : Morphism y z) :
    ((MappingConeIn2 A ((f1 : ((ComplexPreCat_Additive A)⟦_, _⟧)) · g1))
     : ((ComplexPreCat_Additive A)⟦_, _⟧))
      · ((KAOctaMor2 f1 g1) : ((ComplexPreCat_Additive A)⟦_, _⟧)) =
    MappingConeIn2 A g1.
  Proof.
    use MorphismEq. intros i. cbn.
    set (DS1 := to_BinDirectSums A (x (i + 1)) (z i)).
    set (DS2 := to_BinDirectSums A (y (i + 1)) (y i)).
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn2 A DS1). rewrite id_left.
    rewrite (to_Unel2' DS1). rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. apply idpath.
  Qed.

End mapping_cone_octa.
