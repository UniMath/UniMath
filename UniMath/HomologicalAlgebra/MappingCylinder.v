(** * Mapping cylinder in C(A) *)
(** ** Introduction
- Mapping cylinder
- Let f : X -> Y be a morphism of complexes, then Y is isomorphic to Cyl(f) in K(A)
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
Require Import UniMath.HomologicalAlgebra.MappingCone.

Unset Kernel Term Sharing.

Local Open Scope hz_scope.
Local Open Scope cat.

Local Opaque hz isdecrelhzeq hzplus iscommrngops ZeroArrow.

(** * Mapping cylinder *)
(** ** Introduction
In this section we construct the mapping cylinder, which is a complex, of a morphism f : C_1 -> C_2
of complexes. We denote mapping cylinder of f by Cyl(f). The objects of mapping cylinder are given
by C_1^i ⊕ Cone(f)^i. The ith differential of Cyl(f) is given by
         #  p_1 · d^i_X · i_1 - p_2 · p1 · i_1 + p_2 · d^i_C(f) · i_2 #

Here d^i_C(F) is the ith differential of the mapping cone of f, see section [mapping_cone].
We split the definition of the ith differential into a sum of 3 morphisms. These are constructed in
[MappingCylinderDiff1], [MappingCylinderDiff3], and [MappingCylinderDiff3], and correspond the
morphisms of the above formula, respectively. In [MappingCylinderDiff] we construct the
differential. In [MappingCylinder_comp] we show that composition of two consecutive differentials
is 0. The complex Cyl(f) is constructed in [MappingCylinder].
*)
Section mapping_cylinder.

  Variable A : Additive.

  (**  # p_1 · d^i_X · i_1 # *)
  Definition MappingCylinderDiff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1' DS1 DS2' DS2.
    use compose.
    - exact (C1 i).
    - exact (to_Pr1 A DS1).
    - use compose.
      + exact (C1 (i + 1)).
      + exact (Diff C1 i).
      + exact (to_In1 A DS2).
  Defined.

  (**  # p_2 · (- p1) · i_1 # *)
  Definition MappingCylinderDiff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1' DS1 DS2' DS2.
    use compose.
    - exact (DS1').
    - exact (to_Pr2 A DS1).
    - use compose.
      + exact ((TranslationComplex A C1) i).
      + exact (to_inv (to_Pr1 A DS1')).
      + exact (to_In1 A DS2).
  Defined.

  (** p_2 · d^i_C(f) · i_2 *)
  Definition MappingCylinderDiff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1' DS1 DS2' DS2.
    use compose.
    - exact DS1'.
    - exact (to_Pr2 A DS1).
    - use compose.
      + exact DS2'.
      + exact (MappingConeDiff A f i).
      + exact (to_In2 A DS2).
  Defined.

  Definition MappingCylinderDiff {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1 DS2.
    use to_binop.
    - exact (MappingCylinderDiff1 f i).
    - use to_binop.
      +  exact (MappingCylinderDiff2 f i).
      +  exact (MappingCylinderDiff3 f i).
  Defined.

  Lemma MappingCylinder_Diff1_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 i) (MappingCone A f i) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) (MappingCone A f i) in
    (MappingCylinderDiff1 f i) · (MappingCylinderDiff1 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingCylinderDiff1. unfold MappingCylinderDiff2. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A _)).
    set (DS3 := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_IdIn1 A DS3). rewrite id_right. rewrite <- (assoc _ _ (Diff C1 (i + 1))).
    rewrite (DSq A C1 i). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply idpath.
  Qed.

  Lemma MappingCylinder_Diff1_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff1 f i) · (MappingCylinderDiff2 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff1. unfold MappingCylinderDiff2. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCylinder_Diff1_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff1 f i) · (MappingCylinderDiff3 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff1. unfold MappingCylinderDiff3. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCylinder_Diff2_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff2 f i) · (MappingCylinderDiff2 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff2. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCylinder_Diff2_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff2 f i) · (MappingCylinderDiff3 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MapingCylinder_Diff3_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff3 f i) · (MappingCylinderDiff3 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff3. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_IdIn2 A DS). rewrite id_right. rewrite <- (assoc _ (MappingConeDiff A f i)).
    set (tmp := DSq A (MappingCone A f) i). cbn in tmp. cbn. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Lemma MappingCylinder_comp {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    MappingCylinderDiff f i · MappingCylinderDiff f (i + 1) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff. cbn.
    set (D11 := MappingCylinder_Diff1_Diff1 f i).
    set (D12 := MappingCylinder_Diff1_Diff2 f i).
    set (D13 := MappingCylinder_Diff1_Diff3 f i).
    set (D22 := MappingCylinder_Diff2_Diff2 f i).
    set (D23 := MappingCylinder_Diff2_Diff3 f i).
    set (D33 := MapingCylinder_Diff3_Diff3 f i).
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    cbn. cbn in D11. rewrite D11. cbn in D12. rewrite D12. cbn in D13. rewrite D13.
    cbn in D22. rewrite D22. cbn in D23. rewrite D23. cbn in D33. rewrite D33.
    rewrite to_lunax''. rewrite to_lunax''. rewrite to_runax''. rewrite to_runax''.
    rewrite to_lunax''. rewrite to_runax''.
    unfold MappingCylinderDiff1. unfold MappingCylinderDiff2. unfold MappingCylinderDiff3.
    cbn. clear D11 D12 D13 D22 D23 D33.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS1' := to_BinDirectSums A (C1 i) DS1).
    set (DS2 := to_BinDirectSums A (C1 (i + 1 + 1 + 1)) (C2 (i + 1 + 1))).
    set (DS2' := to_BinDirectSums A (C1 (i + 1 + 1)) DS2).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS3' := to_BinDirectSums A (C1 (i + 1)) DS3). cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- (assoc _ _ (to_Pr1 A DS3')). rewrite (to_IdIn1 A DS3'). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr1 A DS3')). rewrite (to_Unel2' DS3').
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS3')). rewrite (to_IdIn2 A DS3').
    rewrite id_right. rewrite to_binop_inv_inv.
    apply cancel_inv. rewrite inv_inv_eq. rewrite to_inv_zero.
    rewrite <- to_postmor_linear'.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (to_In1 A DS2')). apply cancel_postcomposition.
    rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (to_Pr2 A DS1')). apply cancel_precomposition.
    unfold MappingConeDiff.
    unfold MappingConeDiff1. unfold MappingConeDiff2. unfold MappingConeDiff3.
    cbn in *. fold DS1 DS1' DS2 DS2' DS3 DS3'. unfold DiffTranslationComplex.
    rewrite assoc. rewrite assoc. rewrite <- PreAdditive_invrcomp.
    rewrite to_postmor_linear'. rewrite <- (assoc _ _ (to_Pr1 A DS3)).
    rewrite (to_IdIn1 A DS3). rewrite id_right. cbn.
    rewrite to_postmor_linear'. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS3)). rewrite <- (assoc _ _ (to_Pr1 A DS3)).
    rewrite (to_Unel2' DS3). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite to_runax''. rewrite to_runax''. rewrite (@to_rinvax' A (Additive.to_Zero A)).
    apply idpath.
  Qed.

  Definition MappingCylinder {C1 C2 : Complex A} (f : Morphism C1 C2) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (to_BinDirectSums
                         A (C1 i) (to_BinDirectSums A (TranslationComplex A C1 i) (C2 i))).
    - intros i. exact (MappingCylinderDiff f i).
    - intros i. cbn beta. exact (MappingCylinder_comp f i).
  Defined.

End mapping_cylinder.


(** * Let f : X -> Y, then Y is isomorphic to Cyl(f) in K(A) *)
(** ** Introduction
We show that in K(A) Y and Cyl(f) are isomorphic. The isomorphism is given by the morphisms
α := i_2 · i_2 and β := p_1 · f + p_2 · p_2. We have α · β = id in C(A), but
β · α ≠ id_{Cyl(f)} in C(A). We define a homotopy by χ^i := p_1 · i_1 · i_2 : Cyl(f)^i -->
Cyl(f)^{i-1}. We show that
       # id_{Cyl(f)} - β · α = χ^i · d^{i-1}_{Cyl(f)} + d^i_{Cyl(f)} · χ^{i-1} #
       $ id_{Cyl(f)} - β · α = χ^i · d^{i-1}_{Cyl(f)} + d^i_{Cyl(f)} · χ^{i-1} $  ( * )
This means that β · α = id_{Cyl(f)} in K(A) by the definition of homotopy of morphisms.
Hence Y and C(f) are isomorphic.

The morphisms α and β are defined in [MappingCylinderMor1_mor] and [MappingCylinderMor2_mor].
The equality α · β = id is proven in [MappingCylinderIso_eq1]. The homotopy χ is constructed
in [MappingCylinderIsoHomot]. The equality ( * ) is proven in 4 steps. These steps are
[MappingCylinderIsoHomot_eq1], [MappingCylinderIsoHomot_eq2], [MappingCylinderIsoHomot_eq3],
and [MappingCylinderIsoHomot_eq4]. The equality β · α = id is proved in [MappingCylinderIso_eq2].
The fact that Y and Cyl(f) are isomorphic in K(A) is proved in [MappingCylinderIso].
*)
Section mapping_cylinder_KA_iso.

  Variable A : Additive.


  Definition MappingCylinderMor1_mor {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
             (i : hz) : A ⟦ C2 i, (MappingCylinder A f) i ⟧.
  Proof.
    unfold MappingCylinder. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use compose.
    - exact DS1.
    - use (to_In2 A DS1).
    - use (to_In2 A DS2).
  Defined.

  Lemma MappingCylinderMor1_comm {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    MappingCylinderMor1_mor f i · Diff (MappingCylinder A f) i =
    Diff C2 i · MappingCylinderMor1_mor f (i + 1).
  Proof.
    unfold MappingCylinderMor1_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C1 (i + 1)) DS3). rewrite assoc.
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_premor_linear'. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS2)). rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_premor_linear'. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS2)). rewrite (to_IdIn2 A DS2).
    rewrite id_right. rewrite <- PreAdditive_invrcomp.
    rewrite (to_Unel2' DS1). rewrite to_inv_zero. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. apply cancel_postcomposition.
    unfold MappingConeDiff. unfold MappingConeDiff1.
    unfold MappingConeDiff2. unfold MappingConeDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_premor_linear'. rewrite assoc.
    rewrite (to_Unel2' DS1). rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite to_premor_linear'. rewrite assoc. rewrite (to_Unel2' DS1).
    rewrite ZeroArrow_comp_left. rewrite to_lunax''. rewrite assoc.
    rewrite (to_IdIn2 A DS1). rewrite id_left. apply idpath.
  Qed.

  Definition MappingCylinderMor1 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (ComplexPreCat_Additive A)⟦(ComplexHomotFunctor A C2),
                              (ComplexHomotFunctor A (MappingCylinder A f))⟧.
  Proof.
    cbn. use mk_Morphism.
    - intros i. exact (MappingCylinderMor1_mor f i).
    - intros i. exact (MappingCylinderMor1_comm f i).
  Defined.

  Definition MappingCylinderMor2_mor {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
             (i : hz) : A ⟦ (MappingCylinder A f) i, C2 i ⟧.
  Proof.
    unfold MappingCylinder. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use to_binop.
    - use compose.
      + exact (C1 i).
      + use (to_Pr1 A DS2).
        + exact (MMor f i).
    - use compose.
      + exact DS1.
      + use (to_Pr2 A DS2).
      + use (to_Pr2 A DS1).
  Defined.

  Lemma MappingCylinderMor2_comm {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    MappingCylinderMor2_mor f i · Diff C2 i =
    Diff (MappingCylinder A f) i · MappingCylinderMor2_mor f (i + 1).
  Proof.
    unfold MappingCylinderMor2_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C1 (i + 1)) DS3).
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_Unel1' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_Unel1' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_Unel2' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_IdIn2 A DS4). rewrite id_right.
    rewrite <- assoc. rewrite (MComm f i). rewrite assoc. use to_rrw.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'.
    apply cancel_precomposition.
    unfold MappingConeDiff. unfold MappingConeDiff1.
    unfold MappingConeDiff2. unfold MappingConeDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_Unel1' DS3).
    rewrite ZeroArrow_comp_right. rewrite to_lunax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_IdIn2 A DS3). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_IdIn2 A DS3). rewrite id_right.
    rewrite <- PreAdditive_invlcomp. rewrite <- to_assoc.
    rewrite (@to_linvax' A (Additive.to_Zero A)). rewrite to_lunax''. apply idpath.
  Qed.

  Definition MappingCylinderMor2 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (ComplexPreCat_Additive A)⟦(ComplexHomotFunctor A (MappingCylinder A f)),
                               (ComplexHomotFunctor A C2)⟧.
  Proof.
    cbn. use mk_Morphism.
    - intros i. exact (MappingCylinderMor2_mor f i).
    - intros i. exact (MappingCylinderMor2_comm f i).
  Defined.

  Lemma MappingCylinderIso_eq1' {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (MappingCylinderMor1 f) · (MappingCylinderMor2 f) = identity _.
  Proof.
    use MorphismEq. intros i. cbn. unfold MappingCylinderMor1_mor.
    unfold MappingCylinderMor2_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    rewrite to_premor_linear'. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS2)). rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS2)). rewrite (to_IdIn2 A DS2). rewrite id_right.
    rewrite (to_IdIn2 A DS1). apply idpath.
  Qed.

  Lemma MappingCylinderIso_eq1 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (# (ComplexHomotFunctor A) (MappingCylinderMor1 f))
      · (# (ComplexHomotFunctor A) (MappingCylinderMor2 f)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite MappingCylinderIso_eq1'. rewrite functor_id.
    apply idpath.
  Qed.

  Lemma MappingCylinderIsoHomot {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    ComplexHomot A (MappingCylinder A f) (MappingCylinder A f).
  Proof.
    intros i. unfold MappingCylinder. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
    set (DS4 := to_BinDirectSums A (C1 (i - 1)) DS3).
    use compose.
    - exact (C1 i).
    - exact (to_Pr1 A DS2).
    - use compose.
      + exact DS3.
      + exact (transportf (λ x' : ob A, precategory_morphisms x' DS3)
                          (maponpaths C1 (hzrminusplus i 1)) (to_In1 A DS3)).
      + exact (to_inv (to_In2 A DS4)).
  Defined.

  Definition MappingCylinderIsoHomot_mor1 {C1 C2 : Complex A}
             (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) (i : hz) :
    A⟦(MappingCylinder A f) i, (MappingCylinder A f) i⟧.
  Proof.
    cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use to_binop.
    - use compose.
      + exact (C1 i).
      + exact (to_Pr1 A DS2).
      + exact (to_In1 A DS2).
    - use to_binop.
      + use compose.
        * exact (C1 i).
        * exact (to_Pr1 A DS2).
        * use compose.
          -- exact (C1 (i + 1)).
          -- exact (Diff C1 i).
          -- use compose.
             ++ exact DS1.
             ++ exact (to_In1 A DS1).
             ++ exact (to_In2 A DS2).
      + use compose.
        * exact (C1 i).
        * exact (to_Pr1 A DS2).
        * use compose.
          -- exact (C2 i).
          -- exact (to_inv (MMor f i)).
          -- use compose.
             ++ exact DS1.
             ++ exact (to_In2 A DS1).
             ++ exact (to_In2 A DS2).
  Defined.

  Lemma MappingCylinderIsoHomot_eq1 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    (transportf (precategory_morphisms
                   (to_BinDirectSums A (C1 i) (to_BinDirectSums A (C1 (i + 1)) (C2 i))))
                (maponpaths (λ (i0 : hz),
                             BinDirectSumOb
                               A (to_BinDirectSums
                                    A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                            (hzrminusplus i 1))
                (MappingCylinderIsoHomot f i · MappingCylinderDiff A f (i - 1))) =
    MappingCylinderIsoHomot_mor1 f i.
  Proof.
    cbn. rewrite transport_target_postcompose.
    unfold MappingCylinderIsoHomot. unfold MappingCylinderIsoHomot_mor1. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
    set (DS4 := to_BinDirectSums A (C1 (i - 1)) DS3).
    set (DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
    set (DS6 := to_BinDirectSums A (C1 (i - 1 + 1)) DS5). cbn.
    rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'. rewrite <- to_premor_linear'.
    apply cancel_precomposition. rewrite <- transport_target_postcompose.
    rewrite assoc. rewrite assoc. rewrite <- to_postmor_linear'.
    rewrite <- transport_target_postcompose. rewrite <- transport_source_precompose.
    (* Unfold MappingCylinderDiff *)
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6. cbn. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    (* simplify *)
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invlcomp. rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right. rewrite to_inv_zero.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp. rewrite assoc.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_IdIn2 A DS4). rewrite id_right.
    rewrite inv_inv_eq.
    (* Unfold MappingConeDiff *)
    unfold MappingConeDiff. unfold MappingConeDiff1.
    unfold MappingConeDiff2. unfold MappingConeDiff3. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6. cbn. rewrite to_premor_linear'.
    rewrite assoc. rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc.
    rewrite (to_IdIn1 A DS3). rewrite id_left. rewrite id_left.
    rewrite (to_Unel1' DS3). rewrite id_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    unfold DiffTranslationComplex. cbn.
    (* rewrite transports *)
    rewrite <- transport_source_to_binop. rewrite <- transport_target_to_binop.
    rewrite <- transport_source_to_inv. rewrite <- transport_target_to_inv. cbn.
    rewrite to_postmor_linear'.
    rewrite <- transport_source_to_binop. rewrite <- transport_target_to_binop.
    (* The first terms of to_binop are equal, cancel them *)
    assert (e1 : (transportf
                    (precategory_morphisms (C1 i))
                    (maponpaths
                       (λ (i0 : pr1 hz),
                        BinDirectSumOb
                          A (to_BinDirectSums
                               A (C1 i0)
                               (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                       (hzrminusplus i 1))
                    (transportf (λ x' : A, A ⟦ x', DS6 ⟧) (maponpaths C1 (hzrminusplus i 1))
                                (to_In1 A DS6))) = (to_In1 A DS2)).
    {
      cbn. unfold DS2, DS1, DS6, DS5.
      set (tmp := λ (i0 : hz),
                    BinDirectSumOb
                      A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))).
      set (tmp'' := (λ (i0 : hz),
                       to_In1 A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0))))).
      set (tmp' := @transport_hz_double_section_source_target
                     A C1 tmp tmp'' _ _ (hzrminusplus i 1)).
      unfold tmp'' in tmp'.
      rewrite tmp'. unfold tmp. apply idpath.
    }
    cbn in e1. cbn. rewrite <- e1. clear e1. use to_rrw.
    (* The first term of to_binop are equal, cancel them *)
    rewrite <- to_binop_inv_inv. rewrite transport_target_to_inv. rewrite transport_source_to_inv.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp. rewrite inv_inv_eq.
    rewrite transport_target_to_inv. rewrite transport_source_to_inv. rewrite PreAdditive_invlcomp.
    rewrite PreAdditive_invlcomp. rewrite to_postmor_linear'.
    assert (e1 : (transportf (precategory_morphisms (C1 i))
                             (maponpaths
                                (λ (i0 : pr1 hz),
                                 BinDirectSumOb
                                   A (to_BinDirectSums
                                        A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                                (hzrminusplus i 1))
                             (transportf (λ x' : A, A ⟦ x', DS6 ⟧)
                                         (maponpaths C1 (hzrminusplus i 1))
                                         (Diff C1 (i - 1 + 1) · to_In1 A DS5 · to_In2 A DS6))) =
                 (Diff C1 i · to_In1 A DS1 · to_In2 A DS2)).
    {
      cbn. unfold DS2, DS1, DS6, DS5.
      set (tmp := λ i0 : hz, BinDirectSumOb
                                A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                (C2 i0)))).
      set (tmp'' := (λ (i0 : hz),
                       (Diff C1 i0)
                         · (to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                         · (to_In2 A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                    (C2 i0)))))).
      set (tmp' := @transport_hz_double_section_source_target
                     A C1 tmp tmp'' _ _ (hzrminusplus i 1)).
      unfold tmp'' in tmp'.
      rewrite tmp'. unfold tmp. apply idpath.
    }
    rewrite <- e1. clear e1. use to_rrw.
    (* Solve the rest *)
    cbn. unfold DS2, DS1, DS6, DS5.
    set (tmp := λ i0 : hz, BinDirectSumOb
                              A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0)))).
    set (tmp'' := (λ (i0 : hz),
                     (to_inv (MMor f i0))
                       · (to_In2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                       · (to_In2 A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                  (C2 i0)))))).
    set (tmp' := @transport_hz_double_section_source_target A C1 tmp tmp'' _ _ (hzrminusplus i 1)).
    unfold tmp'' in tmp'.
    rewrite tmp'. unfold tmp. apply idpath.
  Qed.

  Definition MappingCylinderIsoHomot_mor2 {C1 C2 : Complex A}
             (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) (i : hz) :
    A⟦(MappingCylinder A f) i, (MappingCylinder A f) i⟧.
  Proof.
    cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use to_binop.
    - use compose.
      + exact (C1 i).
      + exact (to_Pr1 A DS2).
      + use compose.
        * exact (C1 (i + 1)).
        * exact (to_inv (Diff C1 i)).
        * use compose.
          -- exact DS1.
          -- exact (to_In1 A DS1).
          -- exact (to_In2 A DS2).
    - use compose.
      + exact DS1.
      + exact (to_Pr2 A DS2).
      + use compose.
        * exact (C1 (i + 1)).
        * exact (to_Pr1 A DS1).
        * use compose.
          -- exact DS1.
          -- exact (to_In1 A DS1).
          -- exact (to_In2 A DS2).
  Defined.

  Lemma MappyngCylinderIsoHomot_eq2 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    (transportf (precategory_morphisms
                   (to_BinDirectSums A (C1 i) (to_BinDirectSums A (C1 (i + 1)) (C2 i))))
                (maponpaths (λ (i0 : pr1 hz),
                             BinDirectSumOb
                               A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                               (C2 i0))))
                            (hzrplusminus i 1))
                (MappingCylinderDiff A f i · MappingCylinderIsoHomot f (i + 1))) =
    MappingCylinderIsoHomot_mor2 f i.
  Proof.
    cbn. unfold MappingCylinderIsoHomot. unfold MappingCylinderIsoHomot_mor2. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C1 (i + 1)) DS3).
    set (DS5 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS6 := to_BinDirectSums A (C1 (i + 1 - 1)) DS5). cbn.
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6. cbn.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite <- transport_target_to_binop.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_Unel2' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    (* The first terms of to_binop are equal, cancel them *)
    assert (e1 : (transportf (precategory_morphisms DS2)
                             (maponpaths
                                (λ (i0 : pr1 hz),
                                 BinDirectSumOb
                                   A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                   (C2 i0))))
                                (hzrplusminus i 1))
                             (to_Pr1 A DS2 · Diff C1 i · transportf (λ x' : A, A ⟦ x', DS5 ⟧)
                                     (maponpaths C1 (hzrminusplus (i + 1) 1))
                                     (to_In1 A DS5) · to_inv (to_In2 A DS6))) =
                 ((to_Pr1 A DS2) · (to_inv (Diff C1 i)) · (to_In1 A DS1) · (to_In2 A DS2))).
    {
      rewrite transport_target_postcompose. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      rewrite <- assoc. apply cancel_precomposition.
      rewrite <- PreAdditive_invlcomp. rewrite PreAdditive_invrcomp. apply cancel_precomposition.
      rewrite <- transport_target_postcompose. rewrite <- transport_source_precompose.
      rewrite <- PreAdditive_invrcomp.
      unfold DS2, DS1, DS6, DS5.
      set (tmp := λ i0 : hz, BinDirectSumOb
                                A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                (C2 i0)))).
      set (tmp'' := (λ i0 : hz,
                       (to_inv ((to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                                  · (to_In2 A (to_BinDirectSums
                                                  A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0)))))))).
      set (tmp' := @transport_hz_double_section_source_target
                     A (λ i0 : hz, C1 (i0 + 1)) tmp tmp'' _ _ (hzrplusminus i 1)).
      unfold tmp'' in tmp'. rewrite tmp'. clear tmp'. unfold tmp. clear tmp.
      clear tmp''. apply maponpaths.
      rewrite <- transport_source_to_inv. rewrite <- transport_source_to_inv.
      apply maponpaths. rewrite transport_source_precompose. rewrite transport_source_precompose.
      apply cancel_postcomposition.
      assert (e2 : maponpaths C1 (hzrminusplus (i + 1) 1) =
                   maponpaths (λ i0 : hz, C1 (i0 + 1)) (hzrplusminus i 1)).
      {
        assert (e3 : maponpaths (λ i0 : hz, C1 (i0 + 1)) (hzrplusminus i 1) =
                     maponpaths C1 (maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1))).
        {
          induction (hzrplusminus i 1). apply idpath.
        }
        rewrite e3. clear e3. apply maponpaths. apply isasethz.
      }
      rewrite <- e2. apply idpath.
    }
    cbn in e1. cbn. rewrite <- e1. clear e1. use to_rrw.
    (* Use similar technique as above *)
    rewrite transport_target_postcompose. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite <- assoc. apply cancel_precomposition.
    rewrite <- PreAdditive_invlcomp. rewrite PreAdditive_invrcomp. apply cancel_precomposition.
    rewrite <- transport_target_postcompose. rewrite <- transport_source_precompose.
    rewrite <- PreAdditive_invrcomp.
    unfold DS2, DS1, DS6, DS5.
    rewrite transport_target_to_inv. rewrite transport_source_to_inv.
    rewrite inv_inv_eq.
    set (tmp := λ i0 : hz, BinDirectSumOb
                              A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0)))).
    set (tmp'' := (λ i0 : hz,
                     (to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                       · (to_In2 A (to_BinDirectSums
                                       A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))))).
    set (tmp' := @transport_hz_double_section_source_target
                   A (λ i0 : hz, C1 (i0 + 1)) tmp tmp'' _ _ (hzrplusminus i 1)).
    unfold tmp'' in tmp'.
    rewrite tmp'. clear tmp'. unfold tmp. clear tmp. clear tmp''. apply maponpaths.
    rewrite transport_source_precompose. rewrite transport_source_precompose.
    apply cancel_postcomposition.
    assert (e2 : maponpaths C1 (hzrminusplus (i + 1) 1) =
                 maponpaths (λ i0 : hz, C1 (i0 + 1)) (hzrplusminus i 1)).
    {
      assert (e3 : maponpaths (λ i0 : hz, C1 (i0 + 1)) (hzrplusminus i 1) =
                   maponpaths C1 (maponpaths (λ i0 : hz, i0 + 1) (hzrplusminus i 1))).
      {
        induction (hzrplusminus i 1). apply idpath.
        }
        rewrite e3. clear e3. apply maponpaths. apply isasethz.
    }
    rewrite <- e2. apply idpath.
  Qed.

  Lemma MappingCylinderisoHomot_eq3 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i) in
    let DS2 := to_BinDirectSums A (C1 i) DS1 in
    to_binop DS2 DS2
             (to_binop DS2 DS2 (to_Pr1 A DS2 · to_In1 A DS2)
                       (to_Pr2 A DS2 · to_Pr1 A DS1 · to_In1 A DS1 · to_In2 A DS2))
             (to_inv (to_Pr1 A DS2 · MMor f i · to_In2 A DS1 · to_In2 A DS2)) =
    to_binop DS2 DS2 (MappingCylinderIsoHomot_mor1 f i) (MappingCylinderIsoHomot_mor2 f i).
  Proof.
    intros DS1 DS2.
    unfold MappingCylinderIsoHomot_mor1. unfold MappingCylinderIsoHomot_mor2.
    cbn. fold DS1 DS2. cbn. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite to_assoc. rewrite to_assoc. use to_rrw. rewrite to_commax'.
    rewrite (to_commax'
               _ _ ((to_Pr1 A DS2) · (to_inv (MMor f i)) · (to_In2 A DS1) · (to_In2 A DS2))).
    rewrite to_assoc. rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. use to_rrw. rewrite <- to_assoc.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite (@to_rinvax' A (Additive.to_Zero A)).
    rewrite to_lunax''. apply idpath.
  Qed.

  Lemma MappingCylinderIsoHomot_eq {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    to_binop _ _ (identity _) (to_inv (MappingCylinderMor2 f · MappingCylinderMor1 f)) =
    ComplexHomotMorphism A (MappingCylinderIsoHomot f).
  Proof.
    use MorphismEq. intros i. cbn.
    unfold MappingCylinderMor1_mor. unfold MappingCylinderMor2_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    rewrite to_postmor_linear'. rewrite <- to_binop_inv_inv.
    rewrite <- (to_BinOpId A DS2).
    assert (e : to_Pr2 A DS2 · to_In2 A DS2 = to_Pr2 A DS2 · identity _ · to_In2 A DS2).
    {
      rewrite id_right. apply idpath.
    }
    rewrite e. clear e. rewrite <- (to_BinOpId A DS1). rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite to_assoc. rewrite to_assoc.
    rewrite (to_commax'
               _ (to_inv (to_Pr1 A DS2 · MMor f i · to_In2 A DS1 · to_In2 A DS2))).
    rewrite <- (to_assoc
                 _ _ _ (to_inv (to_Pr1 A DS2 · MMor f i · to_In2 A DS1 · to_In2 A DS2))).
    rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_lunax''. rewrite <- to_assoc.
    use (pathscomp0 (MappingCylinderisoHomot_eq3 f i)).
    rewrite <- (MappingCylinderIsoHomot_eq1 f i). rewrite <- (MappyngCylinderIsoHomot_eq2 f i).
    unfold DS2. unfold DS1. apply idpath.
  Qed.

  Lemma MappingCylinderIso_eq2 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (# (ComplexHomotFunctor A) (MappingCylinderMor2 f))
      · (# (ComplexHomotFunctor A) (MappingCylinderMor1 f)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite <- functor_id. apply pathsinv0.
    use ComplexHomotFunctor_rel_mor'.
    - exact (MappingCylinderIsoHomot f).
    - exact (MappingCylinderIsoHomot_eq f).
  Qed.

  Definition MappingCylinderIso {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    iso (ComplexHomotFunctor A C2) (ComplexHomotFunctor A (MappingCylinder A f)).
  Proof.
    use tpair.
    - exact (# (ComplexHomotFunctor A) (MappingCylinderMor1 f)).
    - use is_iso_qinv.
      + exact (# (ComplexHomotFunctor A) (MappingCylinderMor2 f)).
      + split.
        * exact (MappingCylinderIso_eq1 f).
        * exact (MappingCylinderIso_eq2 f).
  Qed.

End mapping_cylinder_KA_iso.

Local Transparent hz isdecrelhzeq hzplus iscommrngops ZeroArrow.
Close Scope hz_scope.
