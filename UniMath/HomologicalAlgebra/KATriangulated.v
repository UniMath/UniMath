(** * K(A) is a triangulated category *)
(** Contents
- K(A) triangulated
 - Octahedral axiom
 - K(A) triangulated
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
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
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
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.ShortExactSequences.
Require Import UniMath.CategoryTheory.categories.abgrs.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Morphisms.
Require Import UniMath.CategoryTheory.AdditiveFunctors.

Require Import UniMath.HomologicalAlgebra.Complexes.
Require Import UniMath.HomologicalAlgebra.Triangulated.
Require Import UniMath.HomologicalAlgebra.KA.
Require Import UniMath.HomologicalAlgebra.TranslationFunctors.
Require Import UniMath.HomologicalAlgebra.MappingCone.
Require Import UniMath.HomologicalAlgebra.KAPreTriangulated.

Unset Kernel Term Sharing.
Opaque hz isdecrelhzeq hzplus hzminus hzone hzzero iscommringops ZeroArrow.

(** * K(A) as a triangulated category *)
Section KATriangulated.

  Context {A : CategoryWithAdditiveStructure}.

  Local Opaque ComplexHomotFunctor ComplexHomotSubset Quotcategory identity
        MappingConePr1 MappingConeIn2 RotMorphism RotMorphismInv InvRotMorphism InvRotMorphismInv
        to_inv compose to_abgr pathsinv0 pathscomp0 ishinh.

  Definition KATriangOcta_TriIso {x y z : ob (@KAPreTriang A)} {f1 : x --> y} {g1 : y --> z}
             (f1' : hfiber # (ComplexHomotFunctor A) f1)
             (g1' : hfiber # (ComplexHomotFunctor A) g1)
             (f1'' := hfiberpr1 _ _ f1') (g1'' := hfiberpr1 _ _ g1')
             (i' := hfiberpair # (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1'')
                               (idpath (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1'')))) :
        TriIso
      (@mk_Tri KAPreTriang Trans _ _ _
               (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1''))
               (# (ComplexHomotFunctor A) (KAOctaMor2 f1'' g1''))
               (# (ComplexHomotFunctor A) (MappingConePr1 A g1'')
                  · # (AddEquiv1 (@Trans KAPreTriang))
                  (# (ComplexHomotFunctor A) (MappingConeIn2 A f1''))))
      (MappingConeTri (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1'')) i').
  Proof.
    use mk_TriIso.
    * use mk_TriMor.
      -- use mk_MPMor.
         ++ use mk_MPMorMors.
            ** exact (identity _).
            ** exact (identity _).
            ** exact (# (ComplexHomotFunctor A) (KAOctaMor3 f1'' g1'')).
         ++ use mk_MPMorComms.
            ** exact (! (KAIdComm _ _ (idpath _))).
            ** exact (KAOctaComm2' f1'' g1'').
      -- exact (KAOctaComm3' f1'' g1'').
    * use mk_TriMor_is_iso.
      ++ exact (is_z_isomorphism_identity _).
      ++ exact (is_z_isomorphism_identity _).
      ++ exact (KAOctaMor3Iso f1'' g1'').
  Defined.

  Definition KATriangOcta_KADTriData {x y z : ob (@KAPreTriang A)} {f1 : x --> y} {g1 : y --> z}
             (f1' : hfiber # (ComplexHomotFunctor A) f1)
             (g1' : hfiber # (ComplexHomotFunctor A) g1)
             (f1'' := hfiberpr1 _ _ f1') (g1'' := hfiberpr1 _ _ g1')  :
    KADTriData
      (@mk_Tri KAPreTriang Trans _ _ _
               (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1''))
               (# (ComplexHomotFunctor A) (KAOctaMor2 f1'' g1''))
               (# (ComplexHomotFunctor A) (MappingConePr1 A g1'')
                  · # (AddEquiv1 (@Trans KAPreTriang))
                  (# (ComplexHomotFunctor A) (MappingConeIn2 A f1'')))).
  Proof.
    use mk_KADTriData.
    + exact (Morphisms.mk_Morphism (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1''))).
    + exact (hfiberpair (# (ComplexHomotFunctor A)) (KAOctaMor1 f1'' g1'') (idpath _)).
    + exact (KATriangOcta_TriIso f1' g1').
  Defined.

  Lemma KATriangOcta_hfiber_comp_eq {x y z : ob (@KAPreTriang A)} (f : x --> y) (g : y --> z)
        (f' : hfiber (# (ComplexHomotFunctor A)) f) (g' : hfiber (# (ComplexHomotFunctor A)) g)
        (f'' := hfiberpr1 # (ComplexHomotFunctor A) f f')
        (g'' := hfiberpr1 # (ComplexHomotFunctor A) g g'):
    # (ComplexHomotFunctor A) (f'' ·  g'') = f · g.
  Proof.
    unfold f'', g''.
    rewrite functor_comp. rewrite hfiberpr2. rewrite hfiberpr2. apply idpath.
  Qed.

  Lemma KATriangOcta {x1 x2 y1 y2 z1 z2 : ob (@KAPreTriang A)}
             {f1 : x1 --> y1} {f2 : y1 --> z2} {f3 : z2 --> (AddEquiv1 Trans x1)}
             {g1 : y1 --> z1} {g2 : z1 --> x2} {g3 : x2 --> (AddEquiv1 Trans y1)}
             {h2 : z1 --> y2} {h3 : y2 --> (AddEquiv1 Trans x1)}
             (H1 : isDTri (mk_Tri f1 f2 f3)) (H2 : isDTri (mk_Tri g1 g2 g3))
             (H3 : isDTri (mk_Tri (f1 · g1) h2 h3)) :
    ∥ Octa H1 H2 H3 ∥.
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f1) (propproperty _)). intros f1'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A g1) (propproperty _)). intros g1'.
    set (f1'' := hfiberpr1 _ _ f1'). set (g1'' := hfiberpr1 _ _ g1').
    set (fg1' := hfiberpair (# (ComplexHomotFunctor A)) (f1'' · g1'')
                            (KATriangOcta_hfiber_comp_eq f1 g1 f1' g1')).
    set (H1' := KAFiberisDTri (Morphisms.mk_Morphism f1) f1').
    set (H2' := KAFiberisDTri (Morphisms.mk_Morphism g1) g1').
    set (H3' := KAFiberisDTri (Morphisms.mk_Morphism (f1 · g1)) fg1').
    use (squash_to_prop
           (DExt KAPreTriang (mk_DTri' _ H1)
                 (mk_DTri' _ (KAFiberisDTri (Morphisms.mk_Morphism f1) f1'))
                 (identity _) (identity _) (! (KAIdComm _ _ (idpath _))))
           (propproperty _)). intros Ext1.
    set (I1' := mk_TriIso
                  (TExtMor Ext1)
                  (@mk_TriMor_is_iso
                     KAPreTriang Trans _ _ (TExtMor Ext1) (is_z_isomorphism_identity _)
                     (is_z_isomorphism_identity _)
                     (TriangulatedFiveLemma (TExtMor Ext1) (is_z_isomorphism_identity _)
                                            (is_z_isomorphism_identity _)))).
    use (squash_to_prop
           (DExt KAPreTriang (mk_DTri' _ H2)
                 (mk_DTri' _ (KAFiberisDTri (Morphisms.mk_Morphism g1) g1'))
                 (identity _) (identity _) (! (KAIdComm _ _ (idpath _))))
           (propproperty _)). intros Ext2.
    set (I2' := mk_TriIso
                  (TExtMor Ext2)
                  (@mk_TriMor_is_iso
                     KAPreTriang Trans _ _  (TExtMor Ext2) (is_z_isomorphism_identity _)
                     (is_z_isomorphism_identity _)
                     (TriangulatedFiveLemma (TExtMor Ext2) (is_z_isomorphism_identity _)
                                            (is_z_isomorphism_identity _)))).
    use (squash_to_prop
           (DExt KAPreTriang (mk_DTri' _ H3)
                 (mk_DTri' _ (KAFiberisDTri (Morphisms.mk_Morphism (f1 · g1)) fg1'))
                 (identity _) (identity _) (! (KAIdComm _ _ (idpath _))))
           (propproperty _)). intros Ext3.
    set (I3' := mk_TriIso (TExtMor Ext3)
                          (@mk_TriMor_is_iso
                             KAPreTriang Trans _ _
                             (TExtMor Ext3) (is_z_isomorphism_identity _)
                             (is_z_isomorphism_identity _)
                             (TriangulatedFiveLemma (TExtMor Ext3) (is_z_isomorphism_identity _)
                                                    (is_z_isomorphism_identity _)))).
    use hinhpr.
    use (OctaIso H1 H2 H3 H1' H2' H3' I1' I2' I3' (idpath _) (idpath _) (idpath _)).
    clear I3' Ext3 I2' Ext2 I1' Ext1.
    use mk_Octa.
    - exact (# (ComplexHomotFunctor A) (KAOctaMor1 f1'' g1'')).
    - exact (# (ComplexHomotFunctor A) (KAOctaMor2 f1'' g1'')).
    - exact (hinhpr (KATriangOcta_KADTriData f1' g1')).
    - use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _))).
      apply maponpaths. exact (KAOctaMor1Comm f1'' g1'').
    - use (pathscomp0 (! (functor_comp (ComplexHomotFunctor A) _ _))).
      apply maponpaths. exact (KAOctaMor2Comm f1'' g1'').
    - use (pathscomp0 (KAOctaComm5' f1'' g1'')).
      apply cancel_postcomposition. exact (hfiberpr2 _ _ g1').
    - use (pathscomp0 (KAOctaComm4' f1'' g1'')).
      apply cancel_precomposition. apply maponpaths. exact (hfiberpr2 _ _ f1').
  Qed.

  Definition KATriang : Triang.
  Proof.
    use mk_Triang.
    - exact (@KAPreTriang A).
    - intros x1 x2 y1 y2 z1 z2 f1 f2 f3 g1 g2 g3 h2 h3 H1 H2 H3.
      exact(KATriangOcta H1 H2 H3).
  Defined.

End KATriangulated.