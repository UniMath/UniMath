(****************************************************************

 In this file, we combine the facts from `precomp_ess_surj.v`
 and `precomp_fully_faithful.v`. We show that if we have a fully
 faithful and essential surjective functor `F : C₁ ⟶ C₂` and a
 univalent category `D`, then we have an adjoint equivalence
 between `[ C₂ , D ]` and `[ C₁ , D ]` (the functor is given
 by precomposition). We also give some functions to use this
 adjoint equivalence.

 ****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.precomp_ess_surj.
Require Import UniMath.CategoryTheory.precomp_fully_faithful.

Local Open Scope cat.

Section PrecompEquivalence.
  Context {C₁ C₂ : category}
          (D : univalent_category)
          (F : C₁ ⟶ C₂)
          (HF₁ : essentially_surjective F)
          (HF₂ : fully_faithful F).

  Definition precomp_adjoint_equivalence
    : adj_equivalence_of_cats (pre_composition_functor C₁ C₂ (pr1 D) F).
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_functor_category.
      exact (pr2 D).
    - exact (pre_composition_with_ess_surj_and_fully_faithful_is_fully_faithful
               C₁ C₂ D
               F
               HF₁ HF₂).
    - exact (pre_composition_essentially_surjective
               C₁ C₂ D (pr2 D)
               F
               HF₁ HF₂).
  Defined.

  Let L : [ C₂ , D ] ⟶ [ C₁ , D ]
    := pre_composition_functor C₁ C₂ (pr1 D) F.
  Let R : [ C₁ , D ] ⟶ [ C₂ , D ]
    := right_adjoint precomp_adjoint_equivalence.
  Let ε : nat_z_iso (R ∙ L) (functor_identity _)
    := counit_nat_z_iso_from_adj_equivalence_of_cats
         precomp_adjoint_equivalence.
  Let η : nat_z_iso (functor_identity _) (L ∙ R)
    := unit_nat_z_iso_from_adj_equivalence_of_cats
         precomp_adjoint_equivalence.

  Definition lift_functor_along
             (G : C₁ ⟶ D)
    : C₂ ⟶ D
    := R G.

  Definition lift_functor_along_comm
             (G : C₁ ⟶ D)
    : nat_z_iso (F ∙ lift_functor_along G) G
    := nat_z_iso_from_z_iso _ (nat_z_iso_pointwise_z_iso ε G).

  Definition lift_nat_trans_along
             {G₁ G₂ : C₂ ⟶ D}
             (α : F ∙ G₁ ⟹ F ∙ G₂)
    : G₁ ⟹ G₂.
  Proof.
    exact (invmap
             (make_weq
                _
                (fully_faithful_from_equivalence
                   _ _ _
                   precomp_adjoint_equivalence
                   G₁ G₂))
          α).
  Defined.

  Definition lift_nat_trans_along_comm
             {G₁ G₂ : C₂ ⟶ D}
             (α : F ∙ G₁ ⟹ F ∙ G₂)
    : pre_whisker F (lift_nat_trans_along α) = α.
  Proof.
    exact (homotweqinvweq
             (make_weq
                _
                (fully_faithful_from_equivalence
                   _ _ _
                   precomp_adjoint_equivalence
                   G₁ G₂))
             α).
  Qed.

  Definition lift_nat_trans_eq_along
             {G₁ G₂ : C₂ ⟶ D}
             {β₁ β₂ : G₁ ⟹ G₂}
             (p : pre_whisker F β₁ = pre_whisker F β₂)
    : β₁ = β₂.
  Proof.
    exact (maponpaths
             pr1
             (proofirrelevance
                _
                (pr2 (fully_faithful_implies_full_and_faithful
                        _ _ _
                        (fully_faithful_from_equivalence
                           _ _ _
                           precomp_adjoint_equivalence))
                   G₁ G₂
                   (pre_whisker F β₂))
                (β₁ ,, p)
                (β₂ ,, idpath _))).
  Qed.
End PrecompEquivalence.
