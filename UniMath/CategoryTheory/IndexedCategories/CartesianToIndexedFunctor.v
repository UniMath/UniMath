(************************************************************************

 Every cartesian functor gives rise to an indexed functor

 In this file, we prove that every cartesian functor between two
 fibrations gives rise to an indexed functor between the corresponding
 indexed categories. The main idea behind this construction is that every
 displayed functor gives rise to a fiber functor between the fibers. The
 data for this construction is already given in the directory on
 displayed categories, and the only thing that is added here, is a proof
 of the laws of an indexed functor.

 Contents
 1. The data
 2. The laws
 3. The indexed functor from a cartesian functor

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.FibrationToIndexedCategory.

Local Open Scope cat.

Section CartesianFunctorToIndexedFunctor.
  Context {C : category}
          {D₁ D₂ : disp_univalent_category C}
          (HD₁ : cleaving D₁)
          (HD₂ : cleaving D₂)
          (F : cartesian_disp_functor (functor_identity C) D₁ D₂).

  (**
   1. The data
   *)
  Definition cartesian_disp_functor_to_indexed_functor_data
    : indexed_functor_data
        (cleaving_to_indexed_cat D₁ HD₁)
        (cleaving_to_indexed_cat D₂ HD₂).
  Proof.
    use make_indexed_functor_data.
    - exact (fiber_functor F).
    - exact (λ x y f, fiber_functor_natural_nat_z_iso HD₁ HD₂ F f).
  Defined.

  (**
   2. The laws
   *)
  Proposition cartesian_disp_functor_to_indexed_functor_laws
    : indexed_functor_laws
        cartesian_disp_functor_to_indexed_functor_data.
  Proof.
    split.
    - intros x xx ; cbn.
      use (cartesian_factorisation_unique
             (cartesian_disp_functor_on_cartesian F (HD₁ _ _ _ _))).
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        refine (!_).
        apply (disp_functor_comp_var F).
      }
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_transportf.
      rewrite transport_f_f.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros x y z f g xx ; cbn.
      rewrite mor_disp_transportf_postwhisker.
      use (cartesian_factorisation_unique
             (cartesian_disp_functor_on_cartesian F (HD₁ _ _ _ _))).
      rewrite !mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite transport_f_f.
      refine (!_).
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        apply (disp_functor_comp_var F).
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite disp_functor_transportf.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc_disp.
        apply idpath.
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  (**
   3. The indexed functor from a cartesian functor
   *)
  Definition cartesian_disp_functor_to_indexed_functor
    : indexed_functor
        (cleaving_to_indexed_cat D₁ HD₁)
        (cleaving_to_indexed_cat D₂ HD₂).
  Proof.
    use make_indexed_functor.
    - exact cartesian_disp_functor_to_indexed_functor_data.
    - exact cartesian_disp_functor_to_indexed_functor_laws.
  Defined.
End CartesianFunctorToIndexedFunctor.
