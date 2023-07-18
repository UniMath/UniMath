(*************************************************************************

 Indexed functors give rise to cartesian functors

 We show that every indexed functor between indexed categories give rise
 to a cartesian functor between their corresponding fibrations. We first
 construct the displayed functor ([indexed_functor_to_disp_functor]), and
 to prove it preserves cartesian morphisms, we use the characterization of
 cartesian morphisms in the Grothendieck construction.

 Contents
 1. The displayed functor arising from an indexed functor
 2. Preservation of cartesian morphisms

 *************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedFunctor.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategoryToFibration.

Local Open Scope cat.

Section IndexedFunctorToCartesianFunctor.
  Context {C : category}
          {Φ Ψ : indexed_cat (C^opp)}
          (τ : indexed_functor Φ Ψ).

  (**
   1. The displayed functor arising from an indexed functor
   *)
  Definition indexed_functor_to_disp_functor_data
    : disp_functor_data
        (functor_identity C)
        (indexed_cat_to_disp_cat Φ)
        (indexed_cat_to_disp_cat Ψ).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, τ x).
    - exact (λ x y xx yy f ff,
             #(τ x) ff
             · inv_from_z_iso (indexed_functor_natural_z_iso τ f yy)).
  Defined.

  Proposition indexed_functor_to_disp_functor_axioms
    : disp_functor_axioms indexed_functor_to_disp_functor_data.
  Proof.
    split.
    - intros x xx ; cbn in *.
      etrans.
      {
        apply maponpaths_2.
        exact (!(indexed_functor_id τ xx)).
      }
      refine (!_).
      use z_iso_inv_on_left.
      apply idpath.
    - intros x y z xx yy zz f g ff gg ; cbn in *.
      refine (!_).
      use z_iso_inv_on_left.
      rewrite !functor_comp.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      use z_iso_inv_on_right.
      etrans.
      {
        do 2 apply maponpaths.
        exact (indexed_functor_comp τ g f zz).
      }
      cbn.
      rewrite !assoc.
      apply maponpaths_2.
      refine (_ @ nat_trans_ax (indexed_functor_natural τ f) _ _ _).
      apply maponpaths_2.
      cbn.
      rewrite <- !functor_comp.
      apply maponpaths.
      rewrite !assoc'.
      rewrite z_iso_after_z_iso_inv.
      apply id_right.
  Qed.

  Definition indexed_functor_to_disp_functor
    : disp_functor
        (functor_identity C)
        (indexed_cat_to_disp_cat Φ)
        (indexed_cat_to_disp_cat Ψ).
  Proof.
    simple refine (_ ,, _).
    - exact indexed_functor_to_disp_functor_data.
    - exact indexed_functor_to_disp_functor_axioms.
  Defined.

  (**
   2. Preservation of cartesian morphisms
   *)
  Definition is_cartesian_indexed_functor_to_disp_functor
    : is_cartesian_disp_functor indexed_functor_to_disp_functor.
  Proof.
    intros x y f xx yy ff Hff ; cbn in *.
    apply is_cartesian_indexed_cat.
    use is_z_iso_comp_of_is_z_isos.
    - use functor_on_is_z_isomorphism.
      exact (is_cartesian_to_iso_indexed_cat Φ ff Hff).
    - apply is_z_isomorphism_inv.
  Defined.

  Definition indexed_functor_to_cartesian_disp_functor
    : cartesian_disp_functor
        (functor_identity _)
        (indexed_cat_to_disp_cat Φ)
        (indexed_cat_to_disp_cat Ψ).
  Proof.
    simple refine (_ ,, _).
    - exact indexed_functor_to_disp_functor.
    - exact is_cartesian_indexed_functor_to_disp_functor.
  Defined.
End IndexedFunctorToCartesianFunctor.
