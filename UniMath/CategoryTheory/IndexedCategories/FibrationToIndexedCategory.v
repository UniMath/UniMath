(************************************************************************

 Every fibration gives rise to an indexed category

 In this file, we prove that every fibration gives rise to an indexed
 category. This construction makes use of the fiber of a displayed
 category. The pseudofunctoriality of the fiber follows from the fact
 that we have a cleaving. Note that all relevant constructions for this
 file are already given in the directory on displayed categories, and
 here, they are only collected. Compared to that directory, the only new
 thing is that we prove the laws of indexed categories.

 Contents
 1. The data
 2. The laws
 3. The identitor and compositor are natural isos
 4. The indexed category from a fibration

 ************************************************************************)
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
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.

Section FibrationToIndexedCat.
  Context {C : category}
          (D : disp_univalent_category C)
          (HD : cleaving D).

  (**
   1. The data
   *)
  Definition cleaving_to_indexed_cat_data
    : indexed_cat_data (C^opp).
  Proof.
    use make_indexed_cat_data.
    - exact (λ x, univalent_fiber_category D x).
    - exact (λ x y f, fiber_functor_from_cleaving D HD f).
    - exact (λ x, fiber_functor_from_cleaving_identity HD x).
    - exact (λ x y z f g, fiber_functor_from_cleaving_comp HD f g).
  Defined.

  (**
   2. The laws
   *)
  Proposition cleaving_to_indexed_cat_laws
    : indexed_cat_laws cleaving_to_indexed_cat_data.
  Proof.
    repeat split.
    - intros x y f xx ; cbn.
      use (cartesian_factorisation_unique (HD _ _ _ _)).
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite id_left_disp.
      refine (!_).
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply idtoiso_fiber_category.
        }
        apply idtoiso_disp_cartesian_lift.
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
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
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros x y f xx ; cbn.
      use (cartesian_factorisation_unique (HD _ _ _ _)).
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite id_left_disp.
      refine (!_).
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply idtoiso_fiber_category.
        }
        apply idtoiso_disp_cartesian_lift.
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite id_left_disp.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros w x y z f g h ww ; cbn.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      use (cartesian_factorisation_unique (HD _ _ _ _)).
      rewrite assoc_disp_var.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      etrans.
      {
        do 3 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply idtoiso_fiber_category.
        }
        apply idtoiso_disp_cartesian_lift.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      refine (!_).
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  (**
   3. The identitor and compositor are natural isos
   *)
  Definition cleaving_to_indexed_cat_isos
    : indexed_cat_isos cleaving_to_indexed_cat_data.
  Proof.
    split.
    - intros x xx ; cbn.
      apply is_nat_z_iso_fiber_functor_from_cleaving_identity.
    - intros x y z f g xx ; cbn.
      apply is_nat_z_iso_fiber_functor_from_cleaving_comp.
  Defined.

  (**
   4. The indexed category from a fibration
   *)
  Definition cleaving_to_indexed_cat
    : indexed_cat (C^opp).
  Proof.
    use make_indexed_cat.
    - exact cleaving_to_indexed_cat_data.
    - exact cleaving_to_indexed_cat_isos.
    - exact cleaving_to_indexed_cat_laws.
  Defined.
End FibrationToIndexedCat.
