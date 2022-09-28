(*******************************************************************

 Limits in bicategories of structured categories

 We look at terminal objects, products, pullbacks, and
 Eilenberg-Moore objects

 Contents
 1. Limits of categories with a terminal objects
 2. Limits of categories with products
 3. Limits of categories with pullbacks
 4. Limits of categories with finite limits
 5. Limits of categories with initial objects
 6. Limits of categories with coproducts

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.CategoryTheory.limits.Examples.UnitCategoryLimits.
Require Import UniMath.CategoryTheory.limits.Examples.CategoryProductLimits.
Require Import UniMath.CategoryTheory.limits.Examples.IsoCommaLimits.
Require Import UniMath.CategoryTheory.limits.Examples.EilenbergMooreLimits.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.
Require Import UniMath.Bicategories.Limits.Examples.TotalBicategoryLimits.
Require Import UniMath.Bicategories.Limits.Examples.DispConstructionsLimits.
Require Import UniMath.Bicategories.Limits.Examples.SubbicatLimits.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInTotalBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.

(**
 1. Limits of categories with a terminal objects
 *)
Definition disp_bifinal_univ_cat_with_terminal_obj
  : disp_bifinal_obj disp_bicat_terminal_obj (_ ,, bifinal_cats).
Proof.
  use subbicat_disp_final.
  - exact terminal_unit_category.
  - intros C.
    apply functor_to_unit_preserves_terminal.
Defined.

Definition bifinal_obj_univ_cat_with_terminal_obj
  : bifinal_obj univ_cat_with_terminal_obj.
Proof.
  use subbicat_final.
  - exact (_ ,, bifinal_cats).
  - exact terminal_unit_category.
  - intros C.
    apply functor_to_unit_preserves_terminal.
Defined.

Definition disp_has_binprod_univ_cat_with_terminal_obj
  : disp_has_binprod disp_bicat_terminal_obj has_binprod_bicat_of_univ_cats.
Proof.
  use subbicat_disp_binprod.
  - exact (λ C₁ C₂, terminal_category_binproduct (pr22 C₁) (pr22 C₂)).
  - intros C₁ C₂.
    apply pr1_preserves_terminal.
  - intros C₁ C₂.
    apply pr2_preserves_terminal.
  - intros C₁ C₂ q.
    apply preserves_terminal_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition has_binprod_univ_cat_with_terminal_obj
  : has_binprod univ_cat_with_terminal_obj.
Proof.
  use subbicat_binprod.
  - exact has_binprod_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - exact (λ C₁ C₂, terminal_category_binproduct (pr22 C₁) (pr22 C₂)).
  - intros C₁ C₂.
    apply pr1_preserves_terminal.
  - intros C₁ C₂.
    apply pr2_preserves_terminal.
  - intros C₁ C₂ q.
    apply preserves_terminal_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition disp_has_pb_univ_cat_with_terminal_obj
  : disp_has_pb disp_bicat_terminal_obj has_pb_bicat_of_univ_cats.
Proof.
  use subbicat_disp_has_pb.
  - exact (λ C₁ C₂ C₃ F G,
           terminal_category_iso_comma
             _ _
             (pr12 F) (pr12 G)
             (pr22 C₁) (pr22 C₂)).
  - exact (λ C₁ C₂ C₃ F G,
           iso_comma_pr1_preserves_terminal
             _ _
             (pr12 F) (pr12 G)
             (pr22 C₁) (pr22 C₂)).
  - exact (λ C₁ C₂ C₃ F G,
           iso_comma_pr2_preserves_terminal
             _ _
             (pr12 F) (pr12 G)
             (pr22 C₁) (pr22 C₂)).
  - exact (λ C₁ C₂ C₃ F G q,
           iso_comma_ump1_preserves_terminal
             _ _
             (pr12 G)
             _ (pr12 (pb_cone_pr1 q))
             _ (pr12 (pb_cone_pr2 q))
             _).
Defined.

Definition has_pb_univ_cat_with_terminal_obj
  : has_pb univ_cat_with_terminal_obj.
Proof.
  use subbicat_has_pb.
  - exact has_pb_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - exact (λ C₁ C₂ C₃ F G,
           terminal_category_iso_comma
             _ _
             (pr12 F) (pr12 G)
             (pr22 C₁) (pr22 C₂)).
  - exact (λ C₁ C₂ C₃ F G,
           iso_comma_pr1_preserves_terminal
             _ _
             (pr12 F) (pr12 G)
             (pr22 C₁) (pr22 C₂)).
  - exact (λ C₁ C₂ C₃ F G,
           iso_comma_pr2_preserves_terminal
             _ _
             (pr12 F) (pr12 G)
             (pr22 C₁) (pr22 C₂)).
  - exact (λ C₁ C₂ C₃ F G q,
           iso_comma_ump1_preserves_terminal
             _ _
             (pr12 G)
             _ (pr12 (pb_cone_pr1 q))
             _ (pr12 (pb_cone_pr2 q))
             _).
Defined.

Definition has_em_univ_cat_with_terminal_obj
  : bicat_has_em univ_cat_with_terminal_obj.
Proof.
  use subbicat_has_em.
  - exact has_em_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - exact (λ m,
           terminal_eilenberg_moore_cat _ (pr22 (ob_of_mnd m))).
  - exact (λ m,
           eilenberg_moore_pr_preserves_terminal _ (pr22 (ob_of_mnd m))).
  - intros m q.
    use functor_to_eilenberg_moore_cat_preserves_terminal.
    exact (pr12 (mor_of_mnd_mor (mor_of_em_cone m q))).
Defined.

(**
 2. Limits of categories with products
 *)
Definition disp_bifinal_obj_univ_cat_with_binprod
  : disp_bifinal_obj disp_bicat_binprod (_ ,, bifinal_cats).
Proof.
  use subbicat_disp_final.
  - exact binproduct_unit_category.
  - intro.
    apply functor_to_unit_preserves_binproduct.
Defined.

Definition bifinal_obj_univ_cat_with_binprod
  : bifinal_obj univ_cat_with_binprod.
Proof.
  use subbicat_final.
  - exact (_ ,, bifinal_cats).
  - exact binproduct_unit_category.
  - intro.
    apply functor_to_unit_preserves_binproduct.
Defined.

Definition disp_has_binprod_univ_cat_with_binprod
  : disp_has_binprod disp_bicat_binprod has_binprod_bicat_of_univ_cats.
Proof.
  use subbicat_disp_binprod.
  - intros C₁ C₂.
    apply binproducts_in_product_category.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr1_preserves_binproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr2_preserves_binproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ q.
    apply preserves_binproduct_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition has_binprod_univ_cat_with_binprod
  : has_binprod univ_cat_with_binprod.
Proof.
  use subbicat_binprod.
  - exact has_binprod_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - intros C₁ C₂.
    apply binproducts_in_product_category.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr1_preserves_binproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr2_preserves_binproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ q.
    apply preserves_binproduct_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition disp_has_pb_univ_cat_with_binprod
  : disp_has_pb disp_bicat_binprod has_pb_bicat_of_univ_cats.
Proof.
  use subbicat_disp_has_pb.
  - intros C₁ C₂ C₃ F G.
    apply binproducts_in_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_binproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_binproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_binproduct.
    + exact (pr12 G).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_pb_univ_cat_with_binprod
  : has_pb univ_cat_with_binprod.
Proof.
  use subbicat_has_pb.
  - exact has_pb_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - intros C₁ C₂ C₃ F G.
    apply binproducts_in_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_binproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_binproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_binproduct.
    + exact (pr12 G).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_em_univ_cat_with_binprod
  : bicat_has_em univ_cat_with_binprod.
Proof.
  use subbicat_has_em.
  - exact has_em_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - exact (λ m,
           BinProducts_eilenberg_moore_cat _ (pr22 (ob_of_mnd m))).
  - exact (λ m,
           eilenberg_moore_pr_preserves_binproduct _ (pr22 (ob_of_mnd m))).
  - intros m q.
    use functor_to_eilenberg_moore_cat_preserves_binproduct.
    exact (pr12 (mor_of_mnd_mor (mor_of_em_cone m q))).
Defined.

(**
 3. Limits of categories with pullbacks
 *)
Definition disp_bifinal_obj_univ_cat_with_pb
  : disp_bifinal_obj disp_bicat_pullback (_ ,, bifinal_cats).
Proof.
  use subbicat_disp_final.
  - exact pullbacks_unit_category.
  - intro.
    apply functor_to_unit_preserves_pullback.
Defined.

Definition bifinal_obj_univ_cat_with_pb
  : bifinal_obj univ_cat_with_pb.
Proof.
  use subbicat_final.
  - exact (_ ,, bifinal_cats).
  - exact pullbacks_unit_category.
  - intro.
    apply functor_to_unit_preserves_pullback.
Defined.

Definition disp_has_binprod_univ_cat_with_pb
  : disp_has_binprod disp_bicat_pullback has_binprod_bicat_of_univ_cats.
Proof.
  use subbicat_disp_binprod.
  - intros C₁ C₂.
    apply pullbacks_in_product_category.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr1_preserves_pullback.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr2_preserves_pullback.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ q.
    apply preserves_pullback_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition has_binprod_univ_cat_with_pb
  : has_binprod univ_cat_with_pb.
Proof.
  use subbicat_binprod.
  - exact has_binprod_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - intros C₁ C₂.
    apply pullbacks_in_product_category.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr1_preserves_pullback.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr2_preserves_pullback.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ q.
    apply preserves_pullback_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition disp_has_pb_univ_cat_with_pb
  : disp_has_pb disp_bicat_pullback has_pb_bicat_of_univ_cats.
Proof.
  use subbicat_disp_has_pb.
  - intros C₁ C₂ C₃ F G.
    apply pullbacks_in_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_pullback.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_pullback.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_pullback.
    + exact (pr12 G).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_pb_univ_cat_with_pb
  : has_pb univ_cat_with_pb.
Proof.
  use subbicat_has_pb.
  - exact has_pb_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - intros C₁ C₂ C₃ F G.
    apply pullbacks_in_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_pullback.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_pullback.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_pullback.
    + exact (pr12 G).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_em_univ_cat_with_pb
  : bicat_has_em univ_cat_with_pb.
Proof.
  use subbicat_has_em.
  - exact has_em_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - exact (λ m,
           Pullbacks_eilenberg_moore _ (pr22 (ob_of_mnd m))).
  - exact (λ m,
           eilenberg_moore_pr_preserves_pullback _ (pr22 (ob_of_mnd m))).
  - intros m q.
    use functor_to_eilenberg_moore_cat_preserves_pullback.
    exact (pr12 (mor_of_mnd_mor (mor_of_em_cone m q))).
Defined.

(**
 4. Limits of categories with finite limits
 *)
Definition disp_bifinal_obj_univ_cat_with_finlim
  : disp_bifinal_obj disp_bicat_finlim (_ ,, bifinal_cats).
Proof.
  use disp_dirprod_bifinal.
  - exact disp_bifinal_univ_cat_with_terminal_obj.
  - exact disp_bifinal_obj_univ_cat_with_pb.
Defined.

Definition bifinal_obj_univ_cat_with_finlim
  : bifinal_obj univ_cat_with_finlim.
Proof.
  use total_bicat_final.
  - use disp_2cells_isaprop_prod.
    + apply disp_2cells_isaprop_subbicat.
    + apply disp_2cells_isaprop_subbicat.
  - intros.
    exact ((tt ,, tt) ,, (tt ,, tt)).
  - exact (_ ,, bifinal_cats).
  - exact disp_bifinal_obj_univ_cat_with_finlim.
Defined.

Definition disp_has_binprod_univ_cat_with_finlim
  : disp_has_binprod disp_bicat_finlim has_binprod_bicat_of_univ_cats.
Proof.
  use disp_dirprod_binprod.
  - exact disp_has_binprod_univ_cat_with_terminal_obj.
  - exact disp_has_binprod_univ_cat_with_pb.
Defined.

Definition has_binprod_univ_cat_with_finlim
  : has_binprod univ_cat_with_finlim.
Proof.
  use total_bicat_prod.
  - use disp_2cells_isaprop_prod.
    + apply disp_2cells_isaprop_subbicat.
    + apply disp_2cells_isaprop_subbicat.
  - intros.
    exact ((tt ,, tt) ,, (tt ,, tt)).
  - apply disp_locally_groupoid_prod.
    + apply disp_locally_groupoid_subbicat.
      apply univalent_cat_is_univalent_2.
    + apply disp_locally_groupoid_subbicat.
      apply univalent_cat_is_univalent_2.
  - exact has_binprod_bicat_of_univ_cats.
  - exact disp_has_binprod_univ_cat_with_finlim.
Defined.

Definition disp_has_pb_univ_cat_with_finlim
  : disp_has_pb disp_bicat_finlim has_pb_bicat_of_univ_cats.
Proof.
  use disp_dirprod_pb.
  - exact disp_has_pb_univ_cat_with_terminal_obj.
  - exact disp_has_pb_univ_cat_with_pb.
Defined.

Definition has_pb_univ_cat_with_finlim
  : has_pb univ_cat_with_finlim.
Proof.
  use total_bicat_has_pb.
  - use disp_2cells_isaprop_prod.
    + apply disp_2cells_isaprop_subbicat.
    + apply disp_2cells_isaprop_subbicat.
  - intros.
    exact ((tt ,, tt) ,, (tt ,, tt)).
  - apply disp_locally_groupoid_prod.
    + apply disp_locally_groupoid_subbicat.
      apply univalent_cat_is_univalent_2.
    + apply disp_locally_groupoid_subbicat.
      apply univalent_cat_is_univalent_2.
  - exact has_pb_bicat_of_univ_cats.
  - exact disp_has_pb_univ_cat_with_finlim.
Defined.

(**
 5. Limits of categories with initial objects
 *)
Definition disp_bifinal_obj_univ_cat_with_initial
  : disp_bifinal_obj disp_bicat_initial_obj (_ ,, bifinal_cats).
Proof.
  use subbicat_disp_final.
  - exact initial_unit_category.
  - intro C.
    apply functor_to_unit_preserves_initial.
Defined.

Definition bifinal_obj_univ_cat_with_initial
  : bifinal_obj univ_cat_with_initial.
Proof.
  use subbicat_final.
  - exact (_ ,, bifinal_cats).
  - exact initial_unit_category.
  - intro C.
    apply functor_to_unit_preserves_initial.
Defined.

Definition disp_has_binprod_univ_cat_with_initial
  : disp_has_binprod disp_bicat_initial_obj has_binprod_bicat_of_univ_cats.
Proof.
  use subbicat_disp_binprod.
  - exact (λ C₁ C₂, initial_category_binproduct (pr22 C₁) (pr22 C₂)).
  - intros C₁ C₂.
    apply pr1_preserves_initial.
  - intros C₁ C₂.
    apply pr2_preserves_initial.
  - intros C₁ C₂ q.
    apply preserves_initial_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition has_binprod_univ_cat_with_initial
  : has_binprod univ_cat_with_initial.
Proof.
  use subbicat_binprod.
  - exact has_binprod_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - exact (λ C₁ C₂, initial_category_binproduct (pr22 C₁) (pr22 C₂)).
  - intros C₁ C₂.
    apply pr1_preserves_initial.
  - intros C₁ C₂.
    apply pr2_preserves_initial.
  - intros C₁ C₂ q.
    apply preserves_initial_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition disp_has_pb_univ_cat_with_initial
  : disp_has_pb disp_bicat_initial_obj has_pb_bicat_of_univ_cats.
Proof.
  use subbicat_disp_has_pb.
  - intros C₁ C₂ C₃ F G.
    apply initial_category_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_initial.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_initial.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_initial.
    + exact (pr12 F).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_pb_univ_cat_with_initial
  : has_pb univ_cat_with_initial.
Proof.
  use subbicat_has_pb.
  - exact has_pb_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - intros C₁ C₂ C₃ F G.
    apply initial_category_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_initial.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_initial.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_initial.
    + exact (pr12 F).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_em_univ_cat_with_initial
  : bicat_has_em univ_cat_with_initial.
Proof.
  use subbicat_has_em.
  - exact has_em_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - refine (λ m,
            initial_eilenberg_moore_cat
              _
              (pr22 (ob_of_mnd m))
              _).
    exact (pr12 (endo_of_mnd m)).
  - refine (λ m,
            eilenberg_moore_pr_preserves_initial _ (pr22 (ob_of_mnd m)) _).
    exact (pr12 (endo_of_mnd m)).
  - intros m q.
    use functor_to_eilenberg_moore_cat_preserves_initial.
    + exact (pr12 (endo_of_mnd m)).
    + exact (pr12 (mor_of_mnd_mor (mor_of_em_cone m q))).
Defined.

(**
 6. Limits of categories with coproducts
 *)
Definition disp_bifinal_obj_univ_cat_with_bincoprod
  : disp_bifinal_obj disp_bicat_bincoprod (_ ,, bifinal_cats).
Proof.
  use subbicat_disp_final.
  - exact bincoproduct_unit_category.
  - intro C.
    apply functor_to_unit_preserves_bincoproduct.
Defined.

Definition bifinal_obj_univ_cat_with_bincoprod
  : bifinal_obj univ_cat_with_bincoprod.
Proof.
  use subbicat_final.
  - exact (_ ,, bifinal_cats).
  - exact bincoproduct_unit_category.
  - intro C.
    apply functor_to_unit_preserves_bincoproduct.
Defined.

Definition disp_has_binprod_univ_cat_with_bincoprod
  : disp_has_binprod disp_bicat_bincoprod has_binprod_bicat_of_univ_cats.
Proof.
  use subbicat_disp_binprod.
  - intros C₁ C₂.
    apply bincoproducts_in_product_category.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr1_preserves_bincoproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr2_preserves_bincoproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ q.
    apply preserves_bincoproduct_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition has_binprod_univ_cat_with_bincoprod
  : has_binprod univ_cat_with_bincoprod.
Proof.
  use subbicat_binprod.
  - exact has_binprod_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - intros C₁ C₂.
    apply bincoproducts_in_product_category.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr1_preserves_bincoproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂.
    apply pr2_preserves_bincoproduct.
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ q.
    apply preserves_bincoproduct_bindelta_pair_functor.
    + exact (pr12 (binprod_cone_pr1 q)).
    + exact (pr12 (binprod_cone_pr2 q)).
Defined.

Definition disp_has_pb_univ_cat_with_bincoprod
  : disp_has_pb disp_bicat_bincoprod has_pb_bicat_of_univ_cats.
Proof.
  use subbicat_disp_has_pb.
  - intros C₁ C₂ C₃ F G.
    apply bincoproducts_in_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_bincoproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_bincoproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_bincoproduct.
    + exact (pr12 F).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_pb_univ_cat_with_bincoprod
  : has_pb univ_cat_with_bincoprod.
Proof.
  use subbicat_has_pb.
  - exact has_pb_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - intros C₁ C₂ C₃ F G.
    apply bincoproducts_in_iso_comma.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr1_preserves_bincoproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G.
    apply iso_comma_pr2_preserves_bincoproduct.
    + exact (pr12 F).
    + exact (pr12 G).
    + exact (pr22 C₁).
    + exact (pr22 C₂).
  - intros C₁ C₂ C₃ F G q.
    apply iso_comma_ump1_preserves_bincoproduct.
    + exact (pr12 F).
    + exact (pr12 (pb_cone_pr1 q)).
    + exact (pr12 (pb_cone_pr2 q)).
Defined.

Definition has_em_univ_cat_with_bincoprod
  : bicat_has_em univ_cat_with_bincoprod.
Proof.
  use subbicat_has_em.
  - exact has_em_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2.
  - refine (λ m,
            bincoproducts_eilenberg_moore
              _
              (pr22 (ob_of_mnd m))
              _).
    exact (pr12 (endo_of_mnd m)).
  - refine (λ m,
            eilenberg_moore_pr_preserves_bincoproduct _ (pr22 (ob_of_mnd m)) _).
    exact (pr12 (endo_of_mnd m)).
  - intros m q.
    use functor_to_eilenberg_moore_cat_preserves_bincoproduct.
    + exact (pr12 (endo_of_mnd m)).
    + exact (pr12 (mor_of_mnd_mor (mor_of_em_cone m q))).
Defined.
