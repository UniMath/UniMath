(** copies the final object and the inserters from the treatment of the bicategory of univalent categories *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.CommaCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.CommaObjects.
Require Import UniMath.Bicategories.Limits.Inserters.
Require Import UniMath.Bicategories.Limits.Equifiers.

Local Open Scope cat.

(**
 1. Final object
 *)
Definition bifinal_cats
  : @is_bifinal bicat_of_cats (pr1 unit_category).
Proof.
  use make_is_bifinal.
  - exact (λ C, functor_to_unit (pr1 C)).
  - exact (λ C F G, unit_category_nat_trans F G).
  - intros Y f g α β.
    apply nat_trans_to_unit_eq.
Defined.


(**
 6. Inserters
 *)
Definition dialgebra_inserter_cone
           {C₁ C₂ : bicat_of_cats}
           (F G : C₁ --> C₂)
  : inserter_cone F G.
Proof.
  use make_inserter_cone.
  - exact (dialgebra F G).
  - exact (dialgebra_pr1 F G).
  - exact (dialgebra_nat_trans F G).
Defined.

Definition dialgebra_inserter_ump_1
           {C₁ C₂ : bicat_of_cats}
           (F G : C₁ --> C₂)
  : has_inserter_ump_1 (dialgebra_inserter_cone F G).
Proof.
  intros q.
  use make_inserter_1cell.
  - exact (nat_trans_to_dialgebra
             (inserter_cone_pr1 q)
             (inserter_cone_cell q)).
  - use nat_z_iso_to_invertible_2cell.
    exact (nat_trans_to_dialgebra_pr1_nat_z_iso
             (inserter_cone_pr1 q)
             (inserter_cone_cell q)).
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       rewrite !(functor_id F), !(functor_id G) ;
       rewrite !id_left, !id_right ;
       apply idpath).
Defined.

Definition dialgebra_inserter_ump_2
           {C₁ C₂ : bicat_of_cats}
           (F G : C₁ --> C₂)
  : has_inserter_ump_2 (dialgebra_inserter_cone F G).
Proof.
  intros C₀ K₁ K₂ α p.
  simple refine (_ ,, _).
  - apply (build_nat_trans_to_dialgebra K₁ K₂ α).
    abstract
      (intro x ;
       pose (nat_trans_eq_pointwise p x) as p' ;
       cbn in p' ;
       rewrite !id_left, !id_right in p' ;
       exact p').
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       apply idpath).
Defined.

Definition dialgebra_inserter_ump_eq
           {C₁ C₂ : bicat_of_cats}
           (F G : C₁ --> C₂)
  : has_inserter_ump_eq (dialgebra_inserter_cone F G).
Proof.
  intros C₀ K₁ K₂ α p n₁ n₂ q₁ q₂.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x.
  use eq_dialgebra.
  exact (nat_trans_eq_pointwise q₁ x @ !(nat_trans_eq_pointwise q₂ x)).
Qed.

Definition has_inserters_bicat_of_cats
  : has_inserters bicat_of_cats.
Proof.
  intros C₁ C₂ F G.
  simple refine (dialgebra F G ,, _ ,, _ ,, _).
  - exact (dialgebra_pr1 F G).
  - exact (dialgebra_nat_trans F G).
  - refine (_ ,, _ ,, _).
    + exact (dialgebra_inserter_ump_1 F G).
    + exact (dialgebra_inserter_ump_2 F G).
    + exact (dialgebra_inserter_ump_eq F G).
Defined.
