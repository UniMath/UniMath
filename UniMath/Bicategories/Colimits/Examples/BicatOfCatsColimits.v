(********************************************************************

 Colimits in the bicategory of categories

 Contents
 1. Kleisli objects

 ********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInBicatOfCats.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInOp1Bicat.
Require Import UniMath.Bicategories.Colimits.KleisliObjects.

Local Open Scope cat.

(**
 1. Kleisli objects
 *)
Section KleisliCategoryUMP.
  Context (m : mnd (op1_bicat bicat_of_cats)).

  Let C : category := ob_of_mnd m.
  Let M : Monad C := mnd_bicat_of_cats_to_Monad (mnd_op1_to_mnd m).

  Definition bicat_of_cats_has_kleisli_cocone
    : kleisli_cocone m.
  Proof.
    use make_kleisli_cocone.
    - exact (Kleisli_cat_monad M).
    - exact (Left_Kleisli_functor M).
    - exact (kleisli_monad_nat_trans M).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ; cbn ;
         intro x ;
         exact (η_η_bind M x)).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ; cbn ;
         intro x ;
         exact (η_bind_bind M x)).
  Defined.

  Definition bicat_of_cats_has_kleisli_ump_1
    : has_kleisli_ump_1 m bicat_of_cats_has_kleisli_cocone.
  Proof.
    intro q.
    pose (F := mor_of_kleisli_cocone _ q).
    pose (γ := cell_of_kleisli_cocone _ q).
    pose (p₁ := nat_trans_eq_pointwise (kleisli_cocone_unit _ q)).
    assert (p₂ : ∏ (x : C), pr1 γ (M x) · pr1 γ x = # (pr1 F) (μ M x) · pr1 γ x).
    {
      intro x.
      pose (p₂ := nat_trans_eq_pointwise (kleisli_cocone_mult _ q) x).
      cbn in p₂.
      rewrite !id_left in p₂.
      exact p₂.
    }
    use make_kleisli_cocone_mor.
    - exact (functor_from_kleisli_cat_monad M F γ p₁ p₂).
    - exact (functor_from_kleisli_cat_monad_nat_trans M F γ p₁ p₂).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         rewrite functor_id ;
         rewrite !id_left, id_right ;
         apply idpath).
    - use is_nat_z_iso_to_is_invertible_2cell.
      intro.
      apply is_z_isomorphism_identity.
  Defined.

  Definition bicat_of_cats_has_kleisli_ump_2
    : has_kleisli_ump_2 m bicat_of_cats_has_kleisli_cocone.
  Proof.
    intros C' G₁ G₂ α p.
    assert (p' : ∏ (x : C),
                 # (pr1 G₁) (kleisli_monad_nat_trans M x) · pr1 α x
                 =
                 pr1 α (M x) · # (pr1 G₂) (kleisli_monad_nat_trans M x)).
    {
      intro x.
      pose (q := nat_trans_eq_pointwise p x).
      cbn in q.
      rewrite !id_left, !id_right in q.
      exact q.
    }
    use iscontraprop1.
    - use invproofirrelevance.
      intros β₁ β₂.
      use subtypePath ; [ intro ; apply cellset_property | ].
      exact (nat_trans_from_kleisli_cat_monad_unique M α (pr2 β₁) (pr2 β₂)).
    - simple refine (_ ,, _).
      + exact (nat_trans_from_kleisli_cat_monad M α p').
      + exact (pre_whisker_nat_trans_from_kleisli_cat_monad M α p').
  Defined.
End KleisliCategoryUMP.

Definition bicat_of_cats_has_kleisli
  : has_kleisli bicat_of_cats.
Proof.
  intro m.
  simple refine (_ ,, _ ,, _).
  - exact (bicat_of_cats_has_kleisli_cocone m).
  - exact (bicat_of_cats_has_kleisli_ump_1 m).
  - exact (bicat_of_cats_has_kleisli_ump_2 m).
Defined.
