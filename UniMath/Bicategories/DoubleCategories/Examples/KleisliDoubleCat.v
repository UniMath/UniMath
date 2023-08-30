(**********************************************************************************

 The Kleisli double category

 Let `C` be a category and let `M` be a monad on `C`. Then we can define the
 following double category:
 - Objects: objects of `C`
 - Vertical morphisms: morphisms of `C`
 - Horizontal morphisms: Kleisli morphisms
 - Squares: commuting squares

 Contents
 1. Horizontal operations
 2. The Kleisli double category

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Comma.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCats.

Local Open Scope cat.

(**
 1. Horizontal operations
 *)
Section Kleisli.
  Context {C : univalent_category}
          (M : Monad C).

  Let K : twosided_disp_cat C C := comma_twosided_disp_cat (functor_identity C) M.

  Definition hor_id_data_kleisli
    : hor_id_data K.
  Proof.
    use make_hor_id_data ; cbn.
    - exact (λ x, η M x).
    - abstract
        (intros x y f ; cbn ;
         exact (nat_trans_ax (η M) _ _ f)).
  Defined.

  Proposition hor_id_laws_kleisli
    : hor_id_laws hor_id_data_kleisli.
  Proof.
    repeat split ; intros.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition hor_id_kleisli
    : hor_id K.
  Proof.
    use make_hor_id.
    - exact hor_id_data_kleisli.
    - exact hor_id_laws_kleisli.
  Defined.

  Definition hor_comp_data_kleisli
    : hor_comp_data K.
  Proof.
    use make_hor_comp_data.
    - exact (λ x y z f g, f · #M g · μ M z).
    - abstract
        (intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn in * ;
         rewrite !assoc ;
         rewrite s₁ ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite !assoc ;
         rewrite <- functor_comp ;
         rewrite s₂ ;
         rewrite functor_comp ;
         rewrite !assoc' ;
         apply maponpaths ;
         exact (nat_trans_ax (μ M) _ _ v₃)).
  Defined.

  Definition hor_comp_laws_kleisli
    : hor_comp_laws hor_comp_data_kleisli.
  Proof.
    repeat split ; intros.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition hor_comp_kleisli
    : hor_comp K.
  Proof.
    use make_hor_comp.
    - exact hor_comp_data_kleisli.
    - exact hor_comp_laws_kleisli.
  Defined.

  Definition double_cat_lunitor_kleisli
    : double_cat_lunitor
        hor_id_kleisli
        hor_comp_kleisli.
  Proof.
    use make_double_lunitor.
    - intros x y f ; cbn.
      use make_iso_twosided_disp.
      + cbn.
        rewrite id_left.
        rewrite functor_id.
        rewrite id_right.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(nat_trans_ax (η M) _ _ f)).
        }
        cbn.
        rewrite !assoc'.
        refine (_ @ id_right _).
        apply maponpaths.
        apply Monad_law1.
      + apply comma_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition double_cat_runitor_kleisli
    : double_cat_runitor
        hor_id_kleisli
        hor_comp_kleisli.
  Proof.
    use make_double_runitor.
    - intros x y f ; cbn.
      use make_iso_twosided_disp.
      + cbn.
        rewrite id_left.
        rewrite functor_id.
        rewrite id_right.
        refine (!_).
        rewrite !assoc'.
        refine (_ @ id_right _).
        apply maponpaths.
        apply Monad_law2.
      + apply comma_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition double_cat_associator_kleisli
    : double_cat_associator hor_comp_kleisli.
  Proof.
    use make_double_associator.
    - intros w x y z h₁ h₂ h₃ ; cbn.
      use make_iso_twosided_disp.
      + cbn.
        rewrite id_left.
        rewrite functor_id.
        rewrite id_right.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !functor_comp.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (!(nat_trans_ax (μ M) _ _ h₃)).
        }
        cbn.
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        apply Monad_law3.
      + apply comma_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  (**
   2. The Kleisli double category
   *)
  Definition kleisli_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact C.
    - exact K.
    - exact hor_id_kleisli.
    - exact hor_comp_kleisli.
    - exact double_cat_lunitor_kleisli.
    - exact double_cat_runitor_kleisli.
    - exact double_cat_associator_kleisli.
    - abstract (intro ; intros ; apply homset_property).
    - abstract (intro ; intros ; apply homset_property).
    - apply univalent_category_is_univalent.
    - apply is_univalent_comma_twosided_disp_cat.
  Defined.
End Kleisli.
