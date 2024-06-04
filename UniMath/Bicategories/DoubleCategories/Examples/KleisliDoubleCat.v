(**********************************************************************************

 The Kleisli double category

 Let `C` be a category and let `M` be a monad on `C`. Then we can define the
 following double category:
 - Objects: objects of `C`
 - Vertical morphisms: morphisms of `C`
 - Horizontal morphisms: Kleisli morphisms
 - Squares: commuting squares
 We give both a univalent and a strict variant.

 Contents
 1. Horizontal operations
 2. The Kleisli double category
 3. The strict Kleisli double category

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Comma.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.StrictDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.

(** * 1. Horizontal operations *)
Section Kleisli.
  Context {C : category}
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
End Kleisli.

(** * 2. The Kleisli double category *)
Definition kleisli_double_cat
           {C : category}
           (M : Monad C)
  : double_cat.
Proof.
  use make_double_cat.
  - exact C.
  - exact (comma_twosided_disp_cat (functor_identity C) M).
  - exact (hor_id_kleisli M).
  - exact (hor_comp_kleisli M).
  - exact (double_cat_lunitor_kleisli M).
  - exact (double_cat_runitor_kleisli M).
  - exact (double_cat_associator_kleisli M).
  - abstract (intro ; intros ; apply homset_property).
  - abstract (intro ; intros ; apply homset_property).
Defined.

Definition all_companions_kleisli_double_cat
           {C : category}
           (M : Monad C)
  : all_companions_double_cat (kleisli_double_cat M).
Proof.
  intros x y f ; cbn in x, y, f ; cbn.
  refine (f · η M _ ,, _).
  use make_double_cat_are_companions.
  - abstract
      (cbn ;
       refine (!_) ;
       etrans ;
       [ apply maponpaths ;
         apply functor_id
       | ] ;
       rewrite id_right ;
       apply idpath).
  - abstract
      (cbn ;
       rewrite id_left ;
       exact (nat_trans_ax (η M) _ _ f)).
  - apply homset_property.
  - apply homset_property.
Defined.

Definition kleisli_double_cat_ver_weq_square
           {C : category}
           (M : Monad C)
           (H : ∏ (x : C), isMonic (η M x))
  : ver_weq_square (kleisli_double_cat M).
Proof.
  intros x y f g.
  use isweqimplimpl.
  - intros p ; cbn in *.
    use H.
    refine (_ @ !(nat_trans_ax (η M) _ _ g)).
    exact p.
  - apply homset_property.
  - apply homset_property.
Qed.

Definition kleisli_univalent_double_cat
           {C : univalent_category}
           (M : Monad C)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (kleisli_double_cat M).
  - split.
    + apply univalent_category_is_univalent.
    + apply is_univalent_comma_twosided_disp_cat.
Defined.

(** * 3. The strict Kleisli double category *)
Definition strict_kleisli_double_cat
           {C : setcategory}
           (M : Monad C)
  : strict_double_cat.
Proof.
  use make_strict_double_cat.
  - exact C.
  - exact (comma_twosided_disp_cat (functor_identity C) M).
  - apply is_strict_comma_twosided_disp_cat.
  - exact (hor_id_kleisli M).
  - exact (hor_comp_kleisli M).
  - abstract
      (intros x y f ; cbn ;
       refine (maponpaths (λ z, z · _) (!(nat_trans_ax (η M) _ _ f)) @ _) ; cbn ;
       refine (_ @ id_right _) ;
       rewrite !assoc' ;
       apply maponpaths ;
       exact (@Monad_law1 _ M y)).
  - abstract
      (intros x y f ; cbn ;
       refine (_ @ id_right _) ;
       rewrite !assoc' ;
       apply maponpaths ;
       exact (@Monad_law2 _ M y)).
  - abstract
      (intros w x y z f g h ; cbn ;
       rewrite !functor_comp ;
       rewrite !assoc' ;
       do 2 apply maponpaths ;
       rewrite !assoc ;
       refine (_ @ maponpaths (λ z, z · _) (nat_trans_ax (μ M) _ _ h)) ; cbn ;
       rewrite !assoc' ;
       apply maponpaths ;
       apply (@Monad_law3 _ M)).
  - abstract
      (intro ; intros ;
       apply homset_property).
  - abstract
      (intro ; intros ;
       apply homset_property).
  - abstract
      (intro ; intros ;
       apply homset_property).
Defined.
