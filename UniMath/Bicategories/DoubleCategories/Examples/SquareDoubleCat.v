(**********************************************************************************

 The square double category of a category

 In this file, we construct a double category from any category `C`. This double
 category is called the square double category. The objects in this double category
 are objects in `C`, horizontal and vertical morphisms in this double category are
 morphisms in `C`, and the squares in this double category are commutative squares
 in `C`. To define this double category, we use the 2-sided displayed category of
 arrows. The operations on horizontal morphisms are inherited from `C`.

 We also define the strict variation of this construction for strict categories.

 Contents
 1. Horizontal operations
 2. The square double category
 3. The strict square double category

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Arrow.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.SymmetricUnivalent.
Require Import UniMath.Bicategories.DoubleCategories.Core.StrictDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.

(** * 1. Horizontal operations *)
Section ArrowDoubleCategory.
  Context (C : category).

  Definition hor_id_data_arrow_twosided_disp_cat
    : hor_id_data (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_id_data ; cbn.
    - exact (λ x, identity x).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Proposition hor_id_laws_arrow_twosided_disp_cat
    : hor_id_laws hor_id_data_arrow_twosided_disp_cat.
  Proof.
    repeat split ; intros.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition hor_id_arrow_twosided_disp_cat
    : hor_id (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_id.
    - exact hor_id_data_arrow_twosided_disp_cat.
    - exact hor_id_laws_arrow_twosided_disp_cat.
  Defined.

  Definition hor_comp_data_arrow_twosided_disp_cat
    : hor_comp_data (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_comp_data.
    - exact (λ x y z f g, f · g).
    - abstract
        (intros x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂ ; cbn in * ;
         rewrite !assoc ;
         rewrite s₁ ;
         rewrite !assoc' ;
         rewrite s₂ ;
         apply idpath).
  Defined.

  Definition hor_comp_laws_arrow_twosided_disp_cat
    : hor_comp_laws hor_comp_data_arrow_twosided_disp_cat.
  Proof.
    repeat split ; intros.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition hor_comp_arrow_twosided_disp_cat
    : hor_comp (arrow_twosided_disp_cat C).
  Proof.
    use make_hor_comp.
    - exact hor_comp_data_arrow_twosided_disp_cat.
    - exact hor_comp_laws_arrow_twosided_disp_cat.
  Defined.

  Definition double_cat_lunitor_arrow_twosided_disp_cat
    : double_cat_lunitor
        hor_id_arrow_twosided_disp_cat
        hor_comp_arrow_twosided_disp_cat.
  Proof.
    use make_double_lunitor.
    - intros x y f ; cbn.
      use make_iso_twosided_disp.
      + abstract
          (cbn ;
           rewrite !id_left, !id_right ;
           apply idpath).
      + apply arrow_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition double_cat_runitor_arrow_twosided_disp_cat
    : double_cat_runitor
        hor_id_arrow_twosided_disp_cat
        hor_comp_arrow_twosided_disp_cat.
  Proof.
    use make_double_runitor.
    - intros x y f ; cbn.
      use make_iso_twosided_disp.
      + abstract
          (cbn ;
           rewrite !id_left, !id_right ;
           apply idpath).
      + apply arrow_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Definition double_cat_associator_arrow_twosided_disp_cat
    : double_cat_associator hor_comp_arrow_twosided_disp_cat.
  Proof.
    use make_double_associator.
    - intros w x y z h₁ h₂ h₃ ; cbn.
      use make_iso_twosided_disp.
      + abstract
          (cbn ;
           rewrite !id_left, !id_right, !assoc' ;
           apply idpath).
      + apply arrow_twosided_disp_cat_is_iso.
    - intro ; intros.
      apply homset_property.
  Qed.

  Proposition triangle_law_arrow_twosided_disp_cat
    : triangle_law
        double_cat_lunitor_arrow_twosided_disp_cat
        double_cat_runitor_arrow_twosided_disp_cat
        double_cat_associator_arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    apply homset_property.
  Qed.

  Proposition pentagon_law_arrow_twosided_disp_cat
    : pentagon_law double_cat_associator_arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    apply homset_property.
  Qed.
End ArrowDoubleCategory.

(** * 2. The square double category *)
Definition square_double_cat
           (C : category)
  : double_cat.
Proof.
  use make_double_cat.
  - exact C.
  - exact (arrow_twosided_disp_cat C).
  - exact (hor_id_arrow_twosided_disp_cat C).
  - exact (hor_comp_arrow_twosided_disp_cat C).
  - exact (double_cat_lunitor_arrow_twosided_disp_cat C).
  - exact (double_cat_runitor_arrow_twosided_disp_cat C).
  - exact (double_cat_associator_arrow_twosided_disp_cat C).
  - exact (triangle_law_arrow_twosided_disp_cat C).
  - exact (pentagon_law_arrow_twosided_disp_cat C).
Defined.

Definition all_companions_square_double_cat
           (C : category)
  : all_companions_double_cat (square_double_cat C).
Proof.
  intros x y f.
  refine (f ,, _).
  use make_double_cat_are_companions'.
  - abstract
      (cbn ;
       apply idpath).
  - abstract
      (cbn ;
       apply idpath).
  - apply homset_property.
  - apply homset_property.
Defined.

Definition square_univalent_double_cat
           (C : univalent_category)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (square_double_cat C).
  - split.
    + apply univalent_category_is_univalent.
    + apply is_univalent_arrow_twosided_disp_cat.
Defined.

Proposition symmetric_univalent_square_double_cat
            (C : univalent_category)
  : symmetric_univalent (square_univalent_double_cat C).
Proof.
  use make_symmetric_univalent.
  - intros x y ; cbn.
    apply homset_property.
  - cbn.
    assert (transpose_category
              (square_univalent_double_cat C)
              (λ x y, homset_property C x y)
            =
            C) as p.
    {
      use subtypePath.
      {
        intro.
        apply isaprop_has_homsets.
      }
      induction C as [ [ C H₁ ] H₂ ].
      cbn.
      refine (maponpaths (λ z, _ ,, z) _).
      apply isaprop_is_precategory.
      apply homset_property.
    }
    pose (univalent_category_is_univalent C) as H.
    rewrite <- p in H.
    exact H.
  - intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    + intros f.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact (p).
    + apply homset_property.
    + use isaproptotal2.
      * intro.
        apply isaprop_is_iso_twosided_disp.
      * intros.
        apply homset_property.
Qed.

(** * 3. The strict square double category *)
Definition strict_square_double_cat
           (C : setcategory)
  : strict_double_cat.
Proof.
  use make_strict_double_cat.
  - exact C.
  - exact (arrow_twosided_disp_cat C).
  - apply is_strict_arrow_twosided_disp_cat.
  - exact (hor_id_arrow_twosided_disp_cat C).
  - exact (hor_comp_arrow_twosided_disp_cat C).
  - abstract
      (intros x y f ; cbn ;
       apply id_left).
  - abstract
      (intros x y f ; cbn ;
       apply id_right).
  - abstract
      (intros w x y z f g h ; cbn ;
       apply assoc).
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
