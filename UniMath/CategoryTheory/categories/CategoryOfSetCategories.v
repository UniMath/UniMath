(******************************************************************************************

 The category of strict categories

 Strict categories are the categories in which the type of objects forms a set. As such,
 the type of functors between them is a set as well, and this allows us to construct a
 category whose objects are strict categories and whose morphisms are functors.

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Local Open Scope cat.

Definition precat_ob_mor_of_setcategory
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact setcategory.
  - exact (λ C₁ C₂, C₁ ⟶ C₂).
Defined.

Definition precat_data_of_setcategory
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact precat_ob_mor_of_setcategory.
  - exact (λ C, functor_identity _).
  - exact (λ C₁ C₂ C₃ F G, F ∙ G).
Defined.

Definition is_precategory_of_setcategory
  : is_precategory precat_data_of_setcategory.
Proof.
  use make_is_precategory_one_assoc.
  - intros C₁ C₂ F.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
  - intros C₁ C₂ F.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
  - intros C₁ C₂ C₃ C₄ F G H.
    use functor_eq.
    {
      apply homset_property.
    }
    use functor_data_eq ; cbn.
    + intro ; apply idpath.
    + intros x y f ; cbn.
      apply idpath.
Qed.

Definition precat_of_setcategory
  : precategory.
Proof.
  use make_precategory.
  - exact precat_data_of_setcategory.
  - exact is_precategory_of_setcategory.
Defined.

Definition has_homsets_cat_of_setcategory
  : has_homsets precat_of_setcategory.
Proof.
  intros C₁ C₂.
  use functor_isaset.
  - apply homset_property.
  - apply C₂.
Qed.

Definition cat_of_setcategory
  : category.
Proof.
  use make_category.
  - exact precat_of_setcategory.
  - exact has_homsets_cat_of_setcategory.
Defined.
