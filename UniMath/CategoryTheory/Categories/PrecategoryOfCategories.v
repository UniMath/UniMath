(**************************************************************************************************
  The precategory of categories.
  Categories only form a precategory and not a category, since the type of functors between two
  categories is usually not a set, so this precategory does not have homsets.
  If we instead look at the subprecategory of "strict categories" or setcategories, in which the
  objects form a set, we actually get a category (see CategoryOfSetCategories).
  Contents
  1. The precategory of categories [category_precategory]
 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope cat.

Definition category_precategory_ob_mor
  : precategory_ob_mor
  := make_precategory_ob_mor
    category
    functor.

Definition category_precategory_data
  : precategory_data
  := make_precategory_data
    category_precategory_ob_mor
    (λ _, functor_identity _)
    (λ C₁ C₂ C₃ F G, F ∙ G).

Lemma category_precategory_is_precategory
  : is_precategory category_precategory_data.
Proof.
  use make_is_precategory_one_assoc;
    intros;
    apply (functor_eq _ _ (homset_property _));
    now use functor_data_eq.
Qed.

Definition category_precategory
  : precategory
  := make_precategory
    category_precategory_data
    category_precategory_is_precategory.
