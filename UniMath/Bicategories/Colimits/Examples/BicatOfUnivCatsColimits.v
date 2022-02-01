(*********************************************************************************

 Colimits of categories

 Contents:
 1. Initial object
 2. Coproducts

 *********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.

Local Open Scope cat.

(**
 1. Initial object
 *)
(** MOVE *)
Definition nat_trans_from_empty
           {C : category}
           (F G : empty_category ⟶ C)
  : nat_trans F G.
Proof.
  use make_nat_trans.
  - exact (λ z, fromempty z).
  - exact (λ z, fromempty z).
Defined.

Definition nat_trans_to_empty
           {C₁ C₂ : category}
           (F : C₁ ⟶ empty_category)
           (G : empty_category ⟶ C₂)
           (H : C₁ ⟶ C₂)
  : H ⟹ F ∙ G.
Proof.
  use make_nat_trans.
  - exact (λ x, fromempty (F x)).
  - exact (λ x y f, fromempty (F x)).
Defined.

Definition nat_trans_to_empty_is_nat_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ empty_category)
           (G : empty_category ⟶ C₂)
           (H : C₁ ⟶ C₂)
  : is_nat_iso (nat_trans_to_empty F G H).
Proof.
  intro x.
  exact (fromempty (F x)).
Defined.



Definition biinitial_univ_cats
  : @is_biinitial bicat_of_univ_cats empty_category.
Proof.
  use make_is_biinitial.
  - exact (λ C, functor_from_empty (pr1 C)).
  - exact (λ _ F G, nat_trans_from_empty F G).
  - abstract
      (intros Y f g α β ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       exact (λ z, fromempty z)).
Defined.

Definition strict_biinitial_univ_cats
  : @is_strict_biinitial_obj bicat_of_univ_cats empty_category.
Proof.
  refine (biinitial_univ_cats ,, _).
  intros C F.
  use equiv_to_adjequiv.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (functor_from_empty _).
  - apply nat_trans_to_empty.
  - exact (nat_trans_from_empty _ _).
  - use is_nat_iso_to_is_invertible_2cell.
    apply nat_trans_to_empty_is_nat_iso.
  - use is_nat_iso_to_is_invertible_2cell.
    intro z.
    apply (fromempty z).
Defined.

(**
 2. Coproducts
 *)
Definition bincoprod_of_precategory_ob_mor
           (C₁ C₂ : category)
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (C₁ ⨿ C₂).
  - intros z₁ z₂.
    induction z₁ as [ x₁ | y₁ ], z₂ as [ x₂ | y₂ ].
    + exact (x₁ --> x₂).
    + exact ∅.
    + exact ∅.
    + exact (y₁ --> y₂).
Defined.

Definition bincoprod_of_precategory_data
           (C₁ C₂ : category)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (bincoprod_of_precategory_ob_mor C₁ C₂).
  - intro z ; induction z as [ x | y ].
    + exact (identity x).
    + exact (identity y).
  - intros z₁ z₂ z₃ f g ;
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ; cbn in *.
    + exact (f · g).
    + exact (fromempty g).
    + exact (fromempty g).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact (fromempty g).
    + exact (f · g).
Defined.

Definition bincoprod_of_is_precategory
           (C₁ C₂ : category)
  : is_precategory (bincoprod_of_precategory_data C₁ C₂).
Proof.
  use make_is_precategory.
  - intros z₁ z₂ f.
    induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
    + apply id_left.
    + exact (fromempty f).
    + exact (fromempty f).
    + apply id_left.
  - intros z₁ z₂ f.
    induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
    + apply id_right.
    + exact (fromempty f).
    + exact (fromempty f).
    + apply id_right.
  - intros z₁ z₂ z₃ z₄ f g h ;
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ;
    induction z₄ as [ x₄ | y₄ ] ; cbn in * ;
    try (apply (fromempty f)) ; try (apply (fromempty g)) ; try (apply (fromempty h)).
    + apply assoc.
    + apply assoc.
  - intros z₁ z₂ z₃ z₄ f g h ;
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ;
    induction z₄ as [ x₄ | y₄ ] ; cbn in * ;
    try (apply (fromempty f)) ; try (apply (fromempty g)) ; try (apply (fromempty h)).
    + apply assoc'.
    + apply assoc'.
Qed.

Definition bincoprod_of_precategory
           (C₁ C₂ : category)
  : precategory.
Proof.
  use make_precategory.
  - exact (bincoprod_of_precategory_data C₁ C₂).
  - exact (bincoprod_of_is_precategory C₁ C₂).
Defined.

Definition bincoprod_of_category_has_homsets
           (C₁ C₂ : category)
  : has_homsets (bincoprod_of_precategory_ob_mor C₁ C₂).
Proof.
  intros z₁ z₂.
  induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
  - apply homset_property.
  - apply isasetempty.
  - apply isasetempty.
  - apply homset_property.
Defined.

Definition bincoprod_of_category
           (C₁ C₂ : category)
  : category.
Proof.
  use make_category.
  - exact (bincoprod_of_precategory C₁ C₂).
  - exact (bincoprod_of_category_has_homsets C₁ C₂).
Defined.

Definition is_univalent_bincoprod_of_category
           {C₁ C₂ : category}
           (HC₁ : is_univalent C₁)
           (HC₂ : is_univalent C₂)
  : is_univalent (bincoprod_of_category C₁ C₂).
Proof.
Admitted.

Definition bincoprod_of_univalent_category
           (C₁ C₂ : univalent_category)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (bincoprod_of_category C₁ C₂).
  - use is_univalent_bincoprod_of_category.
    + apply C₁.
    + apply C₂.
Defined.

Definition inl_functor_data
           (C₁ C₂ : category)
  : functor_data C₁ (bincoprod_of_category C₁ C₂).
Proof.
  use make_functor_data.
  - exact (λ x, inl x).
  - exact (λ _ _ f, f).
Defined.

Definition inl_is_functor
           (C₁ C₂ : category)
  : is_functor (inl_functor_data C₁ C₂).
Proof.
  split ; intro ; intros ; cbn.
  - apply idpath.
  - apply idpath.
Qed.

Definition inl_functor
           (C₁ C₂ : category)
  : C₁ ⟶ bincoprod_of_category C₁ C₂.
Proof.
  use make_functor.
  - exact (inl_functor_data C₁ C₂).
  - exact (inl_is_functor C₁ C₂).
Defined.

Definition inr_functor_data
           (C₁ C₂ : category)
  : functor_data C₂ (bincoprod_of_category C₁ C₂).
Proof.
  use make_functor_data.
  - exact (λ x, inr x).
  - exact (λ _ _ f, f).
Defined.

Definition inr_is_functor
           (C₁ C₂ : category)
  : is_functor (inr_functor_data C₁ C₂).
Proof.
  split ; intro ; intros ; cbn.
  - apply idpath.
  - apply idpath.
Qed.

Definition inr_functor
           (C₁ C₂ : category)
  : C₂ ⟶ bincoprod_of_category C₁ C₂.
Proof.
  use make_functor.
  - exact (inr_functor_data C₁ C₂).
  - exact (inr_is_functor C₁ C₂).
Defined.

Definition bincoprod_cocone_bicat_of_univ_cats
           (C₁ C₂ : bicat_of_univ_cats)
  : bincoprod_cocone C₁ C₂.
Proof.
  use make_bincoprod_cocone.
  - exact (bincoprod_of_univalent_category C₁ C₂).
  - exact (inl_functor (pr1 C₁) (pr1 C₂)).
  - exact (inr_functor (pr1 C₁) (pr1 C₂)).
Defined.

Definition sum_of_functors_data
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : functor_data (bincoprod_of_category C₁ C₂) Q.
Proof.
  use make_functor_data.
  - intro z.
    induction z as [ x | y ].
    + exact (F x).
    + exact (G y).
  - intros z₁ z₂ f.
    induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
    + exact (#F f).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact (#G f).
Defined.

Definition sum_of_functors_is_functor
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : is_functor (sum_of_functors_data F G).
Proof.
  split.
  - intro z.
    induction z as [ x | y ] ; cbn.
    + apply functor_id.
    + apply functor_id.
  - intros z₁ z₂ z₃ f g.
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ; cbn ;
    try (apply (fromempty f)) ; try (apply (fromempty g)).
    + apply functor_comp.
    + apply functor_comp.
Qed.

Definition sum_of_functors
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : bincoprod_of_category C₁ C₂ ⟶ Q.
Proof.
  use make_functor.
  - exact (sum_of_functors_data F G).
  - exact (sum_of_functors_is_functor F G).
Defined.

Definition sum_of_functor_inl
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : inl_functor C₁ C₂ ∙ sum_of_functors F G ⟹ F.
Proof.
  use make_nat_trans.
  - exact (λ z, identity _).
  - abstract
      (intros x₁ x₂ f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition sum_of_functor_inl_is_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : is_nat_iso (sum_of_functor_inl F G).
Proof.
  intro.
Admitted.

Definition sum_of_functor_inl_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : nat_iso
      (inl_functor C₁ C₂ ∙ sum_of_functors F G)
      F.
Proof.
  use make_nat_iso.
  - exact (sum_of_functor_inl F G).
  - exact (sum_of_functor_inl_is_nat_iso F G).
Defined.

Definition sum_of_functor_inr
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : inr_functor C₁ C₂ ∙ sum_of_functors F G ⟹ G.
Proof.
  use make_nat_trans.
  - exact (λ z, identity _).
  - abstract
      (intros x₁ x₂ f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition sum_of_functor_inr_is_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : is_nat_iso (sum_of_functor_inr F G).
Proof.
  intro.
Admitted.

Definition sum_of_functor_inr_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : nat_iso
      (inr_functor C₁ C₂ ∙ sum_of_functors F G)
      G.
Proof.
  use make_nat_iso.
  - exact (sum_of_functor_inr F G).
  - exact (sum_of_functor_inr_is_nat_iso F G).
Defined.

Section BincoprodUMP.
  Context (C₁ C₂ : bicat_of_univ_cats).

  Definition has_bincoprod_ump_1_bicat_of_univ_cats
    : bincoprod_ump_1 (bincoprod_cocone_bicat_of_univ_cats C₁ C₂).
  Proof.
    intros Q.
    use make_bincoprod_1cell.
    - exact (sum_of_functors
               (bincoprod_cocone_inl Q)
               (bincoprod_cocone_inr Q)).
    - use nat_iso_to_invertible_2cell.
      exact (sum_of_functor_inl_nat_iso
               (bincoprod_cocone_inl Q)
               (bincoprod_cocone_inr Q)).
    - use nat_iso_to_invertible_2cell.
      exact (sum_of_functor_inr_nat_iso
               (bincoprod_cocone_inl Q)
               (bincoprod_cocone_inr Q)).
  Defined.

  Definition has_bincoprod_ump_2_bicat_of_univ_cats
    : bincoprod_ump_2 (bincoprod_cocone_bicat_of_univ_cats C₁ C₂).
  Proof.
    intros Q F G α β.
    use iscontraprop1.
    - use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
      use nat_trans_eq ; [ apply homset_property | ].
      intro z ; induction z as [ x | y ].
      + exact (nat_trans_eq_pointwise (pr12 φ₁) x @ !(nat_trans_eq_pointwise (pr12 φ₂) x)).
      + exact (nat_trans_eq_pointwise (pr22 φ₁) y @ !(nat_trans_eq_pointwise (pr22 φ₂) y)).
    - simple refine (_ ,, _).
      + cbn in *.
  Admitted.

  Definition has_bincoprod_ump_bicat_of_univ_cats
    : has_bincoprod_ump (bincoprod_cocone_bicat_of_univ_cats C₁ C₂).
  Proof.
    split.
    - exact has_bincoprod_ump_1_bicat_of_univ_cats.
    - exact has_bincoprod_ump_2_bicat_of_univ_cats.
  Defined.
End BincoprodUMP.

Definition bincoprod_bicat_of_univ_cats
  : has_bincoprod bicat_of_univ_cats
  := λ C₁ C₂,
     bincoprod_cocone_bicat_of_univ_cats C₁ C₂
     ,,
     has_bincoprod_ump_bicat_of_univ_cats C₁ C₂.
