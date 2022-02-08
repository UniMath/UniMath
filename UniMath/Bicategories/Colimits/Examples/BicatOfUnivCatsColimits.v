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
Require Import UniMath.CategoryTheory.CategorySum.
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
Definition bincoprod_cocone_bicat_of_univ_cats
           (C₁ C₂ : bicat_of_univ_cats)
  : bincoprod_cocone C₁ C₂.
Proof.
  use make_bincoprod_cocone.
  - exact (bincoprod_of_univalent_category C₁ C₂).
  - exact (inl_functor (pr1 C₁) (pr1 C₂)).
  - exact (inr_functor (pr1 C₁) (pr1 C₂)).
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

  Definition has_bincoprod_ump_2_bicat_of_univ_cats_unique
             {Q : bicat_of_univ_cats}
             {F G : bincoprod_cocone_bicat_of_univ_cats C₁ C₂ --> Q}
             (α : bincoprod_cocone_inl (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · F
                  ==>
                  bincoprod_cocone_inl (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · G)
             (β : bincoprod_cocone_inr (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · F
                  ==>
                  bincoprod_cocone_inr (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · G)
    : isaprop
        (∑ γ,
         bincoprod_cocone_inl (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) ◃ γ = α
         ×
         bincoprod_cocone_inr (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) ◃ γ = β).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
    use nat_trans_eq ; [ apply homset_property | ].
    intro z ; induction z as [ x | y ].
    - exact (nat_trans_eq_pointwise (pr12 φ₁) x @ !(nat_trans_eq_pointwise (pr12 φ₂) x)).
    - exact (nat_trans_eq_pointwise (pr22 φ₁) y @ !(nat_trans_eq_pointwise (pr22 φ₂) y)).
  Qed.

  Definition has_bincoprod_ump_2_bicat_of_univ_cats
    : bincoprod_ump_2 (bincoprod_cocone_bicat_of_univ_cats C₁ C₂).
  Proof.
    intros Q F G α β.
    use iscontraprop1.
    - exact (has_bincoprod_ump_2_bicat_of_univ_cats_unique α β).
    - simple refine (_ ,, _ ,, _).
      + exact (sum_of_nat_trans α β).
      + exact (sum_of_nat_trans_inl α β).
      + exact (sum_of_nat_trans_inr α β).
  Defined.

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
