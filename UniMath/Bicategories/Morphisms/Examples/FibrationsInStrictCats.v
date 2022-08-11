(******************************************************************************************

 Fibrations of strict categories

 In this file, we classify the internal Street fibrations of strict categories. These are
 just the same Street fibrations.

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetOpFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.StrictCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.

Local Open Scope cat.

Section IsOpCartesian.
  Context {C₁ C₂ : bicat_of_strict_cats}
          {F : C₁ --> C₂}
          (HF : street_opfib F)
          {C₀ : bicat_of_strict_cats}
          {G₁ G₂ : C₀ --> C₁}
          (α : G₁ ==> G₂)
          (Hα : ∏ (x : pr1 C₀), is_opcartesian_sopfib F (pr1 α x)).

  Section Factorization.
    Context {H : C₀ --> C₁}
      {β : G₁ ==> H}
      {δp : G₂ · F ==> H · F}
      (q : β ▹ F = (α ▹ F) • δp).

    Definition strict_pointwise_opcartesian_is_opcartesian_factor_data
      : nat_trans_data (pr1 G₂) (pr1 H)
      := λ x,
        opcartesian_factorization_sopfib
          _
          (Hα x)
          (pr1 β x)
          (pr1 δp x)
          (nat_trans_eq_pointwise q x).

    Definition strict_pointwise_opcartesian_is_opcartesian_factor_laws
      : is_nat_trans _ _ strict_pointwise_opcartesian_is_opcartesian_factor_data.
    Proof.
      intros x y f ; unfold strict_pointwise_opcartesian_is_opcartesian_factor_data ; cbn.
      pose (opcartesian_factorization_sopfib_commute
              F
              (Hα x) (pr1 β x) (pr1 δp x)
              (nat_trans_eq_pointwise q x))
        as p.
      pose (opcartesian_factorization_sopfib_commute
              F
              (Hα y) (pr1 β y) (pr1 δp y)
              (nat_trans_eq_pointwise q y))
        as p'.
      use (opcartesian_factorization_sopfib_unique
             _
             (Hα x)
             (pr1 β x · # (pr1 H) f)
             (pr1 δp x · # (pr1 F) (# (pr1 H) f))).
      - rewrite functor_comp.
        pose (r := nat_trans_eq_pointwise q x) ; cbn in r.
        etrans.
        {
          apply maponpaths_2.
          exact r.
        }
        clear r.
        rewrite !assoc'.
        apply idpath.
      - rewrite functor_comp.
        rewrite opcartesian_factorization_sopfib_over.
        exact (nat_trans_ax δp _ _ f).
      - rewrite !functor_comp.
        rewrite opcartesian_factorization_sopfib_over.
        apply idpath.
      - rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (!(nat_trans_ax α _ _ f)).
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          exact p'.
        }
        exact (nat_trans_ax β _ _ f).
      - rewrite !assoc.
        apply maponpaths_2.
        exact p.
    Qed.

    Definition strict_pointwise_opcartesian_is_opcartesian_factor
      : G₂ ==> H.
    Proof.
      use make_nat_trans.
      - exact strict_pointwise_opcartesian_is_opcartesian_factor_data.
      - exact strict_pointwise_opcartesian_is_opcartesian_factor_laws.
    Defined.

    Definition strict_pointwise_opcartesian_is_opcartesian_over
      : strict_pointwise_opcartesian_is_opcartesian_factor ▹ F = δp.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply (opcartesian_factorization_sopfib_over F).
    Qed.

    Definition strict_pointwise_opcartesian_is_opcartesian_comm
      : α • strict_pointwise_opcartesian_is_opcartesian_factor = β.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply (opcartesian_factorization_sopfib_commute F).
    Qed.

    Definition strict_pointwise_opcartesian_is_opcartesian_unique
      : isaprop (∑ (δ : G₂ ==> H), δ ▹ F = δp × α • δ = β).
    Proof.
      use invproofirrelevance.
      intros δ₁ δ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use (opcartesian_factorization_sopfib_unique
             _ (Hα x)
             (pr1 β x)
             (pr1 δp x)).
      - exact (nat_trans_eq_pointwise q x).
      - exact (nat_trans_eq_pointwise (pr12 δ₁) x).
      - exact (nat_trans_eq_pointwise (pr12 δ₂) x).
      - exact (nat_trans_eq_pointwise (pr22 δ₁) x).
      - exact (nat_trans_eq_pointwise (pr22 δ₂) x).
    Qed.
  End Factorization.

  Definition strict_pointwise_opcartesian_is_opcartesian
    : is_opcartesian_2cell_sopfib F α.
  Proof.
    intros H β δp q.
    use iscontraprop1.
    - exact (strict_pointwise_opcartesian_is_opcartesian_unique q).
    - simple refine (_ ,, _ ,, _).
      + exact (strict_pointwise_opcartesian_is_opcartesian_factor q).
      + exact (strict_pointwise_opcartesian_is_opcartesian_over q).
      + exact (strict_pointwise_opcartesian_is_opcartesian_comm q).
  Defined.
End IsOpCartesian.
