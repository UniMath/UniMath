Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.ConstProduct.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PullbackFunctor.
Import Products.Notations.

Local Open Scope cat.

Definition is_cartesian_closed_bicat
           (B : bicat_with_binprod)
  : UU
  := ∏ (x : B),
     right_universal_arrow
       (const_prod_psfunctor B x).

Definition make_is_cartesian_closed_bicat
           (B : bicat_with_binprod)
           (HB : is_univalent_2_1 B)
           (exp : B -> B → B)
           (app : ∏ (x y : B), exp x y ⊗ x --> y)
           (app2 : ∏ (x y₁ y₂ : B)
                     (f g : y₁ --> exp x y₂)
                     (α : f ⊗₁ id₁ x · app x y₂ ==> g ⊗₁ id₁ x · app x y₂),
                   f ==> g)
           (app2_eq : ∏ (x y₁ y₂ : B)
                        (f g : y₁ --> exp x y₂)
                        (α : f ⊗₁ id₁ x · app x y₂ ==> g ⊗₁ id₁ x · app x y₂),
                      app2 x y₁ y₂ f g α ⊗₂ id₂ (id₁ x) ▹ app x y₂ = α)
           (H : ∏ (x y₁ y₂ : B)
                  (f g : y₁ --> exp x y₂)
                  (α : f ⊗₁ id₁ x · app x y₂ ==> g ⊗₁ id₁ x · app x y₂)
                  (β₁ β₂ : f ==> g)
                  (p₁ : β₁ ⊗₂ id₂ (id₁ x) ▹ app x y₂ = α)
                  (p₂ : β₂ ⊗₂ id₂ (id₁ x) ▹ app x y₂ = α),
                β₁ = β₂)
           (lam : ∏ (x y₁ y₂ : B)
                    (f : y₁ ⊗ x --> y₂),
                  y₁ --> exp x y₂)
           (app_lam : ∏ (x y₁ y₂ : B)
                        (f : y₁ ⊗ x --> y₂),
                      invertible_2cell (lam x y₁ y₂ f ⊗₁ id₁ x · app x y₂) f)
  : is_cartesian_closed_bicat B.
Proof.
  intro x.
  use make_right_universal_arrow'.
  - exact HB.
  - exact (exp x).
  - exact (app x).
  - intros y₁ y₂ f g α.
    simple refine (_ ,, _).
    + exact (app2 x y₁ y₂ f g α).
    + exact (app2_eq x y₁ y₂ f g α).
  - exact (H x).
  - intros y₁ y₂ f.
    simple refine (_ ,, _).
    + exact (lam x y₁ y₂ f).
    + exact (app_lam x y₁ y₂ f).
Defined.

Definition exponentiable_morphism
           (B : bicat_with_pb)
           {b₁ b₂ : B}
           (f : b₁ --> b₂)
  : UU
  := right_universal_arrow (pb_psfunctor B f).

Definition locally_cartesian_closed_bicat
           (B : bicat_with_pb)
  : UU
  := ∏ (b₁ b₂ : B)
       (f : b₁ --> b₂),
     exponentiable_morphism B f.

Definition bicat_has_exponentials
           (B : bicat_with_pb)
  : UU
  := ∏ (b₁ b₂ : B)
       (f : b₁ --> b₂),
     (internal_sfib f → exponentiable_morphism B f)
     ×
     (internal_sopfib f → exponentiable_morphism B f).
