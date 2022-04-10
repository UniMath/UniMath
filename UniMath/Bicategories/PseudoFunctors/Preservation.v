(***********************************************************************

 Preservation of limits and colimits

 In this file, we look at the preservation of some limits and colimits.
 Our main focus is on final and initial objects and on products and
 coproducts.

 Contents:
 1. Basic definitions
 2. The identity pseudofunctor preserves (co)limits
 3. Preservation of the composition

 ***********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.

Local Open Scope cat.

(**
 1. Basic definitions
 *)
Section Preserves.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂).

  Definition preserves_bifinal
    : UU
    := ∏ (x : B₁),
       is_bifinal x
       →
       is_bifinal (F x).

  Definition preserves_biinitial
    : UU
    := ∏ (x : B₁),
       is_biinitial x
       →
       is_biinitial (F x).

  Definition psfunctor_binprod_cone
             {x y : B₁}
             (p : binprod_cone x y)
    : binprod_cone (F x) (F y)
    := make_binprod_cone
         (F p)
         (#F (binprod_cone_pr1 p))
         (#F (binprod_cone_pr2 p)).

  Definition preserves_binprod
    : UU
    := ∏ (x y : B₁)
         (p : binprod_cone x y),
       has_binprod_ump p
       →
       has_binprod_ump (psfunctor_binprod_cone p).

  Definition psfunctor_bincoprod_cocone
             {x y : B₁}
             (p : bincoprod_cocone x y)
    : bincoprod_cocone (F x) (F y)
    := make_bincoprod_cocone
         (F p)
         (#F (bincoprod_cocone_inl p))
         (#F (bincoprod_cocone_inr p)).

  Definition preserves_bincoprod
    : UU
    := ∏ (x y : B₁)
         (p : bincoprod_cocone x y),
       has_bincoprod_ump p
       →
       has_bincoprod_ump (psfunctor_bincoprod_cocone p).
End Preserves.

(**
 2. The identity pseudofunctor preserves (co)limits
 *)
Definition identity_preserves_bifinal
           (B : bicat)
  : preserves_bifinal (id_psfunctor B)
  := λ x Hx, Hx.

Definition identity_preserves_biinitial
           (B : bicat)
  : preserves_biinitial (id_psfunctor B)
  := λ x Hx, Hx.

Definition identity_preserves_binprod
           (B : bicat)
  : preserves_binprod (id_psfunctor B)
  := λ x y p Hp, Hp.

Definition identity_preserves_bincoprod
           (B : bicat)
  : preserves_bincoprod (id_psfunctor B)
  := λ x y p Hp, Hp.

(**
 3. Preservation of the composition
 *)
Definition comp_psfunctor_preserves_bifinal
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_bifinal F)
           (HG : preserves_bifinal G)
  : preserves_bifinal (comp_psfunctor G F)
  := λ x Hx, HG _ (HF _ Hx).

Definition comp_psfunctor_preserves_biinitial
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_biinitial F)
           (HG : preserves_biinitial G)
  : preserves_biinitial (comp_psfunctor G F)
  := λ x Hx, HG _ (HF _ Hx).

Definition comp_psfunctor_preserves_binprod
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_binprod F)
           (HG : preserves_binprod G)
  : preserves_binprod (comp_psfunctor G F)
  := λ x y p Hp, HG _ _ _ (HF _ _ _ Hp).

Definition comp_psfunctor_preserves_bincoprod
           {B₁ B₂ B₃ : bicat}
           {F : psfunctor B₁ B₂}
           {G : psfunctor B₂ B₃}
           (HF : preserves_bincoprod F)
           (HG : preserves_bincoprod G)
  : preserves_bincoprod (comp_psfunctor G F)
  := λ x y p Hp, HG _ _ _ (HF _ _ _ Hp).
