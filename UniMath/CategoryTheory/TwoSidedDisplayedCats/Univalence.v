Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.

Local Open Scope cat.

Definition idtoiso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           (p : x₁ = x₂)
           (q : y₁ = y₂)
           (xy₁ : D x₁ y₁)
           (xy₂ : D x₂ y₂)
           (r : transportf (λ z, D z _) p (transportf (λ z, D _ z) q xy₁) = xy₂)
  : iso_twosided_disp (idtoiso p) (idtoiso q) xy₁ xy₂.
Proof.
  induction p.
  induction q.
  induction r.
  apply id_iso_twosided_disp.
Defined.

Definition is_univalent_twosided_disp_cat
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : UU
  := ∏ (x₁ x₂ : C₁)
       (y₁ y₂ : C₂)
       (p : x₁ = x₂)
       (q : y₁ = y₂)
       (xy₁ : D x₁ y₁)
       (xy₂ : D x₂ y₂),
     isweq (idtoiso_twosided_disp p q xy₁ xy₂).
