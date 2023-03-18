(**********************************************************************************

 Univalence two-sided displayed categories

 We define univalent two-sided displayed categories. To do so, we first define the
 map that sends identities to isomorphisms. Univalence is then expressed the usual
 way.

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
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

Definition isaprop_is_univalent_twosided_disp_cat
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : isaprop (is_univalent_twosided_disp_cat D).
Proof.
  do 8 (use impred ; intro).
  apply isapropisweq.
Qed.

Definition isotoid_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : is_univalent_twosided_disp_cat D)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           (p : x₁ = x₂)
           (q : y₁ = y₂)
           (xy₁ : D x₁ y₁)
           (xy₂ : D x₂ y₂)
           (r : iso_twosided_disp (idtoiso p) (idtoiso q) xy₁ xy₂)
  : transportf (λ z, D z _) p (transportf (λ z, D _ z) q xy₁) = xy₂
  := invmap (_ ,, HD x₁ x₂ y₁ y₂ p q xy₁ xy₂) r.
