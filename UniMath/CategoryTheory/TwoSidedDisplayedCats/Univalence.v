(**********************************************************************************

 Univalence two-sided displayed categories

 We define univalent two-sided displayed categories. To do so, we first define the
 map that sends identities to isomorphisms. Univalence is then expressed the usual
 way.

 Contents
 1. Univalence for two-sided displayed categories
 2. Equivalence with univalent displayed categories

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.

Local Open Scope cat.

(**
 1. Univalence for two-sided displayed categories
 *)
Definition idtoiso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           (p : x₁ = x₂)
           (q : y₁ = y₂)
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
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
     isweq (idtoiso_twosided_disp p q (xy₁ := xy₁) (xy₂ := xy₂)).

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
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           (r : iso_twosided_disp (idtoiso p) (idtoiso q) xy₁ xy₂)
  : transportf (λ z, D z _) p (transportf (λ z, D _ z) q xy₁) = xy₂
  := invmap (_ ,, HD x₁ x₂ y₁ y₂ p q xy₁ xy₂) r.

Proposition idtoisotoid_twosided_disp
            {C₁ C₂ : category}
            {D : twosided_disp_cat C₁ C₂}
            (HD : is_univalent_twosided_disp_cat D)
            {x₁ x₂ : C₁}
            {y₁ y₂ : C₂}
            (p : x₁ = x₂)
            (q : y₁ = y₂)
            {xy₁ : D x₁ y₁}
            {xy₂ : D x₂ y₂}
            (r : transportf (λ z, D z _) p (transportf (λ z, D _ z) q xy₁) = xy₂)
  : isotoid_twosided_disp HD p q (idtoiso_twosided_disp p q r) = r.
Proof.
  apply homotinvweqweq.
Qed.

Proposition isotoidtoiso_twosided_disp
            {C₁ C₂ : category}
            {D : twosided_disp_cat C₁ C₂}
            (HD : is_univalent_twosided_disp_cat D)
            {x₁ x₂ : C₁}
            {y₁ y₂ : C₂}
            (p : x₁ = x₂)
            (q : y₁ = y₂)
            {xy₁ : D x₁ y₁}
            {xy₂ : D x₂ y₂}
            (r : iso_twosided_disp (idtoiso p) (idtoiso q) xy₁ xy₂)
  : idtoiso_twosided_disp p q (isotoid_twosided_disp HD p q r) = r.
Proof.
  apply (homotweqinvweq (_ ,, HD x₁ x₂ y₁ y₂ p q xy₁ xy₂)).
Qed.

Definition univalent_twosided_disp_cat
           (C₁ C₂ : category)
  : UU
  := ∑ (D : twosided_disp_cat C₁ C₂), is_univalent_twosided_disp_cat D.

#[reversible=no] Coercion univalent_twosided_disp_cat_to_twosided_disp_cat
         {C₁ C₂ : category}
         (D : univalent_twosided_disp_cat C₁ C₂)
  : twosided_disp_cat C₁ C₂
  := pr1 D.

Proposition is_univalent_univalent_twosided_disp_cat
            {C₁ C₂ : category}
            (D : univalent_twosided_disp_cat C₁ C₂)
  : is_univalent_twosided_disp_cat D.
Proof.
  exact (pr2 D).
Qed.

(**
 2. Equivalence with univalent displayed categories
 *)
Definition is_univalent_twosided_disp_cat_weq_is_univalent_disp_cat
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : is_univalent_twosided_disp_cat D
    ≃
    is_univalent_disp (two_sided_disp_cat_weq_disp_cat C₁ C₂ D).
Proof.
  use weqimplimpl.
  - intros H.
    use is_univalent_disp_from_fibers.
    intros x xx yy.
    use weqhomot.
    + exact (iso_twosided_disp_weq_z_iso_disp xx yy
             ∘ make_weq _ (H _ _ _ _ (idpath _) (idpath _) xx yy))%weq.
    + intros p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_z_iso_disp.
      }
      apply idpath.
  - intros H x₁ x₂ y₁ y₂ p q xy₁ xy₂.
    induction p, q.
    use weqhomot.
    + exact (invweq (iso_twosided_disp_weq_z_iso_disp xy₁ xy₂)
             ∘ make_weq _ (H (x₁ ,, y₁) (x₁ ,, y₁) (idpath _) xy₁ xy₂))%weq.
    + intros p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_iso_twosided_disp.
      }
      apply idpath.
  - apply isaprop_is_univalent_twosided_disp_cat.
  - apply isaprop_is_univalent_disp.
Qed.

Definition univalent_twosided_disp_cat_weq_univalent_disp_cat
           (C₁ C₂ : category)
  : univalent_twosided_disp_cat C₁ C₂
    ≃
    disp_univalent_category (category_binproduct C₁ C₂).
Proof.
  use weqtotal2.
  - exact (two_sided_disp_cat_weq_disp_cat C₁ C₂).
  - exact (λ D, is_univalent_twosided_disp_cat_weq_is_univalent_disp_cat D).
Defined.
