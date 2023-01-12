Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.

Local Open Scope cat.

Definition isaprop_disp_twosided_mor
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : UU
  := ∏ (x₁ x₂ : C₁)
       (y₁ y₂ : C₂)
       (xy₁ : D x₁ y₁)
       (xy₂ : D x₂ y₂)
       (f : x₁ --> x₂)
       (g : y₁ --> y₂)
       (fg fg' : xy₁ -->[ f ][ g ] xy₂),
    fg = fg'.

Definition all_disp_mor_iso
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : UU
  := ∏ (x₁ x₂ : C₁)
       (y₁ y₂ : C₂)
       (xy₁ : D x₁ y₁)
       (xy₂ : D x₂ y₂)
       (f : x₁ --> x₂)
       (g : y₁ --> y₂)
       (Hf : is_z_isomorphism f)
       (Hg : is_z_isomorphism g)
       (fg : xy₁ -->[ f ][ g ] xy₂),
     is_iso_twosided_disp Hf Hg fg.

Definition sym_mor_twosided_disp_cat
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : UU
  := ∏ (x₁ x₂ : C₁)
       (y₁ y₂ : C₂)
       (xy₁ : D x₁ y₁)
       (xy₂ : D x₂ y₂)
       (f : x₁ --> x₂)
       (g : y₁ --> y₂)
       (Hf : is_z_isomorphism f)
       (Hg : is_z_isomorphism g)
       (fg : xy₁ -->[ f ][ g ] xy₂),
     xy₂
     -->[ inv_from_z_iso (f ,, Hf) ][ inv_from_z_iso (g ,, Hg) ]
     xy₁.

Definition all_disp_mor_iso_from_prop
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD₁ : isaprop_disp_twosided_mor D)
           (HD₂ : sym_mor_twosided_disp_cat D)
  : all_disp_mor_iso D.
Proof.
  intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g Hf Hg fg.
  simple refine (_ ,, _ ,, _).
  - apply HD₂.
    exact fg.
  - apply HD₁.
  - apply HD₁.
Defined.

Definition discrete_twosided_disp_cat
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : UU
  := isaprop_disp_twosided_mor D
     ×
     all_disp_mor_iso D
     ×
     is_univalent_twosided_disp_cat D.

Definition make_discrete_twosided_disp_cat
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD₁ : isaprop_disp_twosided_mor D)
           (HD₂ : sym_mor_twosided_disp_cat D)
           (HD₃ : is_univalent_twosided_disp_cat D)
  : discrete_twosided_disp_cat D.
Proof.
  simple refine (_ ,, _ ,, _).
  - exact HD₁.
  - apply all_disp_mor_iso_from_prop.
    + exact HD₁.
    + exact HD₂.
  - exact HD₃.
Defined.
