(**
 Morphisms in the bicat of univalent categories

 Contents:
 1. Faithful 1-cells
 2. Fully faithful 1-cells
 3. Conservative 1-cells
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.

Local Open Scope cat.

(**
 1. Faithful 1-cells
 *)
Definition cat_faithful_is_faithful_1cell
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
           (HF : faithful F)
  : faithful_1cell F.
Proof.
  intros C₃ G₁ G₂ α₁ α₂ p.
  cbn in *.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x.
  use (invmaponpathsincl _ (HF (G₁ x) (G₂ x))).
  exact (nat_trans_eq_pointwise p x).
Qed.

Definition cat_faithful_1cell_is_faithful
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
           (HF : faithful_1cell F)
  : faithful F.
Proof.
  intros x y ; cbn in *.
  use isinclweqonpaths.
  intros f g.
  use isweqimplimpl.
  - intro p.
    assert (post_whisker (constant_nat_trans C₁ f) F
            =
            post_whisker (constant_nat_trans C₁ g) F)
      as X.
    {
      use nat_trans_eq ; [ apply homset_property | ].
      intro.
      exact p.
    }
    use (nat_trans_eq_pointwise (faithful_1cell_eq_cell HF X) x).
  - apply homset_property.
  - apply homset_property.
Qed.

Definition cat_faithful_weq_faithful_1cell
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
  : faithful F ≃ faithful_1cell F.
Proof.
  use weqimplimpl.
  - exact (cat_faithful_is_faithful_1cell F).
  - exact (cat_faithful_1cell_is_faithful F).
  - apply isaprop_faithful.
  - apply isaprop_faithful_1cell.
Qed.

(**
 2. Fully faithful 1-cells
 *)
Definition fully_faithful_inv_nat_trans_data
           {C₁ C₂ C₃ : category}
           {F : C₂ ⟶ C₃}
           (HF : fully_faithful F)
           {G₁ G₂ : C₁ ⟶ C₂}
           (α : G₁ ∙ F ⟹ G₂ ∙ F)
  : nat_trans_data G₁ G₂
  := λ x, invmap (make_weq _ (HF (G₁ x) (G₂ x))) (α x).

Definition fully_faithful_inv_is_nat_trans
           {C₁ C₂ C₃ : category}
           {F : C₂ ⟶ C₃}
           (HF : fully_faithful F)
           {G₁ G₂ : C₁ ⟶ C₂}
           (α : G₁ ∙ F ⟹ G₂ ∙ F)
  : is_nat_trans _ _ (fully_faithful_inv_nat_trans_data HF α).
Proof.
  intros x y f ; cbn ; unfold fully_faithful_inv_nat_trans_data.
  unfold fully_faithful in HF.
  pose (w := make_weq _ (HF (G₁ x) (G₂ y))).
  refine (!(homotinvweqweq w _) @ _ @ homotinvweqweq w _).
  apply maponpaths.
  cbn.
  rewrite !functor_comp.
  etrans.
  {
    apply maponpaths.
    apply (homotweqinvweq (make_weq _ (HF (G₁ _) (G₂ _)))).
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply (homotweqinvweq (make_weq _ (HF (G₁ _) (G₂ _)))).
  }
  refine (!_).
  exact (nat_trans_ax α _ _ f).
Qed.

Definition fully_faithful_inv_nat_trans
           {C₁ C₂ C₃ : category}
           {F : C₂ ⟶ C₃}
           (HF : fully_faithful F)
           {G₁ G₂ : C₁ ⟶ C₂}
           (α : G₁ ∙ F ⟹ G₂ ∙ F)
  : G₁ ⟹ G₂.
Proof.
  use make_nat_trans.
  - exact (fully_faithful_inv_nat_trans_data HF α).
  - exact (fully_faithful_inv_is_nat_trans HF α).
Defined.

Definition cat_fully_faithful_is_fully_faithful_1cell
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
           (HF : fully_faithful F)
  : fully_faithful_1cell F.
Proof.
  use make_fully_faithful.
  - apply cat_faithful_is_faithful_1cell.
    apply fully_faithful_implies_full_and_faithful.
    exact HF.
  - intros C₃ G₁ G₂ αF ; cbn in *.
    simple refine (_ ,, _).
    + exact (fully_faithful_inv_nat_trans HF αF).
    + use nat_trans_eq ; [ apply homset_property | ].
      intro x.
      cbn ; unfold fully_faithful_inv_nat_trans_data.
      apply (homotweqinvweq (make_weq # F (HF (G₁ x) (G₂ x)))).
Qed.

Definition cat_fully_faithful_1cell_is_fully_faithful
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
           (HF : fully_faithful_1cell F)
  : fully_faithful F.
Proof.
  use full_and_faithful_implies_fully_faithful.
  cbn in *.
  split.
  - intros x y f.
    apply hinhpr.

    assert (is_nat_trans
              (constant_functor C₁ C₁ x ∙ F)
              (constant_functor C₁ C₁ y ∙ F)
              (λ _, f))
      as n_is_nat_trans.
    {
      intro ; intros.
      cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    }
    pose (make_nat_trans
            (constant_functor C₁ C₁ x ∙ F)
            (constant_functor C₁ C₁ y ∙ F)
            (λ _, f)
            n_is_nat_trans)
      as n.

    pose (pr2 HF C₁ (constant_functor _ _ x) (constant_functor _ _ y) n) as inv.
    cbn in inv.
    simple refine (_ ,, _) ; cbn.
    + exact (pr1 inv x).
    + exact (nat_trans_eq_pointwise (pr2 inv) x).
  - apply cat_faithful_1cell_is_faithful.
    apply fully_faithful_1cell_faithful.
    exact HF.
Qed.

Definition cat_fully_faithful_weq_fully_faithful_1cell
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
  : fully_faithful F ≃ fully_faithful_1cell F.
Proof.
  use weqimplimpl.
  - exact (cat_fully_faithful_is_fully_faithful_1cell F).
  - exact (cat_fully_faithful_1cell_is_fully_faithful F).
  - apply isaprop_fully_faithful.
  - apply isaprop_fully_faithful_1cell.
Qed.

(**
 3. Conservative 1-cells
 *)
Definition cat_conservative_1cell_is_conservative
           {C₁ C₂ : bicat_of_univ_cats}
           {F : C₁ --> C₂}
           (HF : conservative_1cell F)
  : conservative F.
Proof.
  intros x y f Hf.
  refine (is_invertible_2cell_to_is_nat_iso
            _
            (HF unit_category _ _ (nat_trans_from_unit f) _)
           tt).
  use is_nat_iso_to_is_invertible_2cell.
  intro.
  cbn.
  apply Hf.
Defined.

Definition cat_conservative_is_conservative_1cell
           {C₁ C₂ : bicat_of_univ_cats}
           {F : C₁ --> C₂}
           (HF : conservative F)
  : conservative_1cell F.
Proof.
  intros C₀ G₁ G₂ α Hα.
  use is_nat_iso_to_is_invertible_2cell.
  intro x.
  apply HF.
  exact (is_invertible_2cell_to_is_nat_iso _ Hα x).
Defined.

Definition cat_conservative_weq_conservative
           {C₁ C₂ : bicat_of_univ_cats}
           (F : C₁ --> C₂)
  : conservative F ≃ conservative_1cell F.
Proof.
  use weqimplimpl.
  - exact cat_conservative_is_conservative_1cell.
  - exact cat_conservative_1cell_is_conservative.
  - apply isaprop_conservative.
  - apply isaprop_conservative_1cell.
Defined.
