Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedFibration.

Local Open Scope cat.

Section ArrowTwoSidedDispCat.
  Context (C : category).

  Definition arrow_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor C C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, x --> y).
    - exact (λ x₁ x₂ y₁ y₂ h₁ h₂ f g, f · h₂ = h₁ · g).
  Defined.

  Definition arrow_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp arrow_twosided_disp_cat_ob_mor.
  Proof.
    split.
    - intros x y xy ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ p q ; cbn in *.
      rewrite assoc'.
      rewrite q.
      rewrite !assoc.
      apply maponpaths_2.
      exact p.
  Qed.

  Definition arrow_twosided_disp_cat_data
    : twosided_disp_cat_data C C.
  Proof.
    simple refine (_ ,, _).
    - exact arrow_twosided_disp_cat_ob_mor.
    - exact arrow_twosided_disp_cat_id_comp.
  Defined.

  Definition isaprop_arrow_twosided_mor
             {x₁ x₂ : C}
             {y₁ y₂ : C}
             (xy₁ : arrow_twosided_disp_cat_data x₁ y₁)
             (xy₂ : arrow_twosided_disp_cat_data x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : isaprop (xy₁ -->[ f ][ g ] xy₂).
  Proof.
    apply homset_property.
  Qed.

  Definition arrow_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms arrow_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply isaprop_arrow_twosided_mor.
    - intro ; intros.
      apply isaprop_arrow_twosided_mor.
    - intro ; intros.
      apply isaprop_arrow_twosided_mor.
    - intro ; intros.
      apply isasetaprop.
      apply isaprop_arrow_twosided_mor.
  Qed.

  Definition arrow_twosided_disp_cat
    : twosided_disp_cat C C.
  Proof.
    simple refine (_ ,, _).
    - exact arrow_twosided_disp_cat_data.
    - exact arrow_twosided_disp_cat_axioms.
  Defined.

  Definition arrow_twosided_disp_cat_is_iso
    : all_disp_mor_iso arrow_twosided_disp_cat.
  Proof.
    intro ; intros.
    simple refine (_ ,, _ ,, _) ; cbn in *.
    - use z_iso_inv_on_right.
      rewrite assoc.
      use z_iso_inv_on_left ; cbn.
      exact fg.
    - apply isaprop_arrow_twosided_mor.
    - apply isaprop_arrow_twosided_mor.
  Qed.

  Definition is_univalent_arrow_twosided_disp_cat
    : is_univalent_twosided_disp_cat arrow_twosided_disp_cat.
  Proof.
    intros x₁ x₂ y₁ y₂ p₁ p₂ xy₁ xy₂.
    induction p₁, p₂ ; cbn.
    use isweqimplimpl.
    - intros f.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact (!p).
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition discrete_arrow_twosided_disp_cat
    : discrete_twosided_disp_cat arrow_twosided_disp_cat.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - exact arrow_twosided_disp_cat_is_iso.
    - exact is_univalent_arrow_twosided_disp_cat.
  Qed.

  Definition arrow_twosided_opcleaving
    : twosided_opcleaving arrow_twosided_disp_cat.
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (f · g ,, _ ,, _) ; cbn.
    - apply id_left.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_arrow_twosided_mor.
      + simple refine (_ ,, _).
        * cbn in *.
          rewrite id_left, assoc in p.
          exact p.
        * apply isaprop_arrow_twosided_mor.
  Qed.

  Definition arrow_twosided_cleaving
    : twosided_cleaving arrow_twosided_disp_cat.
  Proof.
    intros x₁ x₂ x₃ f g ; cbn in *.
    simple refine (g · f ,, _ ,, _) ; cbn.
    - rewrite id_right.
      apply idpath.
    - intros x₄ x₅ h k l p.
      use iscontraprop1.
      + use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isaset_disp_mor.
        }
        apply isaprop_arrow_twosided_mor.
      + cbn in *.
        simple refine (_ ,, _).
        * rewrite id_right, assoc' in p.
          exact p.
        * apply isaprop_arrow_twosided_mor.
  Qed.

  Definition arrow_twosided_fibration
    : twosided_fibration arrow_twosided_disp_cat.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact arrow_twosided_opcleaving.
    - exact arrow_twosided_cleaving.
    - intro ; intros.
      apply arrow_twosided_disp_cat_is_iso.
  Defined.
End ArrowTwoSidedDispCat.
