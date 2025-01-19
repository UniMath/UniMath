(*****************************************************************************************

 Uniqueness of companion pairs

 In this file, we show that companion pairs are unique up to invertible 2-cell. From this
 we conclude that the type of companion pairs of a horizontal morphisms in locally
 univalent Verity double bicategories is a proposition ([isaprop_companion_pair]). In
 addition, having all companions is a proposition in locally univalent Verity double
 bicategory.

 Contents
 1. Squares between companion pairs
 2. The square is invertible
 3. Preservation of the unit and counit
 4. Consequences of the uniqueness

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.LocalUnivalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairs.

Local Open Scope cat.
Local Open Scope double_bicat.

(** * 1. Squares between companion pairs *)
Definition square_between_companions
           {B : verity_double_bicat}
           {x y : B}
           {h : x --> y}
           {v₁ v₂ : x -|-> y}
           (c₁ : are_companions h v₁)
           (c₂ : are_companions h v₂)
  : square_double_bicat (id_h x) (id_h y) v₁ v₂
  := linvunitor _ ◃s (runitor _ ▹s counit_are_companions c₂ ⋆v unit_are_companions c₁).

Section ComparionPairUnique.
  Context {B : verity_double_bicat}
          {x y : B}
          {h : x --> y}
          {v₁ v₂ : x -|-> y}
          (c₁ : are_companions h v₁)
          (c₂ : are_companions h v₂).

  Let γ₁ : square_double_bicat (id₁ _) (id₁ _) v₁ v₂
    := square_between_companions c₁ c₂.

  Let γ₂ : square_double_bicat (id₁ _) (id₁ _) v₂ v₁
    := square_between_companions c₂ c₁.

  (** * 2. The square is invertible *)
  Proposition comp_square_between_companions
    : comp_ver_globular_square γ₁ γ₂ = id_h_square_bicat v₁.
  Proof.
    unfold γ₁, γ₂, square_between_companions.
    unfold comp_ver_globular_square.
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        apply runitor_v_comp_square''.
      }
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        refine (!_).
        apply lunitor_v_comp_square''.
      }
      rewrite !rwhisker_lwhisker_square.
      rewrite <- !lwhisker_hcomp_square.
      do 2 apply maponpaths.
      rewrite <- !rwhisker_lwhisker_square.
      rewrite <- !rwhisker_hcomp_square.
      do 2 apply maponpaths.
      rewrite !lrwhisker_hcomp_square.
      rewrite lassociator_v_comp_square''.
      rewrite !rwhisker_lwhisker_square.
      rewrite <- lwhisker_hcomp_square.
      apply maponpaths.
      rewrite <- !rwhisker_square_comp.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite <- lunitor_triangle.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite vcomp_runitor.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lunitor_linvunitor.
          apply id2_left.
        }
        apply runitor_rinvunitor.
      }
      rewrite rwhisker_square_id.
      rewrite !double_bicat_interchange.
      rewrite are_companions_right'.
      rewrite <- !id_h_square_bicat_id.
      rewrite lunitor_h_comp_square'.
      rewrite runitor_h_comp_square'.
      rewrite <- !dwhisker_vcomp_square.
      apply maponpaths.
      rewrite !dwhisker_uwhisker_square.
      rewrite <- uwhisker_vcomp_square.
      rewrite !dwhisker_uwhisker_square.
      rewrite <- uwhisker_vcomp_square.
      apply maponpaths.
      rewrite !ud_whisker_vcomp_square.
      etrans.
      {
        apply maponpaths_2.
        rewrite <- !dwhisker_square_comp.
        rewrite rinvunitor_runitor.
        rewrite linvunitor_lunitor.
        rewrite !dwhisker_square_id.
        apply runitor_v_comp_square'.
      }
      rewrite l_rwhisker_v_comp_square.
      rewrite l_lwhisker_v_comp_square.
      do 2 apply maponpaths.
      apply are_companions_left'.
    }
    rewrite <- !rwhisker_lwhisker_square.
    rewrite <- !rwhisker_uwhisker_square.
    rewrite <- !rwhisker_dwhisker_square.
    rewrite <- !rwhisker_uwhisker_square.
    rewrite <- !rwhisker_lwhisker_square.
    rewrite <- !rwhisker_dwhisker_square.
    rewrite <- !rwhisker_uwhisker_square.
    rewrite <- !rwhisker_square_comp.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_runitor.
        rewrite runitor_rinvunitor.
        apply id2_left.
      }
      apply rinvunitor_runitor.
    }
    rewrite rwhisker_square_id.
    rewrite dwhisker_uwhisker_square.
    rewrite !lwhisker_uwhisker_square.
    rewrite dwhisker_uwhisker_square.
    rewrite <- uwhisker_square_comp.
    rewrite linvunitor_lunitor.
    rewrite uwhisker_square_id.
    rewrite !lwhisker_dwhisker_square.
    rewrite <- !lwhisker_square_comp.
    rewrite <- !dwhisker_square_comp.
    rewrite lunitor_runitor_identity.
    rewrite rinvunitor_runitor.
    rewrite dwhisker_square_id.
    etrans.
    {
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite runitor_rwhisker.
        rewrite vcomp_lunitor.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        apply id2_left.
      }
      apply linvunitor_lunitor.
    }
    apply lwhisker_square_id.
  Qed.

  (** * 3. Preservation of the unit and counit *)
  Proposition square_between_companions_unit
    : lunitor (id_h y) ▿s (linvunitor h ▵s γ₁ ⋆h unit_are_companions c₂)
      =
      unit_are_companions c₁.
  Proof.
    unfold γ₁, square_between_companions.
    etrans.
    {
      do 3 apply maponpaths.
      refine (!_).
      apply runitor_v_comp_square''.
    }
    rewrite <- lwhisker_hcomp_square.
    rewrite <- rwhisker_hcomp_square.
    etrans.
    {
      do 4 apply maponpaths.
      rewrite lrwhisker_hcomp_square.
      rewrite <- rwhisker_square_comp.
      rewrite runitor_rinvunitor.
      rewrite rwhisker_square_id.
      rewrite double_bicat_interchange.
      apply maponpaths_2.
      apply are_companions_right'.
    }
    etrans.
    {
      apply maponpaths.
      rewrite dwhisker_uwhisker_square.
      rewrite <- uwhisker_vcomp_square.
      rewrite rwhisker_uwhisker_square.
      rewrite lwhisker_uwhisker_square.
      rewrite <- uwhisker_square_comp.
      rewrite linvunitor_lunitor.
      rewrite uwhisker_square_id.
      apply idpath.
    }
    rewrite <- ud_whisker_vcomp_square.
    rewrite lunitor_v_comp_square'.
    rewrite <- rwhisker_square_comp.
    rewrite runitor_lunitor_identity.
    rewrite linvunitor_lunitor.
    rewrite rwhisker_square_id.
    rewrite <- lwhisker_square_comp.
    rewrite linvunitor_lunitor.
    rewrite lwhisker_square_id.
    rewrite <- id_h_square_bicat_id.
    rewrite runitor_h_comp_square'.
    rewrite !dwhisker_uwhisker_square.
    rewrite <- dwhisker_square_comp.
    rewrite <- uwhisker_square_comp.
    rewrite lunitor_runitor_identity.
    rewrite !rinvunitor_runitor.
    rewrite dwhisker_square_id.
    rewrite uwhisker_square_id.
    apply idpath.
  Qed.

  Proposition square_between_companions_counit
    : runitor h ▿s (linvunitor (id_h x) ▵s counit_are_companions c₁ ⋆h γ₁)
      =
      counit_are_companions c₂.
  Proof.
    unfold γ₁, square_between_companions.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply lunitor_v_comp_square''.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite rwhisker_lwhisker_square.
      rewrite <- lwhisker_hcomp_square.
      apply maponpaths.
      rewrite <- rwhisker_lwhisker_square.
      rewrite <- rwhisker_hcomp_square.
      apply maponpaths.
      rewrite lrwhisker_hcomp_square.
      rewrite <- rwhisker_square_comp.
      rewrite lunitor_linvunitor.
      rewrite rwhisker_square_id.
      rewrite double_bicat_interchange.
      rewrite are_companions_right'.
      rewrite <- id_h_square_bicat_id.
      rewrite uwhisker_id_v_square.
      rewrite <- dwhisker_square_comp.
      rewrite <- dwhisker_vcomp_square.
      apply maponpaths.
      rewrite runitor_v_comp_square'.
      rewrite lunitor_h_comp_square'.
      apply idpath.
    }
    rewrite <- rwhisker_dwhisker_square.
    rewrite <- rwhisker_square_comp.
    rewrite rinvunitor_runitor.
    rewrite rwhisker_square_id.
    rewrite lwhisker_dwhisker_square.
    rewrite <- lwhisker_square_comp.
    rewrite runitor_lunitor_identity.
    rewrite linvunitor_lunitor.
    rewrite lwhisker_square_id.
    rewrite !dwhisker_uwhisker_square.
    rewrite <- !dwhisker_square_comp.
    rewrite <- !uwhisker_square_comp.
    rewrite linvunitor_lunitor.
    rewrite uwhisker_square_id.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite linvunitor_lunitor.
    apply dwhisker_square_id.
  Qed.
End ComparionPairUnique.

(** * 4. Consequences of the uniqueness *)
Proposition isaprop_companion_pair
            {B : verity_double_bicat}
            (H : vertically_saturated B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
            {x y : B}
            (h : x --> y)
  : isaprop (∑ (v : x -|-> y), are_companions h v).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use (eq_companion_of_hor H HB_2_1).
  - use (v_sq_isotoid_2_1 H HB_2_1).
    use make_invertible_vertical_square.
    + use make_invertible_vertical_square_data.
      * exact (square_between_companions (pr2 φ₁) (pr2 φ₂)).
      * exact (square_between_companions (pr2 φ₂) (pr2 φ₁)).
    + split.
      * apply comp_square_between_companions.
      * apply comp_square_between_companions.
  - rewrite v_sq_idtoiso_isotoid_2_1 ; cbn.
    apply square_between_companions_unit.
  - rewrite v_sq_idtoiso_isotoid_2_1 ; cbn.
    apply square_between_companions_counit.
Qed.

Proposition isaprop_all_companions
            (B : verity_double_bicat)
            (H : vertically_saturated B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
  : isaprop (all_companions B).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro h.
  apply isaprop_companion_pair.
  - exact H.
  - exact HB_2_1.
Qed.

Proposition isaprop_weakly_hor_invariant
            (B : verity_double_bicat)
            (H : vertically_saturated B)
            (HB_2_1 : locally_univalent_verity_double_bicat B)
  : isaprop (weakly_hor_invariant B).
Proof.
  use impred ; intro x.
  use impred ; intro y.
  use impred ; intro h.
  use impred ; intro Hh.
  apply isaprop_companion_pair.
  - exact H.
  - exact HB_2_1.
Qed.
