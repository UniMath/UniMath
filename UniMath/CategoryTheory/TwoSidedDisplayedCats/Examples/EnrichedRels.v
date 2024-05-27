(******************************************************************************************

 The 2-sided displayed category of enriched relations

 In this file, we show that enriched relations form a 2-sided displayed category.

 Content
 1. The data
 2. The 2-sided displayed category
 3. Univalence

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichedRelation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Section EnrichedRelationTwoSidedDispCat.
  Context (V : quantale_cosmos).

  (** * 1. The data *)
  Definition enriched_relation_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor SET SET.
  Proof.
    simple refine (_ ,, _).
    - exact (λ X Y, enriched_relation V X Y).
    - exact (λ X₁ X₂ Y₁ Y₂ R S f g, enriched_relation_square f g R S).
  Defined.

  Definition enriched_relation_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp
        enriched_relation_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ X Y R, id_v_enriched_relation_square R).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ τ θ, comp_v_enriched_relation_square τ θ).
  Defined.

  Definition enriched_relation_twosided_disp_cat_data
    : twosided_disp_cat_data SET SET.
  Proof.
    simple refine (_ ,, _).
    - exact enriched_relation_twosided_disp_cat_ob_mor.
    - exact enriched_relation_twosided_disp_cat_id_comp.
  Defined.

  Proposition enriched_relation_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms enriched_relation_twosided_disp_cat_data.
  Proof.
    repeat split ; intro ; intros.
    - apply isaprop_enriched_relation_square.
    - apply isaprop_enriched_relation_square.
    - apply isaprop_enriched_relation_square.
    - apply isasetaprop.
      apply isaprop_enriched_relation_square.
  Qed.

  (** * 2. The 2-sided displayed category *)
  Definition enriched_relation_twosided_disp_cat
    : twosided_disp_cat SET SET.
  Proof.
    simple refine (_ ,, _).
    - exact enriched_relation_twosided_disp_cat_data.
    - exact enriched_relation_twosided_disp_cat_axioms.
  Defined.

  Definition to_iso_enriched_relation_twosided_disp_cat
             {X Y : hSet}
             (R₁ R₂ : enriched_relation_twosided_disp_cat X Y)
             (f₁ : ∏ (x : X) (y : Y), R₁ x y --> R₂ x y)
             (f₂ : ∏ (x : X) (y : Y), R₂ x y --> R₁ x y)
    : iso_twosided_disp (identity_z_iso _) (identity_z_iso _) R₁ R₂.
  Proof.
    refine (f₁ ,, f₂ ,, _ ,, _) ; apply isaprop_enriched_relation_square.
  Defined.

  (** * 3. Univalence *)
  Proposition is_univalent_enriched_relation_twosided_disp_cat
    : is_univalent_twosided_disp_cat
        enriched_relation_twosided_disp_cat.
  Proof.
    intros X₁ X₂ Y₁ Y₂ p q R₁ R₂.
    induction p, q ; cbn.
    use isweqimplimpl.
    - intro p.
      use funextsec ; intro x.
      use funextsec ; intro y.
      use (isotoid _ (is_univalent_quantale_cosmos V)).
      use make_z_iso.
      + exact (pr1 p x y).
      + exact (pr12 p x y).
      + split.
        * apply is_poset_category_quantale_cosmos.
        * apply is_poset_category_quantale_cosmos.
    - apply isaset_enriched_relation.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply isaprop_enriched_relation_square.
  Qed.
End EnrichedRelationTwoSidedDispCat.
