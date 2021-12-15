(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

(* ============================================================================================= *)
(* Displayed transformation of contravariant functors.                                           *)
(* ============================================================================================= *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ContravariantFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Arguments nat_trans_comp {C C' F G H} a b.

Section Cofunctormaps.

  Variable (K : univalent_category).

  Definition disp_presheaf : disp_bicat bicat_of_univ_cats
    := disp_presheaf_bicat K.

  Definition disp_two_presheaves : disp_bicat bicat_of_univ_cats
    := disp_dirprod_bicat disp_presheaf disp_presheaf.

  Definition disp_two_presheaves_is_univalent_2_1
    : disp_univalent_2_1 disp_two_presheaves.
  Proof.
    apply is_univalent_2_1_dirprod_bicat.
    - exact (disp_presheaves_is_univalent_2_1 K).
    - exact (disp_presheaves_is_univalent_2_1 K).
  Defined.

  Definition disp_two_presheaves_is_univalent_2_0
    : disp_univalent_2_0 disp_two_presheaves.
  Proof.
    apply is_univalent_2_0_dirprod_bicat.
    - exact univalent_cat_is_univalent_2_1.
    - exact (disp_presheaves_is_univalent_2 K).
    - exact (disp_presheaves_is_univalent_2 K).
  Defined.

  Definition disp_two_presheaves_is_univalent_2
    : disp_univalent_2 disp_two_presheaves.
  Proof.
    split.
    - exact disp_two_presheaves_is_univalent_2_0.
    - exact disp_two_presheaves_is_univalent_2_1.
  Defined.

  Definition disp_cofunctormaps_cat_ob_mor : disp_cat_ob_mor (total_bicat disp_two_presheaves).
  Proof.
    red.
    use tpair.
    - intros (C, (ty, tm)). cbn in *.
      exact (tm ⟹ ty).
    - intros (C, (ty, tm)) (C', (ty', tm')) p p' (f, (αty, αtm)).
      cbn in *.
      exact (nat_trans_comp p αty =
             nat_trans_comp αtm (pre_whisker _ p')).
  Defined.

  Definition disp_cofunctormaps_cat_id_comp
    : disp_cat_id_comp _ disp_cofunctormaps_cat_ob_mor.
  Proof.
    apply tpair.
    - intros (C, (ty, tm)) p.
      apply nat_trans_eq.
      + apply homset_property.
      + cbn. intros. etrans.
        * apply id_right.
        * apply pathsinv0. apply id_left.
    - intros (C, (ty, tm)).
      intros (C', (ty', tm')).
      intros (C'', (ty'', tm'')).
      cbn in *.
      intros (f, (αty,αtm)).
      intros (g, (βty,βtm)).
      cbn in *.
      intros p p' p''.
      cbn in *.
      intros eq1 eq2.
      apply nat_trans_eq.
      + apply homset_property.
      + cbn. intros x.
        set (h1 := nat_trans_eq_pointwise eq1 x).
        set (h2 := nat_trans_eq_pointwise eq2 (f x)).
        cbn in *.
        rewrite assoc.
        rewrite h1.
        rewrite <- assoc.
        rewrite <- assoc.
        apply maponpaths.
        apply h2.
  Defined.

  Definition disp_cofunctormaps_cat_data : disp_cat_data (total_bicat disp_two_presheaves)
    := (_ ,, disp_cofunctormaps_cat_id_comp).

  Definition disp_cofunctormaps_bicat
    : disp_bicat (total_bicat disp_two_presheaves)
    := disp_cell_unit_bicat disp_cofunctormaps_cat_data.

  Definition morphisms_of_presheaves_display : disp_bicat bicat_of_univ_cats.
  Proof.
    use sigma_bicat.
    apply disp_two_presheaves.
    exact disp_cofunctormaps_bicat.
  Defined.

  Definition morphisms_of_presheaves : bicat
    := total_bicat morphisms_of_presheaves_display.

  Definition disp_cofunctormaps_bicat_univalent_2_1
    : disp_univalent_2_1 disp_cofunctormaps_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_1.
    intros F G η x y ; simpl in *.
    apply isaset_nat_trans.
    apply homset_property.
  Qed.

  Definition morphisms_of_presheaves_univalent_2_1
    : is_univalent_2_1 morphisms_of_presheaves.
  Proof.
    apply sigma_is_univalent_2_1.
    - exact univalent_cat_is_univalent_2_1.
    - exact disp_two_presheaves_is_univalent_2_1.
    - exact disp_cofunctormaps_bicat_univalent_2_1.
  Defined.

  Definition disp_cofunctormaps_bicat_univalent_2_0
    : disp_univalent_2_0 disp_cofunctormaps_bicat.
  Proof.
    apply disp_cell_unit_bicat_univalent_2_0.
    + apply total_is_univalent_2_1.
      * exact univalent_cat_is_univalent_2_1.
      * exact disp_two_presheaves_is_univalent_2_1.
    + intros F G η x y ; simpl in *.
      apply isaset_nat_trans.
      apply homset_property.
    + intros a ; simpl.
      apply isaset_nat_trans.
      apply homset_property.
    + intros F α₁ α₂ X ; cbn in *.
      induction X as [X1 X2] ; cbn in *.
      apply nat_trans_eq.
      { apply homset_property. }
      intros x ; cbn in *.
      pose (nat_trans_eq_pointwise X1 x) as p1.
      cbn in *.
      rewrite id_left, id_right in p1.
      exact p1.
  Qed.

  Definition disp_cofunctormaps_bicat_univalent_2
    : disp_univalent_2 disp_cofunctormaps_bicat.
  Proof.
    split.
    - exact disp_cofunctormaps_bicat_univalent_2_0.
    - exact disp_cofunctormaps_bicat_univalent_2_1.
  Defined.

  Definition morphisms_of_presheaves_univalent_2_0
    : is_univalent_2_0 morphisms_of_presheaves.
  Proof.
    apply sigma_is_univalent_2_0.
    - exact univalent_cat_is_univalent_2.
    - exact disp_two_presheaves_is_univalent_2.
    - exact disp_cofunctormaps_bicat_univalent_2.
  Defined.

  Definition morphisms_of_presheaves_univalent_2
    : is_univalent_2 morphisms_of_presheaves.
  Proof.
    split.
    - exact morphisms_of_presheaves_univalent_2_0.
    - exact morphisms_of_presheaves_univalent_2_1.
  Defined.

  Definition disp_2cells_isaprop_cofunctormaps
    : disp_2cells_isaprop disp_cofunctormaps_bicat
    := disp_2cells_isaprop_cell_unit_bicat disp_cofunctormaps_cat_data.

  Definition disp_locally_groupoid_cofunctormaps
    : disp_locally_groupoid disp_cofunctormaps_bicat
    := disp_locally_groupoid_cell_unit_bicat disp_cofunctormaps_cat_data.

  Definition disp_2cells_isaprop_morphisms_of_presheaves_display
    : disp_2cells_isaprop morphisms_of_presheaves_display.
  Proof.
    apply disp_2cells_isaprop_sigma.
    - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_presheaf.
    - apply disp_2cells_isaprop_cofunctormaps.
  Qed.

  Definition disp_locally_groupoid_morphisms_of_presheaves_display
    : disp_locally_groupoid morphisms_of_presheaves_display.
  Proof.
    apply disp_locally_groupoid_sigma.
    - exact univalent_cat_is_univalent_2.
    - apply disp_2cells_isaprop_prod ; apply disp_2cells_isaprop_presheaf.
    - apply disp_2cells_isaprop_cofunctormaps.
    - apply disp_locally_groupoid_prod ; apply disp_locally_groupoid_presheaf.
    - exact disp_locally_groupoid_cofunctormaps.
  Qed.
End Cofunctormaps.
