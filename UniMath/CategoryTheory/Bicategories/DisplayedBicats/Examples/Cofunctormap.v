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
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.ContravariantFunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Sigma.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Arguments nat_trans_comp {C C' F G H} a b.

Section Cofunctormaps.

  Variable (K : univalent_category).

  Definition disp_presheaf : disp_bicat bicat_of_cats
    := disp_presheaf_bicat K.

  Definition disp_two_presheaves : disp_bicat bicat_of_cats
    := disp_dirprod_bicat disp_presheaf disp_presheaf.

  Definition disp_two_presheaves_is_univalent_2_1
    : disp_locally_univalent disp_two_presheaves.
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
    - exact (disp_presheaves_is_univalent_2_0 K).
    - exact (disp_presheaves_is_univalent_2_0 K).
    - exact (disp_presheaves_is_univalent_2_1 K).
    - exact (disp_presheaves_is_univalent_2_1 K).
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
      + apply K.
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
      + apply K.
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

  Definition morphisms_of_presheaves_display : disp_bicat bicat_of_cats.
  Proof.
    use sigma_bicat.
    apply disp_two_presheaves.
    exact disp_cofunctormaps_bicat.
  Defined.

  Definition morphisms_of_presheaves : bicat
    := total_bicat morphisms_of_presheaves_display.

  Definition disp_cofunctormaps_bicat_univalent_2_1
    : disp_locally_univalent disp_cofunctormaps_bicat.
  Proof.
    apply disp_cell_unit_bicat_locally_univalent.
    intros F G η x y ; simpl in *.
    apply isaset_nat_trans.
    apply K.
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
    + apply total_is_locally_univalent.
      * exact univalent_cat_is_univalent_2_1.
      * exact disp_two_presheaves_is_univalent_2_1.
    + intros F G η x y ; simpl in *.
      apply isaset_nat_trans.
      apply K.
    + intros a ; simpl.
      apply isaset_nat_trans.
      apply K.
    + intros F α₁ α₂ X ; cbn in *.
      induction X as [X1 X2] ; cbn in *.
      apply nat_trans_eq.
      { apply K. }
      intros x ; cbn in *.
      pose (nat_trans_eq_pointwise X1 x) as p1.
      cbn in *.
      rewrite id_left, id_right in p1.
      exact p1.
  Qed.

  Definition morphisms_of_presheaves_univalent_2_0
    : is_univalent_2_0 morphisms_of_presheaves.
  Proof.
    apply sigma_is_univalent_2_0.
    - exact univalent_cat_is_univalent_2_0.
    - exact univalent_cat_is_univalent_2_1.
    - exact disp_two_presheaves_is_univalent_2_0.
    - exact disp_two_presheaves_is_univalent_2_1.
    - exact disp_cofunctormaps_bicat_univalent_2_0.
    - exact disp_cofunctormaps_bicat_univalent_2_1.
  Defined.
End Cofunctormaps.