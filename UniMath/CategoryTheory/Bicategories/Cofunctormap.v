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
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.ContravariantFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Sigma.

Open Scope cat.
Open Scope mor_disp_scope.

(* Local Notation "'SET'" := hset_category. *)
Arguments nat_trans_comp {C C' F G H} a b.

Section Cofunctormaps.

  Variable (K : category).

  Definition disp_presheaf : disp_bicat bicat_of_cats
    := presheaf_disp_bicat K.

  Definition two_disp_presheaves : disp_bicat bicat_of_cats
    := dirprod_disp_bicat disp_presheaf disp_presheaf.

  Definition cofunctormaps_disp_cat_ob_mor : disp_cat_ob_mor (total_bicat two_disp_presheaves).
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

  Definition cofunctormaps_disp_cat_id_comp
    : disp_cat_id_comp _ cofunctormaps_disp_cat_ob_mor.
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

  Definition cofunctormaps_disp_cat_data : disp_cat_data (total_bicat two_disp_presheaves)
    := (_ ,, cofunctormaps_disp_cat_id_comp).

  Definition cofunctormaps_disp_prebicat
    : disp_prebicat (total_bicat two_disp_presheaves)
    := cell_unit_disp_prebicat cofunctormaps_disp_cat_data.

  Lemma has_disp_cellset_cofunctormaps_disp_prebicat
    : has_disp_cellset cofunctormaps_disp_prebicat.
  Proof.
    red; cbn; intros.
    exact isasetunit.
  Qed.

  Definition cofunctormaps_disp_bicat
    : disp_bicat (total_bicat two_disp_presheaves)
    := cofunctormaps_disp_prebicat,, has_disp_cellset_cofunctormaps_disp_prebicat.

  Definition morphisms_of_preshaves : disp_bicat bicat_of_cats.
  Proof.
    use sigma_bicat.
    apply two_disp_presheaves.
    exact cofunctormaps_disp_bicat.
  Defined.

End Cofunctormaps.
