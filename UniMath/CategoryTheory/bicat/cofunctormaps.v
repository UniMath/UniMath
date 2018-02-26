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
Require Import UniMath.CategoryTheory.bicat.bicat.
Require Import UniMath.CategoryTheory.bicat.disp_bicat.
Require Import UniMath.CategoryTheory.bicat.Constructions.
Require Import UniMath.CategoryTheory.bicat.bicat_of_cats.
Require Import UniMath.CategoryTheory.bicat.contravariant_functors.
Require Import UniMath.CategoryTheory.bicat.sigma.

Open Scope cat.
Open Scope mor_disp_scope.

Section Disp_Prebicat_Cells_Unit.

  Context {C : prebicat} (D : disp_cat_data C).

  Definition disp_prebicat_cells_unit
    : disp_prebicat_1_id_comp_cells C.
  Proof.
    exists D. red. intros. exact unit.
  Defined.

  Definition disp_prebicat_cells_unit_ops
    : disp_prebicat_ops disp_prebicat_cells_unit.
  Proof.
    repeat use tpair; cbn; intros; exact tt.
  Defined.

  Definition disp_prebicat_cells_unit_data : disp_prebicat_data C
    := _ ,, disp_prebicat_cells_unit_ops.

  Lemma disp_prebicat_cells_unit_laws
    : disp_prebicat_laws disp_prebicat_cells_unit_data.
  Proof.
    repeat use tpair; red; intros; apply (proofirrelevance _ isapropunit).
  Qed.

  Definition cell_unit_disp_prebicat : disp_prebicat C
    := _ ,, disp_prebicat_cells_unit_laws.

End Disp_Prebicat_Cells_Unit.

(* Local Notation "'SET'" := hset_category. *)
Arguments nat_trans_comp {C C' F G H} a b.

Section Cofunctormaps.

  Variable (K : category).

  Definition disp_presheaf : disp_prebicat prebicat_of_cats
    := presheaf_disp_prebicat K.

  Definition two_disp_presheaves : disp_prebicat prebicat_of_cats
    := dirprod_disp_prebicat disp_presheaf disp_presheaf.

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

  Definition morphisms_of_preshaves : disp_prebicat prebicat_of_cats.
  Proof.
    use sigma_prebicat.
    apply two_disp_presheaves.
    exact cofunctormaps_disp_prebicat.
  Defined.

End Cofunctormaps.
