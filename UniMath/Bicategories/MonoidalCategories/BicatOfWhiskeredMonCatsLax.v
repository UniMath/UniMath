(** **********************************************************

Ralph Matthes

August 2023
*)

(** **********************************************************

constructs the bicategory of whiskered monoidal categories
with lax monoidal functors as 1-cells

this is mostly a copy of [BicatOfWhiskeredMonCats]

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.

Section TheConstruction.

  Definition disp_monlaxbicat_disp_ob_mor : disp_cat_ob_mor bicat_of_cats.
  Proof.
    exists monoidal.
    exact (λ C D M N F, fmonoidal_lax M N F).
  Defined.

  Definition disp_monlaxbicat_disp_id_comp : disp_cat_id_comp bicat_of_cats disp_monlaxbicat_disp_ob_mor.
  Proof.
    split.
    - intros C F. apply identity_fmonoidal.
    - intros C D E F G M N O.
      apply comp_fmonoidal_lax.
  Defined.

  Definition disp_monlaxbicat_disp_catdata : disp_cat_data bicat_of_cats
    := (disp_monlaxbicat_disp_ob_mor,,disp_monlaxbicat_disp_id_comp).

  Definition bidisp_monlaxbicat_disp_2cell_struct : disp_2cell_struct disp_monlaxbicat_disp_ob_mor.
  Proof.
    intros C D F G α M N.
    exact (λ Fm Gm, is_mon_nat_trans (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax M N G) α).
  Defined.

  Lemma isaprop_bidisp_monlaxbicat_disp_2cell_struct
        {C D : bicat_of_cats}
        {F G : bicat_of_cats ⟦C,D⟧ }
        {α : prebicat_cells bicat_of_cats F G}
        {M : disp_monlaxbicat_disp_catdata C}
        {N : disp_monlaxbicat_disp_catdata D}
        (Fm : M -->[ F] N)
        (Gm : M -->[ G] N)
    : isaprop (bidisp_monlaxbicat_disp_2cell_struct C D F G α M N Fm Gm).
  Proof.
    apply isaprop_is_mon_nat_trans.
  Qed.

  Definition bidisp_monlaxbicat_disp_prebicat_1_id_comp_cells
    :  disp_prebicat_1_id_comp_cells bicat_of_cats
    := (disp_monlaxbicat_disp_catdata,, bidisp_monlaxbicat_disp_2cell_struct).

  Lemma bidisp_monlaxbicat_disp_prebicat_ops :
    disp_prebicat_ops bidisp_monlaxbicat_disp_prebicat_1_id_comp_cells.
  Proof.
    split.
    { intros; apply is_mon_nat_trans_identity. }
    repeat split; try red; cbn; unfold fmonoidal_preservestensordata, fmonoidal_preservesunit; intros; show_id_type.
    - rewrite functor_id.
      do 2 rewrite id_right.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in *.
             apply (bifunctor_leftid y).
           - cbn in *.
             apply (bifunctor_rightid y).
      }
      apply pathsinv0, id_left.
    - rewrite functor_id.
      rewrite id_right.
      apply id_right.
    - etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in *.
             apply (bifunctor_leftid y).
           - cbn in *.
             apply (bifunctor_rightid y).
      }
      apply id_right.
    - rewrite id_right.
      apply id_left.
    - etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in *.
             apply (bifunctor_leftid y).
           - cbn in *.
             apply (bifunctor_rightid y).
      }
      rewrite functor_id.
      apply pathsinv0, id_left.
    - rewrite functor_id.
      apply idpath.
    - etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in *.
             apply (bifunctor_leftid y).
           - cbn in *.
             apply (bifunctor_rightid y).
      }
      do 2 rewrite id_left.
      apply id_right.
    - rewrite id_left.
      apply id_right.
    - etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in *.
             apply (bifunctor_leftid z).
           - cbn in *.
             apply (bifunctor_rightid z).
      }
      rewrite id_right.
      rewrite id_left.
      repeat rewrite assoc'.
      apply maponpaths.
      apply functor_comp.
    - rewrite id_right.
      rewrite assoc'.
      apply maponpaths.
      apply functor_comp.
    - etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in *.
             apply (bifunctor_leftid z).
           - cbn in *.
             apply (bifunctor_rightid z).
      }
      rewrite id_right.
      rewrite id_left.
      repeat rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, functor_comp.
    - rewrite id_right.
      repeat rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, functor_comp.
    - apply (pr1 (is_mon_nat_trans_comp _ _ _ _ _ X X0)).
    - apply (pr2 (is_mon_nat_trans_comp _ _ _ _ _ X X0)).
    - assert (aux := pr1 X (pr1 f a0) (pr1 f a')).
      unfold fmonoidal_preservestensordata in aux.
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           exact aux. }
      clear aux.
      repeat rewrite assoc'.
      apply maponpaths.
      apply nat_trans_ax.
    - assert (aux := pr2 X).
      red in aux.
      unfold fmonoidal_preservesunit in aux.
      rewrite <- aux.
      repeat rewrite assoc'.
      apply maponpaths.
      apply nat_trans_ax.
    - etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, functor_comp. }
      etrans.
      { do 2 apply maponpaths.
        apply (pr1 X).
      }
      unfold fmonoidal_preservestensordata.
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, preservestensor_is_nattrans_full.
      + apply (fmonoidal_preservestensornatleft (gg : fmonoidal_lax _ _ g)).
      + apply (fmonoidal_preservestensornatright (gg : fmonoidal_lax _ _ g)).
    - rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply pathsinv0, functor_comp. }
      apply maponpaths.
      apply (pr2 X).
  Qed.

  Definition bidisp_monlaxbicat_disp_prebicat_data : disp_prebicat_data bicat_of_cats
    := (bidisp_monlaxbicat_disp_prebicat_1_id_comp_cells,, bidisp_monlaxbicat_disp_prebicat_ops).

  Definition bidisp_monlaxbicat_disp_prebicat_laws : disp_prebicat_laws bidisp_monlaxbicat_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isaprop_bidisp_monlaxbicat_disp_2cell_struct.
  Qed.

  Definition bidisp_monlaxbicat_disp_prebicat : disp_prebicat bicat_of_cats
    := (bidisp_monlaxbicat_disp_prebicat_data,,bidisp_monlaxbicat_disp_prebicat_laws).

  Definition bidisp_monlaxbicat_disp_bicat : disp_bicat bicat_of_cats.
  Proof.
    refine (bidisp_monlaxbicat_disp_prebicat,, _).
    intros C D F G α M N Fm Gm.
    apply isasetaprop.
    apply isaprop_bidisp_monlaxbicat_disp_2cell_struct.
  Defined.

  Lemma monlaxbicat_disp_2cells_isaprop : disp_2cells_isaprop bidisp_monlaxbicat_disp_bicat.
  Proof.
    red.
    intros.
    apply isaprop_bidisp_monlaxbicat_disp_2cell_struct.
  Qed.

  Definition monlaxbicat : bicat := total_bicat bidisp_monlaxbicat_disp_bicat.


End TheConstruction.

Definition monlaxbicat_disp_locally_groupoid : disp_locally_groupoid bidisp_monlaxbicat_disp_bicat.
Proof.
  red. intros C D F G αiso M N Fm Gm ismnt.
  use tpair.
  - transparent assert (isnziα : (is_nat_z_iso (pr11 αiso))).
    { apply (nat_trafo_pointwise_z_iso_if_z_iso (pr2 D)). exact (pr2 αiso). }
    exact (is_mon_nat_trans_pointwise_inverse (Fm : fmonoidal_lax _ _ _) (Gm : fmonoidal_lax _ _ _) (pr1 αiso) isnziα ismnt).
  - split; apply isaprop_bidisp_monlaxbicat_disp_2cell_struct.
Defined.
