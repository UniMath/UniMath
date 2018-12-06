Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Projection.
  Context {C : bicat}.
  Variable (D : disp_prebicat C).

  Definition pr1_psfunctor_ob_mor_cell : laxfunctor_ob_mor_cell (total_prebicat_data D) C.
  Proof.
    use tpair.
    - use tpair.
      + exact pr1.
      + intros a b. exact pr1.
    - intros a b f g. exact pr1.
  Defined.

  Definition pr1_psfunctor_cell_data : laxfunctor_cell_data pr1_psfunctor_ob_mor_cell.
  Proof.
    use tpair.
    - intro a. cbn.
      apply id2_invertible_2cell.
    - cbn. intros a b c f g.
      apply id2_invertible_2cell.
  Defined.

  Definition pr1_psfunctor_data : laxfunctor_data (total_prebicat_data D) C
    := pr1_psfunctor_ob_mor_cell ,, pr1_psfunctor_cell_data.

  Definition pr1_psfunctor_laws : laxfunctor_laws pr1_psfunctor_data.
  Proof.
    repeat split; intro a; intros; cbn.
    - rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite id2_left.
      apply idpath.
    - rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite id2_left.
      apply idpath.
    - rewrite !lwhisker_id2, !id2_rwhisker.
      rewrite !id2_left, !id2_right.
      apply idpath.
    - rewrite id2_right.
      rewrite id2_left.
      apply idpath.
    - rewrite id2_left.
      rewrite id2_right.
      apply idpath.
  Qed.

  Definition pr1_laxfunctor : laxfunctor (total_prebicat_data D) C
    := _ ,, pr1_psfunctor_laws.

  Definition pr1_is_pseudofunctor : is_pseudofunctor pr1_laxfunctor.
  Proof.
    split ; cbn ; intros ; is_iso.
  Defined.

  Definition pr1_psfunctor : psfunctor (total_prebicat_data D) C
    := _ ,, pr1_is_pseudofunctor.
End Projection.