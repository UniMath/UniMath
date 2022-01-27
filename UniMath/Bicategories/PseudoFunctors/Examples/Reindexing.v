Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.FibSlice.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FibrationCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.OpFibrationCleaving.

Local Open Scope cat.

Section ReindexFib.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (F : C₁ --> C₂).

  Definition reindex_fib_psfunctor_data
    : psfunctor_data
        (fib_slice_bicat C₂)
        (fib_slice_bicat C₁).
  Proof.
    use make_psfunctor_data.
    - exact (λ D, cleaving_of_fibs_lift_obj D F).
    - exact (λ D₁ D₂ G, reindex_of_cartesian_disp_functor F G (pr2 D₁)).
    - exact (λ D₁ D₂ G₁ G₂ α, reindex_of_disp_nat_trans F α).
    - exact (λ D, reindex_of_disp_functor_identity F (pr1 D)).
    - exact (λ D₁ D₂ D₃ G₁ G₂, reindex_of_disp_functor_composite F (pr1 G₁) (pr1 G₂)).
  Defined.

  Definition reindex_fib_psfunctor_laws
    : psfunctor_laws reindex_fib_psfunctor_data.
  Proof.
    repeat split.
    - intros D₁ D₂ G.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      apply idpath.
    - intros D₁ D₂ G₁ G₂ G₃ α β.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ G.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !id_right_disp.
      unfold transportb.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_functor_transportf _ (pr1 G)).
      }
      rewrite transport_f_f.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ G.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !id_right_disp.
      unfold transportb.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ D₄ G₁ G₂ G₃.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      rewrite id_left_disp.
      etrans.
      {
        do 4 apply maponpaths.
        apply (disp_functor_transportf _ (pr1 G₃)).
      }
      rewrite disp_functor_id.
      unfold transportb.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ G H₁ H₂ α.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      etrans.
      {
        apply transportf_reindex.
      }
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ G₁ G₂ H α.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      etrans.
      {
        apply transportf_reindex.
      }
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_functor_transportf _ (pr1 H)).
      }
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition reindex_fib_psfunctor_invertible_cells
    : invertible_cells reindex_fib_psfunctor_data.
  Proof.
    repeat split.
    - intro D.
      use is_invertible_2cell_fib_slice.
      intros x xx.
      apply (@id_is_iso_disp _ (reindex_disp_cat F (pr1 D))).
    - intros D₁ D₂ D₃ G₁ G₂.
      use is_invertible_2cell_fib_slice.
      intros x xx.
      apply (@id_is_iso_disp _ (reindex_disp_cat F (pr1 D₃))).
  Defined.

  Definition reindex_fib_psfunctor
    : psfunctor
        (fib_slice_bicat C₂)
        (fib_slice_bicat C₁).
  Proof.
    use make_psfunctor.
    - exact reindex_fib_psfunctor_data.
    - exact reindex_fib_psfunctor_laws.
    - exact reindex_fib_psfunctor_invertible_cells.
  Defined.
End ReindexFib.

Section ReindexOpFib.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (F : C₁ --> C₂).

  Definition reindex_opfib_psfunctor_data
    : psfunctor_data
        (opfib_slice_bicat C₂)
        (opfib_slice_bicat C₁).
  Proof.
    use make_psfunctor_data.
    - exact (λ D, cleaving_of_opfibs_lift_obj D F).
    - exact (λ D₁ D₂ G, reindex_of_opcartesian_disp_functor F G (pr2 D₁)).
    - exact (λ D₁ D₂ G₁ G₂ α, reindex_of_disp_nat_trans F α).
    - exact (λ D, reindex_of_disp_functor_identity F (pr1 D)).
    - exact (λ D₁ D₂ D₃ G₁ G₂, reindex_of_disp_functor_composite F (pr1 G₁) (pr1 G₂)).
  Defined.

  Definition reindex_opfib_psfunctor_laws
    : psfunctor_laws reindex_opfib_psfunctor_data.
  Proof.
    repeat split.
    - intros D₁ D₂ G.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      apply idpath.
    - intros D₁ D₂ G₁ G₂ G₃ α β.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ G.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !id_right_disp.
      unfold transportb.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_functor_transportf _ (pr1 G)).
      }
      rewrite transport_f_f.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ G.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !id_right_disp.
      unfold transportb.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ D₄ G₁ G₂ G₃.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      rewrite !id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      rewrite id_left_disp.
      etrans.
      {
        do 4 apply maponpaths.
        apply (disp_functor_transportf _ (pr1 G₃)).
      }
      rewrite disp_functor_id.
      unfold transportb.
      etrans.
      {
        apply maponpaths.
        apply transportf_reindex.
      }
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ G H₁ H₂ α.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      etrans.
      {
        apply transportf_reindex.
      }
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    - intros D₁ D₂ D₃ G₁ G₂ H α.
      use disp_nat_trans_eq.
      intros x xx ; cbn.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !mor_disp_transportf_postwhisker.
      etrans.
      {
        apply transportf_reindex.
      }
      refine (!_).
      etrans.
      {
        apply transportf_reindex.
      }
      rewrite id_left_disp, id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply (disp_functor_transportf _ (pr1 H)).
      }
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition reindex_opfib_psfunctor_invertible_cells
    : invertible_cells reindex_opfib_psfunctor_data.
  Proof.
    repeat split.
    - intro D.
      use is_invertible_2cell_opfib_slice.
      intros x xx.
      apply (@id_is_iso_disp _ (reindex_disp_cat F (pr1 D))).
    - intros D₁ D₂ D₃ G₁ G₂.
      use is_invertible_2cell_opfib_slice.
      intros x xx.
      apply (@id_is_iso_disp _ (reindex_disp_cat F (pr1 D₃))).
  Defined.

  Definition reindex_opfib_psfunctor
    : psfunctor
        (opfib_slice_bicat C₂)
        (opfib_slice_bicat C₁).
  Proof.
    use make_psfunctor.
    - exact reindex_opfib_psfunctor_data.
    - exact reindex_opfib_psfunctor_laws.
    - exact reindex_opfib_psfunctor_invertible_cells.
  Defined.
End ReindexOpFib.
