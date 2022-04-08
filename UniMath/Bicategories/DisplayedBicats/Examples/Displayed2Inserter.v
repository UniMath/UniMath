Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.

Section DispTwoInserter.
  Context {B C : bicat}
          {F G : psfunctor B C}
          (α β : pstrans F G).

  Definition disp_two_inserter_disp_cat
    : disp_cat_ob_mor B.
  Proof.
    use make_disp_cat_ob_mor.
    - exact (λ x , α x ==> β x).
    - exact (λ x y θ τ f, (θ ▹ #G f) • psnaturality_of β f
                          =
                          psnaturality_of α f • (#F f ◃ τ)).
  Defined.

  Definition disp_two_inserter_disp_cat_id_comp
    : disp_cat_id_comp _ disp_two_inserter_disp_cat.
  Proof.
    use tpair ; simpl.
    - intros x xx.
      rewrite !pstrans_id_alt.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_runitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    - intros x y z f g xx yy zz p q.
      rewrite !pstrans_comp_alt.
      etrans.
      {
        rewrite !vassocr.
        rewrite vcomp_whisker.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !vassocl.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocr.
        apply idpath.
      }
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite <- q.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      rewrite p.
      apply idpath.
  Qed.

  Definition disp_two_inserter_disp_cat_data
    : disp_cat_data B.
  Proof.
    use tpair.
    - exact disp_two_inserter_disp_cat.
    - exact disp_two_inserter_disp_cat_id_comp.
  Defined.

  Definition disp_two_inserter_prebicat : disp_prebicat B
    := disp_cell_unit_bicat disp_two_inserter_disp_cat_data.

  Definition disp_two_inserter_bicat : disp_bicat B
    := disp_cell_unit_bicat disp_two_inserter_disp_cat_data.

  Definition disp_two_inserter_univalent_2_1
    : disp_univalent_2_1 disp_two_inserter_bicat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_1.
    intros.
    apply C.
  Defined.

  Definition disp_two_inserter_univalent_2_0
             (HB : is_univalent_2_1 B)
    : disp_univalent_2_0 disp_two_inserter_bicat.
  Proof.
    use disp_cell_unit_bicat_univalent_2_0.
    - exact HB.
    - intros ; apply C.
    - simpl ; intro.
      apply C.
    - simpl ; intros x xx yy p.
      induction p as [p₁ p₂].
      rewrite !pstrans_id_alt in p₁.
      rewrite !vassocr in p₁.
      rewrite vcomp_whisker in p₁.
      rewrite !vassocl in p₁.
      assert (H : is_invertible_2cell (α x ◃ (psfunctor_id G x) ^-1)) by is_iso.
      assert (q₁ := vcomp_lcancel _ H p₁) ; clear p₁ H.
      cbn -[psfunctor_id] in q₁.
      rewrite vcomp_whisker in q₁.
      rewrite !vassocr in q₁.
      assert (H : is_invertible_2cell (psfunctor_id F x ▹ β x)).
      {
        is_iso.
        apply psfunctor_id.
      }
      assert (q₁' := vcomp_rcancel _ H q₁) ; clear q₁ H.
      rewrite vcomp_runitor in q₁'.
      rewrite !vassocl in q₁'.
      assert (H : is_invertible_2cell (runitor (α x))) by is_iso.
      assert (q₁'' := vcomp_lcancel _ H q₁') ; clear H q₁'.
      rewrite lwhisker_hcomp in q₁''.
      rewrite <- linvunitor_natural in q₁''.
      assert (H : is_invertible_2cell (linvunitor (β x))) by is_iso.
      assert (q₁''' := vcomp_rcancel _ H q₁'') ; clear H q₁''.
      exact q₁'''.
  Qed.

  Definition disp_two_inserter_cells_isaprop
    : disp_2cells_isaprop disp_two_inserter_bicat.
  Proof.
    intro; intros; exact isapropunit.
  Qed.

  Definition disp_two_inserter_locally_groupoid
    : disp_locally_groupoid disp_two_inserter_bicat.
  Proof.
    use make_disp_locally_groupoid.
    - intro ; intros.
      exact tt.
    - exact disp_two_inserter_cells_isaprop.
  Qed.
End DispTwoInserter.
