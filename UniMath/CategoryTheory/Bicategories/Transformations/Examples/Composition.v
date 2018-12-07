(**
Composition of lax transformations gives another transformation.
In addition, if both are pseudo transformations, then the composition is a pseudotransformation as well.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.LaxTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.

Local Open Scope cat.

Section Composition.
  Context {C D : bicat}
          {F₁ F₂ F₃ : psfunctor C D}.
  Variable (σ₁ : laxtrans F₁ F₂) (σ₂ : laxtrans F₂ F₃).

  Definition comp_data : laxtrans_data F₁ F₃.
  Proof.
    use mk_laxtrans_data.
    - exact (λ X, σ₁ X · σ₂ X).
    - exact (λ X Y f,
             (rassociator (σ₁ X) (σ₂ X) (#F₃ f))
               • (σ₁ X ◃ laxnaturality_of σ₂ f)
               • lassociator (σ₁ X) (#F₂ f) (σ₂ Y)
               • (laxnaturality_of σ₁ f ▹ σ₂ Y)
               • rassociator (#F₁ f) (σ₁ Y) (σ₂ Y)).
  Defined.

  Definition comp_laws
    : is_laxtrans comp_data.
  Proof.
    repeat split.
    - intros X Y f g α ; cbn in *.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      pose (laxnaturality_natural σ₁).
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite <- laxnaturality_natural.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !rwhisker_vcomp.
      rewrite laxnaturality_natural.
      reflexivity.
    - intros X ; cbn.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_vcomp.
      rewrite laxtrans_id.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite runitor_triangle.
      rewrite !vassocl.
      apply maponpaths.
      pose (laxtrans_id σ₁).
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite rwhisker_vcomp.
      rewrite laxtrans_id.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor, id2_rwhisker, id2_left.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite linvunitor_assoc.
      reflexivity.
    - intros X Y Z f g ; cbn.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocr.
      assert ((lassociator (σ₁ X · σ₂ X) (# F₃ f) (# F₃ g))
                • (rassociator (σ₁ X) (σ₂ X) (# F₃ f) ▹ # F₃ g)
              =
              (rassociator (σ₁ X) (σ₂ X) (#F₃ f · #F₃ g))
                • (σ₁ X ◃ lassociator (σ₂ X) (# F₃ f) (# F₃ g))
                • lassociator (σ₁ X) (σ₂ X · # F₃ f) (# F₃ g)) as ->.
      {
        rewrite !vassocl.
        use vcomp_move_L_pM.
        { is_iso. }
        cbn.
        rewrite !vassocr.
        rewrite !lwhisker_hcomp, !rwhisker_hcomp.
        rewrite pentagon_2.
        rewrite !vassocl.
        reflexivity.
      }
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !(maponpaths
                  (λ z, _ • (_ • (_ • (_ • (_ • (_ • (_ • (_ • (_ • (_ • (_ • z)))))))))))
                  (vassocr _ _ _)).
      pose (inverse_pentagon_5 (σ₂ Z) (σ₁ Z) (#F₁ g) (#F₁ f)) as pent.
      rewrite <- !lwhisker_hcomp, <- !rwhisker_hcomp in pent.
      rewrite pent ; clear pent.
      rewrite !vassocl.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite laxtrans_comp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      refine (!(_ @ _)).
      {
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 11 apply maponpaths_2.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        rewrite !vassocl.
        exact (!(pentagon (#F₃ g) (σ₂ Y) (#F₂ f) (σ₁ X))).
      }
      rewrite !vassocl.
      refine (!(_ @ _)).
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
        rewrite rwhisker_vcomp.
        rewrite laxtrans_comp.
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocl.
        reflexivity.
      }
      rewrite !vassocr.
      repeat (apply maponpaths_2).
      rewrite !vassocl.
      rewrite rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      use vcomp_move_L_Mp.
      { is_iso. }
      use vcomp_move_L_Mp.
      { is_iso. }
      cbn.
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        rewrite <- inverse_pentagon.
        reflexivity.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        reflexivity.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !(maponpaths (λ z, z • _) (vassocl _ _ _)).
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        rewrite <- pentagon.
        rewrite !vassocl.
        rewrite lassociator_rassociator, id2_right.
        reflexivity.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      refine (!(_ @ _)).
      {
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        rewrite <- inverse_pentagon.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_lwhisker_rassociator.
      reflexivity.
  Qed.

  Definition comp_laxtrans : laxtrans F₁ F₃
    := mk_laxtrans comp_data comp_laws.
End Composition.

Definition comp_trans
           {C D : bicat}
           {F₁ F₂ F₃ : psfunctor C D}
           (σ₁ : pstrans F₁ F₂) (σ₂ : pstrans F₂ F₃)
  : pstrans F₁ F₃.
Proof.
  use mk_pstrans.
  - exact (comp_laxtrans σ₁ σ₂).
  - intros X Y f ; cbn.
    is_iso.
    + apply σ₂.
    + apply σ₁.
Defined.