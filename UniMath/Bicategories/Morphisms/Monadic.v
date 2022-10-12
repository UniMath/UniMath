(*********************************************************************************


 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.Examples.AdjunctionToMonad.

Local Open Scope cat.

Section Monadic.
  Context {B : bicat}
          (HB : bicat_has_em B)
          {x y : B}
          (l : adjunction x y).

  Let r : y --> x := left_adjoint_right_adjoint l.
  Let η : id₁ _ ==> l · r := left_adjoint_unit l.
  Let ε : r · l ==> id₁ _ := left_adjoint_counit l.

  Let m : mnd B := mnd_from_adjunction l.

  Let e : em_cone m := pr1 (HB m).
  Let He : has_em_ump _ e := pr2 (HB m).

  Local Definition comparison_mor_cone_cell
    : l · r · endo_of_mnd m ==> id₁ x · (l · r)
    := rassociator _ _ _
       • (_ ◃ (lassociator _ _ _ • (ε ▹ r) • lunitor _))
       • linvunitor _.

  Local Definition comparison_mor_cone_unit
    : linvunitor (l · r)
      =
      (rinvunitor (l · r) • (l · r ◃ η)) • comparison_mor_cone_cell.
  Proof.
    unfold comparison_mor_cone_cell.
    refine (!(id2_left _) @ _).
    rewrite !vassocr.
    apply maponpaths_2.
    refine (!_).
    rewrite <- rinvunitor_triangle.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !lwhisker_vcomp.
    refine (_ @ lwhisker_id2 _ _).
    apply maponpaths.
    rewrite !vassocr.
    exact (internal_triangle2 l).
  Qed.

  Local Definition comparison_mor_cone_mult
    : lassociator _ (l · r) (l · r)
      • (comparison_mor_cone_cell ▹ (l · r))
      • (lunitor (l · r) ▹ (l · r))
      • comparison_mor_cone_cell
      =
      (l · r ◃ mult_of_mnd m)
      • comparison_mor_cone_cell.
  Proof.
    unfold comparison_mor_cone_cell.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    do 5 apply maponpaths_2.
    rewrite !vassocl.
    rewrite rwhisker_vcomp.
    rewrite linvunitor_lunitor.
    rewrite id2_rwhisker.
    rewrite id2_right.
    rewrite !vassocr.
    rewrite inverse_pentagon_7.
    rewrite !vassocl.
    use vcomp_move_R_pM ; [ is_iso | ].
    refine (_ @ lwhisker_lwhisker _ _ _).
    etrans.
    {
      apply maponpaths.
      rewrite !rwhisker_vcomp, !lwhisker_vcomp.
      rewrite <- rwhisker_lwhisker.
      rewrite <- !rwhisker_vcomp.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !lwhisker_vcomp.
    apply maponpaths.
    cbn.
    rewrite !vassocl.
    rewrite <- !lwhisker_vcomp.
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite !vassocr.
    rewrite lassociator_lassociator.
    rewrite !vassocl.
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite !vassocr.
    rewrite lwhisker_lwhisker.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_hcomp.
      rewrite inverse_pentagon_5.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      apply idpath.
    }
    use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
    rewrite !lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lwhisker_lwhisker_rassociator.
    rewrite !vassocl.
    rewrite !rwhisker_vcomp.
    rewrite <- rwhisker_rwhisker_alt.
    rewrite !vassocr.
    apply maponpaths_2.


    enough (lassociator (r · l) (r · l) r
            • (lassociator (r · l) r l ▹ r)
            • ((((ε ▹ r) • lunitor r) ▹ l) ▹ r)
            =
              r · l ◃ ((ε ▹ r) • lunitor r)).
    {
      exact X.
    }
    rewrite !vassocl.
    rewrite rwhisker_vcomp.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      rewrite lunitor_triangle.
      apply idpath.
    }
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite rwhisker_rwhisker.
    rewrite !vassocl.
    rewrite lunitor_triangle.
    rewrite <- lwhisker_vcomp.


    Check internal_triangle2 l.

    refine (!_).

    refine (_ @ id2_right _).
    rewrite <- lwhisker_id2.
    rewrite !lwhisker_vcomp.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact (!(internal_triangle2 l)).
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    refine (_ @ id2_left _).
    apply maponpaths_2.
    rewrite !vassocl.
    Check internal_triangle1 l.
    rewrite <- lunitor_triangle.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !lwhisker_vcomp.
      rewrite vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite <- rwhisker_rwhisker.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    rewrite <- lwhisker_lwhisker.

  Admitted.

  Definition comparison_mor_cone
    : em_cone m.
  Proof.
    use make_em_cone.
    - exact x.
    - exact (l · r).
    - exact comparison_mor_cone_cell.
    - exact comparison_mor_cone_unit.
    - exact comparison_mor_cone_mult.
  Defined.

  Definition comparison_mor
    : x --> e
    := em_ump_1_mor _ He comparison_mor_cone.

  Definition is_monadic
    : UU
    := left_adjoint_equivalence comparison_mor.
End Monadic.
