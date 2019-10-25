(* ******************************************************************************* *)
(** * Displayed biequivalences give rise to equivalences on the fiber.
      This requires that the involved displayed bicategoies have propositions
      as displayed 2-cells, are locally groupoidal, and locally univalent.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Fibration.
Require Import UniMath.Bicategories.DisplayedBicats.FiberCategory.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition local_iso_cleaving_id
           {C : bicat}
           (HC : is_univalent_2_1 C)
           {D : disp_bicat C}
           (HD_2_1 : disp_univalent_2_1 D)
           (h : local_iso_cleaving D)
           (c : C)
           {xx  : D c}
           (p : xx -->[ id₁ c · id₁ c] xx)
           (α : disp_invertible_2cell (idempunitor c) (id_disp xx) p)
  : local_iso_cleaving_1cell
      h
      p
      (idempunitor c)
    =
    id_disp xx.
Proof.
  rewrite <- (idtoiso_2_1_isotoid_2_1 HC (idempunitor c)) in α.
  rewrite (transportb_transpose_right (disp_isotoid_2_1 _ HD_2_1 _ _ _ α)).
  pose (disp_local_iso_cleaving_invertible_2cell h p (idempunitor c)) as d.
  rewrite <- (idtoiso_2_1_isotoid_2_1 HC (idempunitor c)) in d.
  rewrite <- (idtoiso_2_1_isotoid_2_1 HC (idempunitor c)).
  rewrite (transportb_transpose_right (disp_isotoid_2_1 _ HD_2_1 _ _ _ d)).
  rewrite idtoiso_2_1_isotoid_2_1.
  apply idpath.
Qed.

Section FiberOfBiequiv.
  Context {C : bicat}
          (HC : is_univalent_2_1 C)
          {D₁ : disp_bicat C}
          (HD₁ : disp_2cells_isaprop D₁)
          (LGD₁ : disp_locally_groupoid D₁)
          (HD₁_2_1 : disp_univalent_2_1 D₁)
          (h₁ : local_iso_cleaving D₁)
          {D₂ : disp_bicat C}
          (HD₂ : disp_2cells_isaprop D₂)
          (LGD₂ : disp_locally_groupoid D₂)
          (HD₂_2_1 : disp_univalent_2_1 D₂)
          (h₂ : local_iso_cleaving D₂)
          {F : disp_psfunctor D₁ D₂ (id_psfunctor C)}
          {G : disp_psfunctor D₂ D₁ (id_psfunctor C)}
          (E : is_disp_biequivalence_unit_counit _ _ (id_is_biequivalence C) F G)
          (EE : disp_is_biequivalence_data _ _ (id_is_biequivalence C) E)
          (c : C).

  Local Notation "'FF'" := (fiber_functor HC HD₁ HD₁_2_1 h₁ HD₂ HD₂_2_1 h₂ F c).
  Local Notation "'GG'" := (fiber_functor HC HD₂ HD₂_2_1 h₂ HD₁ HD₁_2_1 h₁ G c).

  Definition help_equation
    : ((((((rinvunitor (id₁ c))
             • (id₁ c ◃ linvunitor (id₁ c)))
            • lassociator (id₁ c) (id₁ c) (id₁ c))
           • ((((lunitor (id₁ c) • rinvunitor (id₁ c))
                  • (id₁ c ◃ linvunitor (id₁ c)))
                 • lassociator (id₁ c) (id₁ c) (id₁ c)) ▹ id₁ c))
          • rassociator (id₁ c · id₁ c) (id₁ c) (id₁ c))
         • (id₁ c · id₁ c ◃ lunitor (id₁ c)))
        • runitor (id₁ c · id₁ c)
      =
      linvunitor (id₁ c).
  Proof.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor.
      rewrite !vassocl.
      apply id2_left.
    }
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    rewrite runitor_lunitor_identity.
    rewrite lunitor_linvunitor.
    rewrite lwhisker_hcomp.
    rewrite !vassocr.
    rewrite triangle_l_inv.
    rewrite <- !rwhisker_hcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      apply idpath.
    }
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    rewrite id2_right.
    rewrite !vassocl.
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    rewrite runitor_rwhisker.
    rewrite !vassocr.
    rewrite vcomp_whisker.
    rewrite !vassocl.
    refine (_ @ id2_right _).
    apply maponpaths.
    rewrite <- runitor_triangle.
    rewrite runitor_lunitor_identity.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_rwhisker.
    apply idpath.
  Qed.


  Definition fiber_unit_is_nat_trans
    : is_nat_trans
        (FF ∙ GG) (functor_identity _)
        (λ z, unit_of_is_disp_biequivalence _ _ E c z).
  Proof.
    intros z₁ z₂ f.
    refine (maponpaths (λ z, local_iso_cleaving_1cell h₁ z (idempunitor c)) _).
    cbn.
    pose (disp_psnaturality_of _ _ _ (unit_of_is_disp_biequivalence D₁ D₂ E) f) as d.
    simpl in d.
    rewrite <- (idtoiso_2_1_isotoid_2_1
                  HC
                  (psnaturality_of (lunitor_pstrans (id_psfunctor C)) (id₁ c))) in d.
    pose (transportb_transpose_right (disp_isotoid_2_1 _ HD₁_2_1 _ _ _ d)) as p.
    refine (_ @ !p).
    clear d p.
    refine (!_).
    assert (isotoid_2_1
              HC
              (psnaturality_of (lunitor_pstrans (id_psfunctor C)) (id₁ c))
            = idpath _) as X.
    {
      cbn.
      refine (_ @ isotoid_2_1_idtoiso_2_1 HC _).
      apply maponpaths.
      use subtypePath.
      { intro ; apply isaprop_is_invertible_2cell. }
      cbn.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor.
      apply idpath.
    }
    rewrite X.
    apply idpath.
  Qed.

  Definition fiber_unit
    : nat_trans (FF ∙ GG) (functor_identity _)
    := _ ,, fiber_unit_is_nat_trans.

  Definition fiber_unit_nat_iso
    : is_nat_iso fiber_unit.
  Proof.
    intros z.
    use is_iso_qinv.
    - exact (pr1 EE c z).
    - split.
      + apply local_iso_cleaving_id.
        * exact HC.
        * exact HD₁_2_1.
        * use tpair.
          ** apply ((pr12 (pr122 EE)) c z).
          ** apply (LGD₁ _ _ _ _ (_ ,, is_invertible_2cell_linvunitor (id₁ c))).
      + apply local_iso_cleaving_id.
        * exact HC.
        * exact HD₁_2_1.
        * use tpair.
          ** pose ((pr111 (pr22 EE)) c z) as m.
             simpl in m.
             pose (disp_inv_cell m) as d.
             refine (transportf (λ z, _ ==>[ z ] _)  _ d).
             exact help_equation.
          ** apply LGD₁.
  Qed.

  Definition fiber_unit_iso
    : nat_iso (FF ∙ GG) (functor_identity _)
    := (_ ,, fiber_unit_nat_iso).

  Definition fiber_counit_is_nat_trans
    : is_nat_trans
        (GG ∙ FF) (functor_identity _)
        (λ z, counit_of_is_disp_biequivalence _ _ E c z).
  Proof.
    intros z₁ z₂ f.
    refine (maponpaths (λ z, local_iso_cleaving_1cell h₂ z (idempunitor c)) _).
    cbn.
    pose (disp_psnaturality_of _ _ _ (counit_of_is_disp_biequivalence D₁ D₂ E) f) as d.
    simpl in d.
    rewrite <- (idtoiso_2_1_isotoid_2_1
                  HC
                  (psnaturality_of (lunitor_pstrans (id_psfunctor C)) (id₁ c))) in d.
    pose (transportb_transpose_right (disp_isotoid_2_1 _ HD₂_2_1 _ _ _ d)) as p.
    refine (_ @ !p).
    clear d p.
    refine (!_).
    assert (isotoid_2_1
              HC
              (psnaturality_of (lunitor_pstrans (id_psfunctor C)) (id₁ c))
            = idpath _) as X.
    {
      cbn.
      refine (_ @ isotoid_2_1_idtoiso_2_1 HC _).
      apply maponpaths.
      use subtypePath.
      { intro ; apply isaprop_is_invertible_2cell. }
      cbn.
      rewrite lunitor_runitor_identity.
      rewrite runitor_rinvunitor.
      apply idpath.
    }
    rewrite X.
    apply idpath.
  Qed.

  Definition fiber_counit
    : nat_trans (GG ∙ FF) (functor_identity _)
    := _ ,, fiber_counit_is_nat_trans.

  Definition fiber_counit_nat_iso
    : is_nat_iso fiber_counit.
  Proof.
    intros z.
    use is_iso_qinv.
    - exact (pr12 EE c z).
    - split.
      + apply local_iso_cleaving_id.
        * exact HC.
        * exact HD₂_2_1.
        * use tpair.
          ** apply (pr12 (pr222 EE) c z).
          ** apply (LGD₂ _ _ _ _ (_ ,, is_invertible_2cell_linvunitor (id₁ c))).
      + apply local_iso_cleaving_id.
        * exact HC.
        * exact HD₂_2_1.
        * use tpair.
          ** pose (pr11 (pr222 EE) c z) as m; simpl in m.
             simpl in m.
             pose (disp_inv_cell m) as d.
             refine (transportf (λ z, _ ==>[ z ] _)  _ d).
             exact help_equation.
          ** apply LGD₂.
  Qed.

  Definition fiber_counit_iso
    : nat_iso (GG ∙ FF) (functor_identity _)
    := (_ ,, fiber_counit_nat_iso).

  Definition fiber_equivalence
    : equivalence_of_precats
        (discrete_fiber_category D₁ HD₁ HD₁_2_1 h₁ c)
        (discrete_fiber_category D₂ HD₂ HD₂_2_1 h₂ c).
  Proof.
    simple refine ((FF ,, (GG ,, (_ ,, _))) ,, (_ ,, _)).
    - exact (pr1 (nat_iso_inv fiber_unit_iso)).
    - exact (pr1 fiber_counit_iso).
    - exact (pr2 (nat_iso_inv fiber_unit_iso)).
    - exact (pr2 fiber_counit_iso).
  Defined.
End FiberOfBiequiv.
