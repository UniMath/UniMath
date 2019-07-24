(* ------------------------------------------------------------------------- *)
(** Displayed biequivalence.                                                 *)
(* ------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Initial.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Final.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.

Import PseudoFunctor.Notations.

Local Open Scope cat.

Opaque ps_comp.

Definition is_psfunctor_eq_to_pstrans_data
           {B₁ B₂ : bicat}
           (F : psfunctor_data B₁ B₂)
           (HF₁ HF₂ : is_psfunctor F)
  : pstrans_data (F,,HF₁) (F,,HF₂).
Proof.
  use make_pstrans_data.
  + intros x.
    exact (id₁ _).
  + intros x y f. cbn.
    use make_invertible_2cell.
    * exact (lunitor _ • rinvunitor _).
    * is_iso.
Defined.

Lemma is_psfunctor_eq_to_pstrans_is_pstrans
      {B₁ B₂ : bicat}
      (F : psfunctor_data B₁ B₂)
      (HF₁ HF₂ : is_psfunctor F)
  : is_pstrans (is_psfunctor_eq_to_pstrans_data F HF₁ HF₂).
Proof.
  repeat split; cbn.
  - intros x y f g α.
    rewrite vassocr. rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite rinvunitor_natural.
    rewrite rwhisker_hcomp.
    apply idpath.
  - intros x.
    rewrite vassocr. rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite rinvunitor_natural.
    rewrite rwhisker_hcomp.
    rewrite lunitor_runitor_identity.
    rewrite lunitor_V_id_is_left_unit_V_id.
    apply idpath.
  - intros x y z f g.
    rewrite vassocr. rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite rinvunitor_natural.
    rewrite <- rwhisker_hcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite <- rwhisker_vcomp.
    rewrite <- lunitor_triangle.
    rewrite !vassocl.
    do 2 apply maponpaths.
    rewrite <- rinvunitor_triangle.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite <- lwhisker_vcomp.
    symmetry.
    etrans.
    {
      rewrite !vassocl.
      apply maponpaths.
      rewrite vassocr.
      rewrite lunitor_lwhisker.
      apply idpath.
    }
    rewrite vassocr.
    rewrite rwhisker_vcomp.
    rewrite rinvunitor_runitor.
    rewrite id2_rwhisker.
    rewrite id2_left.
    apply idpath.
Qed.

Definition is_psfunctor_eq_to_pstrans
           {B₁ B₂ : bicat}
           (F : psfunctor_data B₁ B₂)
           (HF₁ HF₂ : is_psfunctor F)
  : pstrans (F,,HF₁) (F,,HF₂).
Proof.
  use make_pstrans.
  - apply is_psfunctor_eq_to_pstrans_data.
  - apply is_psfunctor_eq_to_pstrans_is_pstrans.
Defined.

Section DisplayedBiequivalece.

Context {B₁ B₂ : bicat}
        (D₁ : disp_bicat B₁)
        (D₂ : disp_bicat B₂).

Definition is_disp_biequivalence_unit_counit
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           (e : is_biequivalence_unit_counit F G)
           (FF : disp_psfunctor D₁ D₂ F) (GG : disp_psfunctor D₂ D₁ G)
  : UU
  := disp_pstrans (disp_pseudo_comp F G D₁ D₂ D₁ FF GG)
                  (disp_pseudo_id D₁)
                  (unit_of_is_biequivalence e) ×
     disp_pstrans (disp_pseudo_comp G F D₂ D₁ D₂ GG FF)
                  (disp_pseudo_id D₂)
                  (counit_of_is_biequivalence e).

Definition unit_of_is_disp_biequivalence
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : disp_pstrans (disp_pseudo_comp F G D₁ D₂ D₁ FF GG)
                 (disp_pseudo_id D₁) (unit_of_is_biequivalence e)
  := pr1 ee.

Definition counit_of_is_disp_biequivalence
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : disp_pstrans (disp_pseudo_comp G F D₂ D₁ D₂ GG FF)
                 (disp_pseudo_id D₂)
                 (counit_of_is_biequivalence e)
  := pr2 ee.

Definition total_is_biequivalence_unit_counit
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : is_biequivalence_unit_counit (total_psfunctor _ _ _ FF)
                                 (total_psfunctor _ _ _ GG).
Proof.
  split.
  - pose (unit_of_is_disp_biequivalence ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    refine (comp_trans _ (comp_trans tuu _)).
    + apply is_psfunctor_eq_to_pstrans.
    + apply is_psfunctor_eq_to_pstrans.
  - pose (counit_of_is_disp_biequivalence ee) as uu.
    pose (total_pstrans _ _ _ uu) as tuu.
    refine (comp_trans _ (comp_trans tuu _)).
    + apply is_psfunctor_eq_to_pstrans.
    + apply is_psfunctor_eq_to_pstrans.
Defined.


Definition disp_is_biequivalence_data
           {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
           {e : is_biequivalence_unit_counit F G}
           (a : is_biequivalence_adjoints e)
           {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
           (ee : is_disp_biequivalence_unit_counit e FF GG)
  : UU.

  simple refine
         (∑ uu : disp_pstrans (disp_pseudo_id D₁)
                              (disp_pseudo_comp _ _ _ _ _ FF GG)
                              (invunit_of_is_biequivalence a),
                 _).
  simple refine
         (∑ cc : disp_pstrans (disp_pseudo_id D₂)
                              (disp_pseudo_comp _ _ _ _ _ GG FF)
                              (invcounit_of_is_biequivalence a),
                 _).
  simple refine
    (∑ mpuu : disp_invmodification _ _ _ _
                                   (disp_ps_comp _ _ _ _ _ _ _ _ _ _
                                                 uu
                                                 (unit_of_is_disp_biequivalence ee))
                                   (disp_id_trans _)
                                   (unitcounit_of_is_biequivalence _ ),_).
  simple refine
    (∑ mquu : disp_invmodification _ _ _ _
                                   (disp_ps_comp _ _ _ _ _ _ _ _ _ _
                                                 (unit_of_is_disp_biequivalence ee)
                                                 uu)
                                   (disp_id_trans _)
                                   (unitunit_of_is_biequivalence _ ),_).
  simple refine
    (∑ mpcc : disp_invmodification _ _ _ _
                                   (disp_ps_comp _ _ _ _ _ _ _ _ _ _
                                                 cc
                                                 (counit_of_is_disp_biequivalence ee))
                                   (disp_id_trans _)
                                   (counitcounit_of_is_biequivalence _ ),_).
  exact (disp_invmodification _ _ _ _
                              (disp_ps_comp _ _ _ _ _ _ _ _ _ _
                                            (counit_of_is_disp_biequivalence ee)
                                            cc)
                              (disp_id_trans _)
                              (counitunit_of_is_biequivalence _ )).
Defined.


Section total_biequivalence.

Context {F : psfunctor B₁ B₂} {G : psfunctor B₂ B₁}
        {e : is_biequivalence_unit_counit F G}
        (a : is_biequivalence_adjoints e)
        {FF : disp_psfunctor D₁ D₂ F} {GG : disp_psfunctor D₂ D₁ G}
        {ee : is_disp_biequivalence_unit_counit e FF GG}
        (aa : disp_is_biequivalence_data a ee).

Definition total_biequivalence_unit_inv
  : pstrans (ps_id_functor (total_bicat D₁))
            (ps_comp (total_psfunctor D₂ D₁ G GG) (total_psfunctor D₁ D₂ F FF)).
Proof.
  pose (pr1 aa) as aapr.
  pose (total_pstrans _ _ _ aapr) as taapr.
  refine (comp_trans _ (comp_trans taapr _)).
  - apply is_psfunctor_eq_to_pstrans.
  - apply is_psfunctor_eq_to_pstrans.
Defined.

Definition total_biequivalence_counit_inv
  : pstrans (ps_id_functor (total_bicat D₂))
            (ps_comp (total_psfunctor D₁ D₂ F FF) (total_psfunctor D₂ D₁ G GG)).
Proof.
  pose (pr12 aa) as aapr.
  pose (total_pstrans _ _ _ aapr) as taapr.
  refine (comp_trans _ (comp_trans taapr _)).
  - apply is_psfunctor_eq_to_pstrans.
  - apply is_psfunctor_eq_to_pstrans.
Defined.

Definition total_is_biequivalence
  : is_biequivalence (total_psfunctor _ _ _ FF).
Proof.

  use make_is_biequivalence_from_unit_counit.
  - exact (total_psfunctor _ _ _ GG).
  - exact (total_is_biequivalence_unit_counit ee).
  - exact total_biequivalence_unit_inv.
  - exact total_biequivalence_counit_inv.

  - pose (pr122 aa) as aapr.
    pose (total_invmodification _ _ _ _ _ _ _ aapr) as taapr.
Abort.

End total_biequivalence.