(**********************************************************************************

 The double category of spans

 In this file, we define the double category of spans. If `C` is a category with
 pullbacks, then we have the following double category:
 - Objects: objects in `C`
 - Vertical morphisms: morphisms in `C`
 - Horizontal morphisms: spans in `C`
 - Squares: morphisms of spans
 Spans are composed by taking a pullback.

 Contents
 1. Horizontal identities
 2. Horizontal composition
 3. The unitors and associators
 4. The triangle and pentagon equations
 5. The double category of spans

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Spans.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.PseudoDoubleSetCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.
Local Open Scope double_cat.

Section SpansDoubleCat.
  Context {C : category}
          (PC : Pullbacks C).

  (** * 1. Horizontal identities *)
  Definition spans_double_cat_hor_id_data
    : hor_id_data (twosided_disp_cat_of_spans C).
  Proof.
    use make_hor_id_data.
    - exact (id_span C).
    - exact (λ x y f, id_span_mor C f).
  Defined.

  Proposition spans_double_cat_hor_id_laws
    : hor_id_laws spans_double_cat_hor_id_data.
  Proof.
    split.
    - intros a.
      use span_sqr_eq ; cbn.
      apply idpath.
    - intros a₁ a₂ a₃ f g.
      use span_sqr_eq ; cbn.
      apply idpath.
  Qed.

  Definition spans_double_cat_hor_id
    : hor_id (twosided_disp_cat_of_spans C).
  Proof.
    use make_hor_id.
    - exact spans_double_cat_hor_id_data.
    - exact spans_double_cat_hor_id_laws.
  Defined.

  (** * 2. Horizontal composition *)
  Definition spans_double_cat_hor_comp_data
    : hor_comp_data (twosided_disp_cat_of_spans C).
  Proof.
    use make_hor_comp_data.
    - exact (λ a₁ a₂ a₃ s t, comp_span C PC s t).
    - exact (λ _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂, comp_span_mor C PC s₁ s₂).
  Defined.

  Proposition spans_double_cat_hor_comp_laws
    : hor_comp_laws spans_double_cat_hor_comp_data.
  Proof.
    split.
    - intros a₁ a₂ a₃ h₁ h₂.
      use span_sqr_eq.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
      + unfold mor_of_comp_span_mor.
        rewrite PullbackArrow_PullbackPr1 ; cbn.
        rewrite id_left, id_right.
        apply idpath.
      + unfold mor_of_comp_span_mor.
        rewrite PullbackArrow_PullbackPr2 ; cbn.
        rewrite id_left, id_right.
        apply idpath.
    - intros.
      use span_sqr_eq.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
      + rewrite !assoc'.
        unfold mor_of_comp_span_mor.
        rewrite !PullbackArrow_PullbackPr1 ; cbn.
        rewrite !assoc.
        rewrite !PullbackArrow_PullbackPr1.
        rewrite !assoc'.
        apply idpath.
      + rewrite !assoc'.
        unfold mor_of_comp_span_mor.
        rewrite !PullbackArrow_PullbackPr2 ; cbn.
        rewrite !assoc.
        rewrite !PullbackArrow_PullbackPr2.
        rewrite !assoc'.
        apply idpath.
  Qed.

  Definition spans_double_cat_hor_comp
    : hor_comp (twosided_disp_cat_of_spans C).
  Proof.
    use make_hor_comp.
    - exact spans_double_cat_hor_comp_data.
    - exact spans_double_cat_hor_comp_laws.
  Defined.

  (** * 3. The unitors and associators *)
  Definition spans_double_cat_lunitor_data
    : double_lunitor_data
        spans_double_cat_hor_id
        spans_double_cat_hor_comp.
  Proof.
    intros x y h.
    simple refine (_ ,, _).
    - exact (span_lunitor C PC h).
    - use is_iso_twosided_disp_span_sqr ; cbn.
      apply is_z_iso_span_lunitor_mor.
  Defined.

  Proposition spans_double_cat_lunitor_laws
    : double_lunitor_laws spans_double_cat_lunitor_data.
  Proof.
    intros x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ sq.
    use span_sqr_eq.
    rewrite transportb_disp_mor2_span ; cbn.
    unfold span_lunitor_mor, mor_of_comp_span_mor.
    rewrite PullbackArrow_PullbackPr2.
    apply idpath.
  Qed.

  Definition spans_double_cat_lunitor
    : double_cat_lunitor
        spans_double_cat_hor_id
        spans_double_cat_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact spans_double_cat_lunitor_data.
    - exact spans_double_cat_lunitor_laws.
  Defined.

  Definition spans_double_cat_runitor_data
    : double_runitor_data
        spans_double_cat_hor_id
        spans_double_cat_hor_comp.
  Proof.
    intros x y h.
    simple refine (_ ,, _).
    - exact (span_runitor C PC h).
    - use is_iso_twosided_disp_span_sqr ; cbn.
      apply is_z_iso_span_runitor_mor.
  Defined.

  Proposition spans_double_cat_runitor_laws
    : double_runitor_laws spans_double_cat_runitor_data.
  Proof.
    intros x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ sq.
    use span_sqr_eq.
    rewrite transportb_disp_mor2_span ; cbn.
    unfold span_runitor_mor, mor_of_comp_span_mor.
    rewrite PullbackArrow_PullbackPr1.
    apply idpath.
  Qed.

  Definition spans_double_cat_runitor
    : double_cat_runitor
        spans_double_cat_hor_id
        spans_double_cat_hor_comp.
  Proof.
    use make_double_runitor.
    - exact spans_double_cat_runitor_data.
    - exact spans_double_cat_runitor_laws.
  Defined.

  Definition spans_double_cat_associator_data
    : double_associator_data spans_double_cat_hor_comp.
  Proof.
    intros w x y z h₁ h₂ h₃.
    simple refine (_ ,, _).
    - exact (span_associator C PC h₁ h₂ h₃).
    - use is_iso_twosided_disp_span_sqr ; cbn.
      apply is_z_iso_span_associator_mor.
  Defined.

  Proposition spans_double_cat_associator_laws
    : double_associator_laws spans_double_cat_associator_data.
  Proof.
    intros w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ j₁ j₂ k₁ k₂ vw vx vy vz sq₁ sq₂ sq₃.
    use span_sqr_eq.
    rewrite transportb_disp_mor2_span ; cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
    - rewrite !assoc'.
      unfold span_associator_mor, mor_of_comp_span_mor ; cbn.
      rewrite !PullbackArrow_PullbackPr1.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr1.
      unfold mor_of_comp_span_mor.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
      + rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr1.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr2.
        rewrite !assoc.
        rewrite !PullbackArrow_PullbackPr2.
        rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr1.
        apply idpath.
    - rewrite !assoc'.
      unfold span_associator_mor, mor_of_comp_span_mor ; cbn.
      rewrite !PullbackArrow_PullbackPr2.
      rewrite !assoc.
      rewrite !PullbackArrow_PullbackPr2.
      rewrite !assoc'.
      apply maponpaths.
      unfold mor_of_comp_span_mor.
      rewrite !PullbackArrow_PullbackPr2.
      apply idpath.
  Qed.

  Definition spans_double_cat_associator
    : double_cat_associator spans_double_cat_hor_comp.
  Proof.
    use make_double_associator.
    - exact spans_double_cat_associator_data.
    - exact spans_double_cat_associator_laws.
  Defined.

  (** * 4. The triangle and pentagon equations *)
  Proposition spans_double_cat_triangle
    : triangle_law
        spans_double_cat_lunitor
        spans_double_cat_runitor
        spans_double_cat_associator.
  Proof.
    intro ; intros.
    use span_sqr_eq.
    rewrite transportb_disp_mor2_span ; cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
    - unfold span_associator_mor, mor_of_comp_span_mor ; cbn.
      rewrite !assoc'.
      rewrite !PullbackArrow_PullbackPr1.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr1.
      unfold span_runitor_mor.
      rewrite PullbackArrow_PullbackPr1, id_right.
      apply idpath.
    - unfold span_associator_mor, mor_of_comp_span_mor ; cbn.
      rewrite !assoc'.
      rewrite !PullbackArrow_PullbackPr2.
      rewrite !assoc.
      rewrite PullbackArrow_PullbackPr2.
      refine (id_right _ @ _).
      apply idpath.
  Qed.

  Proposition spans_double_cat_pentagon
    : pentagon_law spans_double_cat_associator.
  Proof.
    intro ; intros.
    use span_sqr_eq.
    rewrite transportb_disp_mor2_span ; cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
    - unfold span_associator_mor, mor_of_comp_span_mor ; cbn.
      rewrite !assoc'.
      rewrite !PullbackArrow_PullbackPr1.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
      + rewrite !assoc'.
        unfold span_associator_mor.
        rewrite !PullbackArrow_PullbackPr1.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          rewrite PullbackArrow_PullbackPr1.
          apply idpath.
        }
        use (MorphismsIntoPullbackEqual (isPullback_Pullback (PC _ _ _ _ _))) ; cbn.
        * rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr1.
          apply id_right.
        * rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr2.
          etrans.
          {
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            rewrite !PullbackArrow_PullbackPr2.
            apply idpath.
          }
          rewrite !assoc.
          rewrite !PullbackArrow_PullbackPr2.
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite !PullbackArrow_PullbackPr1.
          apply idpath.
      + rewrite !assoc'.
        unfold span_associator_mor.
        rewrite !PullbackArrow_PullbackPr2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          rewrite PullbackArrow_PullbackPr1.
          refine (assoc _ _ _ @ _).
          rewrite PullbackArrow_PullbackPr2.
          apply idpath.
        }
        rewrite !assoc.
        rewrite !PullbackArrow_PullbackPr2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite PullbackArrow_PullbackPr1.
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
    - unfold span_associator_mor, mor_of_comp_span_mor.
      rewrite !assoc'.
      rewrite !PullbackArrow_PullbackPr2.
      rewrite !assoc.
      rewrite !PullbackArrow_PullbackPr2.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        rewrite PullbackArrow_PullbackPr2.
        apply idpath.
      }
      rewrite !assoc.
      unfold span_sqr_ob_mor ; cbn.
      rewrite id_right.
      rewrite PullbackArrow_PullbackPr2.
      unfold span_associator_mor .
      rewrite !assoc'.
      rewrite PullbackArrow_PullbackPr2.
      apply idpath.
  Qed.

  (** * 5. The double category of spans *)
  Definition spans_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact C.
    - exact (twosided_disp_cat_of_spans C).
    - exact spans_double_cat_hor_id.
    - exact spans_double_cat_hor_comp.
    - exact spans_double_cat_lunitor.
    - exact spans_double_cat_runitor.
    - exact spans_double_cat_associator.
    - exact spans_double_cat_triangle.
    - exact spans_double_cat_pentagon.
  Defined.

  Definition spans_double_cat_ver_weq_square
    : ver_weq_square spans_double_cat.
  Proof.
    intros x y f g.
    use isweqimplimpl.
    - cbn.
      intros fg.
      induction fg as [ h [ p q ]].
      rewrite id_left, id_right in p.
      rewrite id_left, id_right in q.
      rewrite p, q.
      apply idpath.
    - apply homset_property.
    - use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      pose (p₁ := pr12 φ₁).
      pose (p₂ := pr12 φ₂).
      cbn in p₁, p₂.
      rewrite id_left, id_right in p₁.
      rewrite id_left, id_right in p₂.
      rewrite <- p₁.
      rewrite p₂.
      apply idpath.
  Qed.

  Definition all_companions_spans
    : all_companions_double_cat spans_double_cat.
  Proof.
    intros x y f.
    simple refine (_ ,, _).
    - exact (span_companion C f).
    - use make_double_cat_are_companions'.
      + exact (span_companion_unit C f).
      + exact (span_companion_counit C f).
      + abstract
          (use span_sqr_eq ;
           refine (transportf_disp_mor2_span _ _ _ _ @ _) ;
           cbn ;
           unfold mor_of_comp_span_mor, span_runitor_mor, span_linvunitor ;
           rewrite !assoc' ;
           rewrite PullbackArrow_PullbackPr1 ;
           rewrite !assoc ;
           rewrite PullbackArrow_PullbackPr1 ;
           cbn ;
           apply id_left).
      + abstract
          (use span_sqr_eq ;
           refine (transportf_disp_mor2_span _ _ _ _ @ _) ;
           cbn ;
           apply id_left).
  Defined.

  Definition all_conjoints_spans
    : all_conjoints_double_cat spans_double_cat.
  Proof.
    intros x y f.
    simple refine (_ ,, _).
    - exact (span_conjoint C f).
    - use make_double_cat_are_conjoints'.
      + exact (span_conjoint_unit C f).
      + exact (span_conjoint_counit C f).
      + abstract
          (use span_sqr_eq ;
           refine (transportf_disp_mor2_span _ _ _ _ @ _) ;
           cbn ;
           unfold mor_of_comp_span_mor, span_lunitor_mor, span_rinvunitor ;
           rewrite PullbackArrow_PullbackPr2 ;
           rewrite !assoc ;
           rewrite PullbackArrow_PullbackPr2 ;
           cbn ;
           apply id_left).
      + abstract
          (use span_sqr_eq ;
           refine (transportf_disp_mor2_span _ _ _ _ @ _) ;
           cbn ;
           apply id_left).
  Defined.
End SpansDoubleCat.

Definition spans_univalent_double_cat
           {C : univalent_category}
           (PC : Pullbacks C)
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact (spans_double_cat PC).
  - split.
    + apply univalent_category_is_univalent.
    + use is_univalent_spans_twosided_disp_cat.
      apply univalent_category_is_univalent.
Defined.

Definition spans_pseudo_double_setcat
           {C : setcategory}
           (PC : Pullbacks C)
  : pseudo_double_setcat.
Proof.
  use make_pseudo_double_setcat.
  - exact (spans_double_cat PC).
  - apply C.
  - use is_strict_spans_twosided_disp_cat.
    apply C.
Defined.
