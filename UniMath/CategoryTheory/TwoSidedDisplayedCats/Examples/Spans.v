#[local] Unset Universe Checking.
(**********************************************************************************

 The two-sided displayed category of spans

 A span in a category `C` is a diagram `x₁ <-- y --> x₂`. We construct a two-sided
 displayed category whose displayed objects are spans.

 Contents
 1. The definition
 2. The univalence

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Local Open Scope cat.

Section Spans.
  Context (C : category).

  (**
   1. The definition
   *)
  Definition spans_ob
    : twosided_disp_cat C C
    := constant_twosided_disp_cat C C C.

  Definition spans_mor_left_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xyz, pr22 xyz --> pr1 xyz).
    - exact (λ xyz₁ xyz₂ l₁ l₂ fgh,
             l₁ · pr1 fgh
             =
             pr22 fgh · l₂).
  Defined.

  Definition spans_mor_left_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category spans_ob)
        spans_mor_left_ob_mor.
  Proof.
    split.
    - intros xyz fgh ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros xyz₁ xyz₂ xyz₃ fgh₁ fgh₂ h₁ h₂ h₃ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      apply idpath.
  Qed.

  Definition spans_mor_left_data
    : disp_cat_data (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_left_ob_mor.
    - exact spans_mor_left_id_comp.
  Defined.

  Definition spans_mor_left_axioms
    : disp_cat_axioms
        (total_twosided_disp_category spans_ob)
        spans_mor_left_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition spans_mor_left
    : disp_cat (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_left_data.
    - exact spans_mor_left_axioms.
  Defined.

  Definition spans_mor_right_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xyz, pr22 xyz --> pr12 xyz).
    - exact (λ xyz₁ xyz₂ l₁ l₂ fgh,
             l₁ · pr12 fgh
             =
             pr22 fgh · l₂).
  Defined.

  Definition spans_mor_right_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category spans_ob)
        spans_mor_right_ob_mor.
  Proof.
    split.
    - intros xyz fgh ; cbn.
      rewrite id_left, id_right.
      apply idpath.
    - intros xyz₁ xyz₂ xyz₃ fgh₁ fgh₂ h₁ h₂ h₃ p₁ p₂ ; cbn in *.
      rewrite !assoc.
      rewrite p₁.
      rewrite !assoc'.
      rewrite p₂.
      apply idpath.
  Qed.

  Definition spans_mor_right_data
    : disp_cat_data (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_right_ob_mor.
    - exact spans_mor_right_id_comp.
  Defined.

  Definition spans_mor_right_axioms
    : disp_cat_axioms
        (total_twosided_disp_category spans_ob)
        spans_mor_right_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply homset_property.
    - intro ; intros.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition spans_mor_right
    : disp_cat (total_twosided_disp_category spans_ob).
  Proof.
    simple refine (_ ,, _).
    - exact spans_mor_right_data.
    - exact spans_mor_right_axioms.
  Defined.

  Definition spans_mors
    : disp_cat (total_twosided_disp_category spans_ob)
    := dirprod_disp_cat
         spans_mor_left
         spans_mor_right.

  Definition twosided_disp_cat_of_spans
    : twosided_disp_cat C C
    := sigma_twosided_disp_cat _ spans_mors.

  (**
   2. The univalence
   *)
  Definition is_univalent_disp_spans_mor_left
    : is_univalent_disp spans_mor_left.
  Proof.
    intros x y p l₁ l₂.
    induction p.
    use isweqimplimpl.
    - intro f ; cbn in *.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_disp_spans_mor_right
    : is_univalent_disp spans_mor_right.
  Proof.
    intros x y p l₁ l₂.
    induction p.
    use isweqimplimpl.
    - intro f ; cbn in *.
      pose (p := pr1 f) ; cbn in p.
      rewrite id_left, id_right in p.
      exact p.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_spans_twosided_disp_cat
             (HC : is_univalent C)
    : is_univalent_twosided_disp_cat twosided_disp_cat_of_spans.
  Proof.
    use is_univalent_sigma_of_twosided_disp_cat.
    - use is_univalent_constant_twosided_disp_cat.
      exact HC.
    - use dirprod_disp_cat_is_univalent.
      + exact is_univalent_disp_spans_mor_left.
      + exact is_univalent_disp_spans_mor_right.
  Defined.
End Spans.
