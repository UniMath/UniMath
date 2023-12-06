(**********************************************************************************

 Preservation of the right unitor by the composition of double functors

 This file is split due to high memory consumption

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.Basics.

Local Open Scope cat.

Unset Kernel Term Sharing.
(* this is to reduce the memory consumption of this file *)

Proposition comp_functor_runitor
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {I₁ : hor_id D₁}
            {I₂ : hor_id D₂}
            {I₃ : hor_id D₃}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {r₁ : double_cat_runitor I₁ Cm₁}
            {r₂ : double_cat_runitor I₂ Cm₂}
            {r₃ : double_cat_runitor I₃ Cm₃}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {G : C₂ ⟶ C₃}
            {GG : twosided_disp_functor G G D₂ D₃}
            {FI : double_functor_hor_id FF I₁ I₂}
            {GI : double_functor_hor_id GG I₂ I₃}
            {FC : double_functor_hor_comp FF Cm₁ Cm₂}
            {GC : double_functor_hor_comp GG Cm₂ Cm₃}
            (Fl : double_functor_runitor r₁ r₂ FI FC)
            (Gl : double_functor_runitor r₂ r₃ GI GC)
  : double_functor_runitor
      r₁ r₃
      (comp_hor_id FI GI)
      (comp_hor_comp FC GC).
Proof.
  intros x y f ; cbn.
  rewrite two_disp_post_whisker_b.
  rewrite two_disp_pre_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite Gl, Fl.
  rewrite transportf_twosided_disp_functor.
  rewrite two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp.
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite twosided_disp_functor_comp.
  rewrite two_disp_pre_whisker_b.
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp_alt.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite assoc_two_disp.
    apply idpath.
  }
  rewrite two_disp_post_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    rewrite assoc_two_disp.
    rewrite functor_double_comp_eq_alt.
    unfold transportb_disp_mor2.
    rewrite two_disp_pre_whisker_f.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  rewrite two_disp_pre_whisker_f.
  rewrite two_disp_post_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite assoc_two_disp.
  unfold transportb_disp_mor2.
  rewrite two_disp_pre_whisker_f.
  rewrite two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  rewrite <- double_hor_comp_mor_comp.
  rewrite id_two_disp_left.
  rewrite twosided_disp_functor_id.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  refine (!_).
  etrans.
  {
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite two_disp_pre_whisker_f.
    rewrite transport_f_f_disp_mor2.
    apply idpath.
  }
  etrans.
  {
    apply maponpaths.
    do 3 apply maponpaths_2.
    apply (double_hor_comp_mor_transportf_disp_mor2_right
             _
             (!(id_left _ @ functor_id _ _))).
  }
  rewrite !two_disp_pre_whisker_f.
  rewrite transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  do 4 apply maponpaths_2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.
