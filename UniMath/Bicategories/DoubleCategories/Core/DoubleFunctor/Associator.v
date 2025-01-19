(**********************************************************************************

 Preservation of the associator by the composition of double functors

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
(**
 This is to reduce the memory consumption of this file.
 Usually, the Coq kernel uses lazy evaluation, but with this command,
 strict evaluation is used. As a result, the memory consumption might
 decrease while the time consumption might increase.

 On my laptop (M2 Macbook Air, 2022):

 Without kernel term sharing:
 - The final Qed takes 33.027 seconds
 - At the end of the file, 5.92 GB of RAM is used
 With kernel term sharing:
 - The final Qed takes 42.759 seconds
 - At the end of the file, 7.27 GB of RAM is used
 *)

Proposition comp_functor_associator
            {C₁ C₂ C₃ : category}
            {D₁ : twosided_disp_cat C₁ C₁}
            {D₂ : twosided_disp_cat C₂ C₂}
            {D₃ : twosided_disp_cat C₃ C₃}
            {Cm₁ : hor_comp D₁}
            {Cm₂ : hor_comp D₂}
            {Cm₃ : hor_comp D₃}
            {a₁ : double_cat_associator Cm₁}
            {a₂ : double_cat_associator Cm₂}
            {a₃ : double_cat_associator Cm₃}
            {F : C₁ ⟶ C₂}
            {FF : twosided_disp_functor F F D₁ D₂}
            {G : C₂ ⟶ C₃}
            {GG : twosided_disp_functor G G D₂ D₃}
            {FC : double_functor_hor_comp FF Cm₁ Cm₂}
            {GC : double_functor_hor_comp GG Cm₂ Cm₃}
            (Fa : double_functor_associator a₁ a₂ FC)
            (Ga : double_functor_associator a₂ a₃ GC)
  : double_functor_associator
      a₁ a₃
      (comp_hor_comp FC GC).
Proof.
  intros w x y z f g h ; cbn.
  rewrite !two_disp_post_whisker_b.
  rewrite two_disp_pre_whisker_b.
  unfold transportb_disp_mor2.
  rewrite transport_f_f_disp_mor2.
  etrans.
  {
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths.
      exact (id_two_disp_left_alt _).
    }
    rewrite (double_hor_comp_transport_mor _ _ _ _ _ _ _ (functor_id _ _)).
    rewrite two_disp_post_whisker_f.
    rewrite two_disp_pre_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite assoc_two_disp.
      apply maponpaths.
      apply maponpaths_2.
      rewrite twosided_disp_functor_id_alt.
      rewrite functor_double_comp_eq_transport.
      apply idpath.
    }
    unfold transportb_disp_mor2.
    rewrite !two_disp_post_whisker_f.
    rewrite two_disp_pre_whisker_f.
    rewrite !two_disp_post_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp.
    unfold transportb_disp_mor2.
    rewrite two_disp_pre_whisker_f.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply Ga.
    }
    rewrite !two_disp_pre_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite transport_f_f_disp_mor2.
    rewrite twosided_disp_functor_comp_alt.
    rewrite !two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    rewrite twosided_disp_functor_comp_alt.
    rewrite !two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite assoc_two_disp.
      rewrite Fa.
      unfold transportb_disp_mor2.
      rewrite transport_f_f_disp_mor2.
      rewrite transportf_twosided_disp_functor.
      apply idpath.
    }
    rewrite !two_disp_post_whisker_f.
    rewrite transport_f_f_disp_mor2.
    do 2 rewrite twosided_disp_functor_comp.
    unfold transportb_disp_mor2.
    rewrite two_disp_pre_whisker_f.
    rewrite !two_disp_post_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply maponpaths_2.
      exact (id_two_disp_left_alt _).
    }
    rewrite (double_hor_comp_transport_mor _ _ _ _ _ _ _ (!(functor_id _ _))).
    rewrite !two_disp_pre_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite !transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite !transport_f_f_disp_mor2.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite assoc_two_disp.
      apply maponpaths.
      apply maponpaths_2.
      rewrite assoc_two_disp.
      apply maponpaths.
      apply maponpaths_2.
      rewrite twosided_disp_functor_id_alt.
      rewrite transport_f_f_disp_mor2.
      apply (functor_double_comp_eq_transport GC _ _ (idpath _) (idpath _)).
    }
    unfold transportb_disp_mor2.
    rewrite !two_disp_post_whisker_f.
    rewrite !two_disp_pre_whisker_f.
    rewrite !two_disp_post_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite !two_disp_post_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    rewrite assoc_two_disp_alt.
    rewrite !two_disp_post_whisker_f.
    rewrite !transport_f_f_disp_mor2.
    apply idpath.
  }
  rewrite assoc_two_disp_alt.
  rewrite !two_disp_post_whisker_f.
  rewrite !transport_f_f_disp_mor2.
  use transportf_disp_mor2_eq.
  apply idpath.
Qed.
