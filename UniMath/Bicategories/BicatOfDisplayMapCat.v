(** * Bicategory of Display Map Categories *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayMapCat.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FullCompCat.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Definition prebicat_display_map_cat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact (∑ C : univalent_category, display_map_class C).
  - intros [C₁ D₁] [C₂ D₂].                       exact (display_map_class_functor D₁ D₂).
  - intros [C₁ D₁] [C₂ D₂] F G.                   exact (nat_trans F G).
  - intros [C D].                                 exact (display_map_class_functor_identity D).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G.           exact (display_map_class_functor_composite F G).
  - intros [C₁ D₁] [C₂ D₂] F.                     exact (nat_trans_id F).
  - intros [C₁ D₁] [C₂ D₂] F G H α β.             exact (nat_trans_comp _ _ _ α β).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G H α.       exact (pre_whisker F α).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G H α.       exact (post_whisker α H).
  - intros [C₁ D₁] [C₂ D₂] F.                     exact (nat_trans_id F).
  - intros [C₁ D₁] [C₂ D₂] F.                     exact (nat_trans_id F).
  - intros [C₁ D₁] [C₂ D₂] F.                     exact (nat_trans_id F).
  - intros [C₁ D₁] [C₂ D₂] F.                     exact (nat_trans_id F).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] F G H. exact (nat_trans_id _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] F G H. exact (nat_trans_id _).
Defined.

Definition prebicat_display_map_cat_laws : prebicat_laws prebicat_display_map_cat_data.
Proof.
  split21; cbn.
  - intros [C₁ D₁] [C₂ D₂] F G α.
    exact (nat_trans_comp_id_left (pr21 C₂) _ _ α).
  - intros [C₁ D₁] [C₂ D₂] F G α.
    exact (nat_trans_comp_id_right (pr21 C₂) _ _ α).
  - intros [C₁ D₁] [C₂ D₂] F G H K α β γ.
    exact (nat_trans_comp_assoc (pr21 C₂) _ _ _ _ _ _ _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G.
    exact (pre_whisker_identity _ _ _ _ _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G.
    exact (post_whisker_identity _ _ _ _ _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G H I α β.
    exact (!pre_whisker_composition _ _ _ _ _ _ _ _ _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G H I α β.
    exact (!post_whisker_composition _ _ _ _ _ _ _ _ _).
  - intros [C₁ D₁] [C₂ D₂] F G α.
    rewrite identity_pre_whisker.
    rewrite (nat_trans_comp_id_left (pr21 C₂) F).
    apply nat_trans_comp_id_right.
    exact (pr21 C₂).
  - intros [C₁ D₁] [C₂ D₂] F G α.
    rewrite identity_post_whisker.
    rewrite (nat_trans_comp_id_left (pr21 C₂) F).
    apply nat_trans_comp_id_right.
    exact (pr21 C₂).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] F G H I α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] F G H I α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] F G H I α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G H I α β.
    apply nat_trans_eq; cbn. { exact (pr21 C₃). }
    intros x; cbn. exact (pr2 β _ _ _).
  - intros [C₁ D₁] [C₂ D₂] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ D₁] [C₂ D₂] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ D₁] [C₂ D₂] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ D₁] [C₂ D₂] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] F G H. apply nat_trans_eq.
    { exact (pr21 C₄). } intros c. exact (id_left _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] F G H. apply nat_trans_eq.
    { exact (pr21 C₄). } intros c. exact (id_left _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] F G.
    rewrite pre_whisker_identity, post_whisker_identity. apply nat_trans_eq.
    { exact (pr21 C₃). } intros c. exact (id_left _).
  - intros [C₁ D₁] [C₂ D₂] [C₃ D₃] [C₄ D₄] [C₅ D₅] F G H I.
    rewrite pre_whisker_identity, post_whisker_identity. apply nat_trans_eq.
    { exact (pr21 C₅). } intros c. cbn. rewrite ? id_left. exact (idpath _).
Defined.

Definition prebicat_display_map_cat_isaset_cells : isaset_cells (prebicat_display_map_cat_data,, prebicat_display_map_cat_laws).
Proof.
  intros [C₁ D₁] [C₂ D₂] F G; cbn in *.
  exact (isaset_nat_trans (pr21 C₂) F G).
Defined.

Definition bicat_display_map_cat : bicat.
Proof.
  use build_bicategory.
  - exact prebicat_display_map_cat_data.
  - exact prebicat_display_map_cat_laws.
  - exact prebicat_display_map_cat_isaset_cells.
Defined.

(** ** Pseudofunctor into the Bicategory of Full Comprehension Categories *)
Definition bicat_display_map_cat_to_bicat_full_comp_cat
  : psfunctor bicat_display_map_cat bicat_full_comp_cat.
Proof.
  use make_psfunctor.
  - admit.
  - admit.
  - admit.
Admitted.
