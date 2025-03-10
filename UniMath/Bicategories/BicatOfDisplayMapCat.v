(** * Bicategory of Display Map Categories *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayMapCat.

Require Import UniMath.Bicategories.Core.Bicat.
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Base. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor. *)
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.CompCat.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FullCompCat.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Definition prebicat_display_map_cat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact (∑ C : univalent_category, Terminal C × display_map_class C).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]].                                   exact (display_map_class_functor D₁ D₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G.                               exact (nat_trans F G).
  - intros [C [TC D]].                                                    exact (display_map_class_functor_identity D).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G.                 exact (display_map_class_functor_composite F G).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F.                                 exact (nat_trans_id F).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G H α β.                         exact (nat_trans_comp _ _ _ α β).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G H α.             exact (pre_whisker F α).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G H α.             exact (post_whisker α H).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F.                                 exact (nat_trans_id F).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F.                                 exact (nat_trans_id F).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F.                                 exact (nat_trans_id F).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F.                                 exact (nat_trans_id F).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] F G H. exact (nat_trans_id _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] F G H. exact (nat_trans_id _).
Defined.

Definition prebicat_display_map_cat_laws : prebicat_laws prebicat_display_map_cat_data.
Proof.
  split21; cbn.
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G α.
    exact (nat_trans_comp_id_left (pr21 C₂) _ _ α).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G α.
    exact (nat_trans_comp_id_right (pr21 C₂) _ _ α).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G H K α β γ.
    exact (nat_trans_comp_assoc (pr21 C₂) _ _ _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G.
    exact (pre_whisker_identity _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G.
    exact (post_whisker_identity _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G H I α β.
    exact (!pre_whisker_composition _ _ _ _ _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G H I α β.
    exact (!post_whisker_composition _ _ _ _ _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G α.
    rewrite identity_pre_whisker.
    rewrite (nat_trans_comp_id_left (pr21 C₂) F).
    apply nat_trans_comp_id_right.
    exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G α.
    rewrite identity_post_whisker.
    rewrite (nat_trans_comp_id_left (pr21 C₂) F).
    apply nat_trans_comp_id_right.
    exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] F G H I α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] F G H I α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] F G H I α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G H I α β.
    apply nat_trans_eq; cbn. { exact (pr21 C₃). }
    intros x; cbn. exact (pr2 β _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] F G H. apply nat_trans_eq.
    { exact (pr21 C₄). } intros c. exact (id_left _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] F G H. apply nat_trans_eq.
    { exact (pr21 C₄). } intros c. exact (id_left _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G.
    rewrite pre_whisker_identity, post_whisker_identity. apply nat_trans_eq.
    { exact (pr21 C₃). } intros c. exact (id_left _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [C₅ [TC₅ D₅]] F G H I.
    rewrite pre_whisker_identity, post_whisker_identity. apply nat_trans_eq.
    { exact (pr21 C₅). } intros c. cbn. rewrite ? id_left. exact (idpath _).
Qed.

Definition prebicat_display_map_cat_isaset_cells : isaset_cells (prebicat_display_map_cat_data,, prebicat_display_map_cat_laws).
Proof.
  intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F G; cbn in *.
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
Definition display_map_cat_to_full_comp_cat
  : bicat_display_map_cat → bicat_full_comp_cat.
Proof.
  intros [C [TC D]]. use ((((_ ,, ((_ ,, tt) ,, _)) ,, (_ ,, tt)) ,, _) ,, (_ ,, tt)); simpl.
  (* TODO: clean up this splitting ^^? *)
  - exact C.
  - exact TC.
  - exact (univalent_display_map_cat (pr2 C) D).
  - exact (display_map_cleaving).
  - exact (cartesian_ι D).
  - exact (ι_ff D).
Defined.

Definition display_map_functor_to_comp_cat_functor
  : ∏ t₁ t₂ : bicat_display_map_cat,
      bicat_display_map_cat ⟦ t₁, t₂ ⟧
      → bicat_full_comp_cat ⟦ display_map_cat_to_full_comp_cat t₁, display_map_cat_to_full_comp_cat t₂ ⟧.
Proof.
  intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F; use ((((_ ,, ((tt ,, _) ,, _)) ,, (tt ,, _)) ,, _) ,, (tt ,, _)); cbn in *.
  - exact (pr1 F).
  - admit.
  - exact (display_map_functor F).
  - admit.
  - admit.
  - intros x dx. admit.
Admitted.

Definition bicat_display_map_cat_to_bicat_full_comp_cat_data
  : psfunctor_data bicat_display_map_cat bicat_full_comp_cat.
Proof.
  use make_psfunctor_data.
  - exact display_map_cat_to_full_comp_cat.
  - exact display_map_functor_to_comp_cat_functor.
  - admit.
  - intros [C [TC D]]. admit.
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G. admit.
Admitted.

Definition bicat_display_map_cat_to_bicat_full_comp_cat
  : psfunctor bicat_display_map_cat bicat_full_comp_cat.
Proof.
  use make_psfunctor.
  - exact bicat_display_map_cat_to_bicat_full_comp_cat_data.
  - admit.
  - admit.
Admitted.
