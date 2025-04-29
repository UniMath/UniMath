(** * Bicategory of Display Map Categories
    NOTE: The displayed version of this category should be used instead of this.
          Everything in this file is mirrored in that version.

    This file contains a direct construction of the bicategory of display map categories with a terminal object in their base category.
    It adds the terminal condition to make the construction of the pseudofunctor possible.

    Contents:
    - bicategory of display map categories [bicat_display_map_cat]
    - pseudofunctor into the bicategory of full comprehension categories [bicat_display_map_cat_to_bicat_full_comp_cat]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayMapCat.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Import Bicat.Notations.
Import DispBicat.Notations.
Import PseudoFunctor.Notations.

Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.
Local Open Scope cat.

(** ** Bicategory *)

Definition prebicat_display_map_cat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact (∑ C : univalent_category, Terminal C × display_map_class C).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]].                                                        exact (∑ (F : display_map_class_functor D₁ D₂), preserves_terminal F).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G].                                      exact (nat_trans F G).
  - intros [C [TC D]].                                                                         exact (display_map_class_functor_identity D ,, identity_preserves_terminal _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G].                        exact (display_map_class_functor_composite F G ,, composition_preserves_terminal pT_F pT_G).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].                                               exact (nat_trans_id F).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] [H pT_H] α β.                         exact (nat_trans_comp _ _ _ α β).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G] [H pT_H] α.             exact (pre_whisker F α).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G] [H pT_H] α.             exact (post_whisker α H).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].                                               exact (nat_trans_id _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].                                               exact (nat_trans_id _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].                                               exact (nat_trans_id _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].                                               exact (nat_trans_id _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H]. exact (nat_trans_id _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H]. exact (nat_trans_id _).
Defined.

Definition prebicat_display_map_cat_laws : prebicat_laws prebicat_display_map_cat_data.
Proof.
  split21; cbn.
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] α.
    exact (nat_trans_comp_id_left (pr21 C₂) _ _ α).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] α.
    exact (nat_trans_comp_id_right (pr21 C₂) _ _ α).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] [H pT_H] [I pT_I] α β γ.
    exact (nat_trans_comp_assoc (pr21 C₂) _ _ _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G].
    exact (pre_whisker_identity _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G].
    exact (post_whisker_identity _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G] [H pT_H] [I pT_I] α β.
    exact (!pre_whisker_composition _ _ _ _ _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G] [H pT_H] [I pT_I] α β.
    exact (!post_whisker_composition _ _ _ _ _ _ _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] α.
    rewrite identity_pre_whisker.
    rewrite (nat_trans_comp_id_left (pr21 C₂) F).
    apply nat_trans_comp_id_right.
    exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] α.
    rewrite identity_post_whisker.
    rewrite (nat_trans_comp_id_left (pr21 C₂) F).
    apply nat_trans_comp_id_right.
    exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H] [I pT_I] α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H] [I pT_I] α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H] [I pT_I] α.
    apply nat_trans_eq; cbn. { exact (pr21 C₄). }
    intros x. rewrite id_left, id_right. exact (idpath _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G] [H pT_H] [I pT_I] α β.
    apply nat_trans_eq; cbn. { exact (pr21 C₃). }
    intros x; cbn. exact (pr2 β _ _ _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F]. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F]. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F]. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F]. apply nat_trans_comp_id_left. exact (pr21 C₂).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H]. apply nat_trans_eq.
    { exact (pr21 C₄). } intros c. exact (id_left _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H]. apply nat_trans_eq.
    { exact (pr21 C₄). } intros c. exact (id_left _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G].
    rewrite pre_whisker_identity, post_whisker_identity. apply nat_trans_eq.
    { exact (pr21 C₃). } intros c. exact (id_left _).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [C₅ [TC₅ D₅]] [F pT_F] [G pT_G] [H pT_H] [I pT_I].
    rewrite pre_whisker_identity, post_whisker_identity. apply nat_trans_eq.
    { exact (pr21 C₅). } intros c. cbn. rewrite ? id_left. exact (idpath _).
Qed.

Definition prebicat_display_map_cat_isaset_cells : isaset_cells (prebicat_display_map_cat_data,, prebicat_display_map_cat_laws).
Proof.
  intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G]; cbn in *.
  exact (isaset_nat_trans (pr21 C₂) F G).
Qed.

Definition bicat_display_map_cat : bicat.
Proof.
  use build_bicategory.
  - exact prebicat_display_map_cat_data.
  - exact prebicat_display_map_cat_laws.
  - exact prebicat_display_map_cat_isaset_cells.
Defined.

(** Some functions for clarity *)
Definition display_map_univ_cat : UU := bicat_display_map_cat.
Coercion bicat_display_map_cat_ob_to_display_map_univ_cat (D : bicat_display_map_cat) : display_map_univ_cat := D.

Coercion display_map_cat_to_base_category (D : display_map_univ_cat) : univalent_category := pr1 D.

Coercion display_map_cat_to_terminal_category (D : display_map_univ_cat) : Terminal D := pr12 D.

Coercion display_map_cat_to_display_map_class (D : display_map_univ_cat) : display_map_class (display_map_cat_to_base_category D) := pr22 D.

Definition display_map_cat_functor (D₁ D₂ : bicat_display_map_cat) : UU := bicat_display_map_cat ⟦D₁, D₂⟧.
Coercion bicat_display_map_mor_to_display_map_cat_functor  {D₁ D₂ : bicat_display_map_cat} (F : bicat_display_map_cat ⟦D₁, D₂⟧) : display_map_cat_functor D₁ D₂ := F.

Coercion display_map_functor_to_display_map_class_functor {D₁ D₂ : bicat_display_map_cat} (F : display_map_cat_functor D₁ D₂) : display_map_class_functor D₁ D₂ := pr1 F.

Coercion display_map_functor_preserves_terminal {D₁ D₂ : bicat_display_map_cat} (F : display_map_cat_functor D₁ D₂) : preserves_terminal F := pr2 F.

(** ** Pseudofunctor into the Bicategory of Full Comprehension Categories *)
Section DisplayMapCategoryToFullComprehensionCategory.

  Definition display_map_cat_to_full_comp_cat
    : bicat_display_map_cat → bicat_full_comp_cat.
  Proof.
    intros D. use make_full_comp_cat.
    - use make_comp_cat.
      + use make_cat_with_terminal_cleaving.
        * use make_cat_with_terminal_disp_cat.
          -- exact D.
          -- exact D.
          -- exact (univalent_display_map_cat D).
        * exact display_map_cleaving.
      + exact (cartesian_ι _).
    - exact (ι_ff _).
  Defined.

  Definition display_map_functor_to_comp_cat_functor
    : ∏ t₁ t₂ : bicat_display_map_cat,
        bicat_display_map_cat ⟦ t₁, t₂ ⟧
        → bicat_full_comp_cat ⟦ display_map_cat_to_full_comp_cat t₁, display_map_cat_to_full_comp_cat t₂ ⟧.
  Proof.
    intros D₁ D₂ F; use make_full_comp_cat_functor.
    - use make_comp_cat_functor.
      + use make_functor_with_terminal_cleaving.
        * use make_functor_with_terminal_disp_cat.
          -- exact F.
          -- exact F.
          -- exact (display_map_functor F).
        * exact (is_cartesian_display_map_functor _).
      + exact (map_ι_is_ι_map (display_map_functor_to_display_map_class_functor F)).
    - abstract (exact (λ x dx, pr1 (map_ι_is_ι_map (display_map_functor_to_display_map_class_functor F) x dx) ,, id_left _ ,, id_right _ )).
  Defined.

  Definition display_map_transformation_to_comp_cat_transformation
    : ∏ (D₁ D₂ : bicat_display_map_cat) (F G : bicat_display_map_cat ⟦ D₁, D₂ ⟧),
      prebicat_cells bicat_display_map_cat F G
      → prebicat_cells bicat_full_comp_cat (display_map_functor_to_comp_cat_functor D₁ D₂ F)
          (display_map_functor_to_comp_cat_functor D₁ D₂ G).
  Proof.
    intros D₁ D₂ F G α. simpl in *.
    use make_full_comp_cat_nat_trans; use make_comp_cat_nat_trans.
    - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
      + exact α.
      + exact (display_map_nat_trans α).
    - abstract (
          intros x dx; simpl in x,dx; cbn;
          rewrite id_left, id_right;
          exact (idpath _)).
  Defined.

  Definition display_map_to_comp_cat_id_1cell
    : ∏ D : bicat_display_map_cat,
        prebicat_cells bicat_full_comp_cat (identity (display_map_cat_to_full_comp_cat D))
          (display_map_functor_to_comp_cat_functor D D (identity D)).
  Proof.
    intros D. use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
    - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
      + exact (nat_trans_id _).
      + cbn. use (_ ,, _).
        * intros x dx; simpl in *. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
        * abstract (intros x₁ x₂ f dx₁ dx₂ df;
          use eq_display_map_cat_mor; rewrite (transportb_display_map _ (identity (pr1 dx₁) · pr1 df ,, _));
          exact (id_right _ @ !id_left _)).
    - abstract (intros x dx; exact (id_right _ @ !id_left _)).
  Defined.

  Definition display_map_to_comp_cat_comp_1cell
    : ∏ (D₁ D₂ D₃ : bicat_display_map_cat) (F : bicat_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_display_map_cat ⟦ D₂, D₃ ⟧),
      prebicat_cells bicat_full_comp_cat
        (display_map_functor_to_comp_cat_functor D₁ D₂ F · display_map_functor_to_comp_cat_functor D₂ D₃ G)
        (display_map_functor_to_comp_cat_functor D₁ D₃ (F · G)).
  Proof.
    intros D₁ D₂ D₃ F G. use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
    - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
      + exact (nat_trans_id _).
      + exact display_map_functor_composite_to_composite_display_map_functor.
    - abstract (intros x dx; cbn; rewrite ? (pr12 (pr11 G)); exact (!assoc _ _ _ @ id_left _ @ id_left _ @ !id_right _)).
  Defined.

  Definition bicat_display_map_cat_to_bicat_full_comp_cat_data
    : psfunctor_data bicat_display_map_cat bicat_full_comp_cat.
  Proof.
    use make_psfunctor_data.
    - exact display_map_cat_to_full_comp_cat.
    - exact display_map_functor_to_comp_cat_functor.
    - exact display_map_transformation_to_comp_cat_transformation.
    - exact display_map_to_comp_cat_id_1cell.
    - exact display_map_to_comp_cat_comp_1cell.
  Defined.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_id2_law
    : psfunctor_id2_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].
    use full_comp_nat_trans_eq.
    - intros x. cbn. exact (idpath _).
    - intros x dx. use eq_display_map_cat_mor. etrans.
      + apply transportf_display_map_mor.
      + cbn. exact (idpath _).
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_vcomp2_law
    : psfunctor_vcomp2_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] [H pT_H] α β. cbn in * |-.
    use full_comp_nat_trans_eq.
    - intros x. cbn. exact (idpath _).
    - intros x dx. use eq_display_map_cat_mor. etrans.
      + apply transportf_display_map_mor.
      + cbn. exact (idpath _).
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_lunitor_law
    : psfunctor_lunitor_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].
    use full_comp_nat_trans_eq.
    - intros x. cbn. rewrite (functor_id F). exact (!id_right _ @ !id_right _).
    - intros x dx. use eq_display_map_cat_mor. etrans.
      + apply transportf_display_map_mor.
      + cbn. rewrite (functor_id F). exact (!id_right _ @ !id_right _).
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_runitor_law
    : psfunctor_runitor_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F].
    use full_comp_nat_trans_eq.
    - intros x. cbn. exact (!id_right _ @ !id_right _).
    - intros x dx. use eq_display_map_cat_mor. etrans.
      + apply transportf_display_map_mor.
      + cbn. exact (!id_right _ @ !id_right _).
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_lassociator_law
    : psfunctor_lassociator_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [C₄ [TC₄ D₄]] [F pT_F] [G pT_G] [H pT_H].
    use full_comp_nat_trans_eq.
    - intros x. cbn. rewrite ? (functor_id H). exact (idpath _).
    - intros x dx. use eq_display_map_cat_mor. etrans.
      + apply transportf_display_map_mor.
      + cbn. rewrite ? (functor_id H). exact (idpath _).
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_lwhisker_law
    : psfunctor_lwhisker_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G] [H pT_H] α.
    use full_comp_nat_trans_eq.
    - intros x. cbn. exact (id_left _ @ !id_right _).
    - intros x dx. use eq_display_map_cat_mor. etrans.
      + apply transportf_display_map_mor.
      + cbn. exact (id_left _ @ !id_right _).
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_rwhisker_law
    : psfunctor_rwhisker_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G] [H pT_H] α.
    use full_comp_nat_trans_eq.
    - intros x. cbn. exact (id_left _ @ !id_right _).
    - intros x dx. use eq_display_map_cat_mor. etrans.
      + apply transportf_display_map_mor.
      + cbn. exact (id_left _ @ !id_right _).
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_laws
    : psfunctor_laws bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    split7.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_id2_law.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_vcomp2_law.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_lunitor_law.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_runitor_law.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_lassociator_law.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_lwhisker_law.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_rwhisker_law.
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_id_2cell
    : ∏ d : bicat_display_map_cat,
        disp_nat_trans
          (nat_trans_id (functor_identity (pr1 d))
            :
            functor_data_from_functor _ _
              (full_comp_cat_functor_to_comp_cat_functor
                (# bicat_display_map_cat_to_bicat_full_comp_cat_data (id₁ d)))
            ⟹ functor_data_from_functor _ _
                (full_comp_cat_functor_to_comp_cat_functor
                  (id₁ (bicat_display_map_cat_to_bicat_full_comp_cat_data d))))
          (comp_cat_type_functor
            (full_comp_cat_functor_to_comp_cat_functor
              (# bicat_display_map_cat_to_bicat_full_comp_cat_data (id₁ d))))
          (comp_cat_type_functor
            (full_comp_cat_functor_to_comp_cat_functor
              (id₁ (bicat_display_map_cat_to_bicat_full_comp_cat_data d)))).
  Proof.
    intros [C [TC D]]. use tpair.
    - intros x dx; cbn in *. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
    - abstract (intros x₁ x₂ f dx₁ dx₂ [df Hsq];
      (* symmetry; etrans; use eq_display_map_cat_mor. *)
      use eq_display_map_cat_mor; symmetry; etrans;
      (* the following did not work: *)
      (* + apply transportb_display_map_mor. *)
      (* we'll unfold it instead: *)
      [ refine (pr1_transportf (A := C⟦_, _⟧) _ _ @ _); rewrite transportf_const; simpl; apply id_left | simpl; exact (!id_right _)]).
  Defined.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_invertible_id_2cell
    : ∏ D : bicat_display_map_cat,
        is_invertible_2cell (PseudoFunctorBicat.psfunctor_id bicat_display_map_cat_to_bicat_full_comp_cat_data D).
  Proof.
    intros [C [TC D]].
    use tpair.
    - use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
      + use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
        * cbn. exact (nat_trans_id _).
        * exact (bicat_display_map_cat_to_bicat_full_comp_cat_id_2cell _).
      + intros x dx; cbn in *. exact (idpath _).
    - use tpair; use full_comp_nat_trans_eq; simpl.
      + intros x. exact (id_left _).
      + intros x dx. use eq_display_map_cat_mor. etrans;
        [ apply transportf_display_map_mor | exact (id_left _)].
      + intros x. exact (id_left _).
      + intros x dx. use eq_display_map_cat_mor. etrans;
        [ apply transportf_display_map_mor | exact (id_left _)].
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_comp_2cell
    : ∏ (D₁ D₂ D₃ : bicat_display_map_cat) (F : bicat_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_display_map_cat ⟦ D₂, D₃ ⟧),
        disp_nat_trans
          (nat_trans_id (full_comp_cat_functor_to_comp_cat_functor (# bicat_display_map_cat_to_bicat_full_comp_cat_data (F · G))))
          (comp_cat_type_functor
            (full_comp_cat_functor_to_comp_cat_functor (# bicat_display_map_cat_to_bicat_full_comp_cat_data (F · G))))
          (comp_cat_type_functor
            (full_comp_cat_functor_to_comp_cat_functor (# bicat_display_map_cat_to_bicat_full_comp_cat_data F
              · # bicat_display_map_cat_to_bicat_full_comp_cat_data G))).
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G.
    use tpair.
    - intros x dx. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
    - abstract (intros x₁ x₂ f dx₁ dx₂ [df Hsq];
      use eq_display_map_cat_mor; symmetry; etrans;
      [ refine (pr1_transportf (A := C₃⟦_, _⟧) _ _ @ _); rewrite transportf_const; simpl; apply id_left | simpl; exact (!id_right _)]).
  Defined.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_invertible_comp_2cell
    : ∏ (D₁ D₂ D₃ : bicat_display_map_cat) (F : bicat_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_display_map_cat ⟦ D₂, D₃ ⟧),
      is_invertible_2cell (PseudoFunctorBicat.psfunctor_comp bicat_display_map_cat_to_bicat_full_comp_cat_data F G).
  Proof.
    intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G.
    use tpair.
    - use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
      + use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
        * exact (nat_trans_id _).
        * exact (bicat_display_map_cat_to_bicat_full_comp_cat_comp_2cell _ _ _ _ _).
      + intros x dx. cbn. rewrite functor_id. rewrite ? id_left. exact (idpath _).
    - split; use full_comp_nat_trans_eq;
      [ intros x; exact (id_left _)
      | intros x dx; use subtypePath; try (exact (λ _, homset_property _ _ _ _ _)); etrans;
        [ refine (pr1_transportf (A := C₃⟦_, _⟧) _ _ @ _); rewrite transportf_const;
          apply id_left | exact (idpath _) ]
      | intros x; exact (id_left _)
      | intros x dx; use subtypePath; try (exact (λ _, homset_property _ _ _ _ _)); etrans;
        [ refine (pr1_transportf (A := C₃⟦_, _⟧) _ _ @ _); rewrite transportf_const;
          apply id_left | exact (idpath _) ]].
  Qed.

  Lemma bicat_display_map_cat_to_bicat_full_comp_cat_invertible_cells
    : invertible_cells bicat_display_map_cat_to_bicat_full_comp_cat_data.
  Proof.
    split.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_invertible_id_2cell.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_invertible_comp_2cell.
  Qed.

  Definition bicat_display_map_cat_to_bicat_full_comp_cat
    : psfunctor bicat_display_map_cat bicat_full_comp_cat.
  Proof.
    use make_psfunctor.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_data.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_laws.
    - exact bicat_display_map_cat_to_bicat_full_comp_cat_invertible_cells.
  Defined.

End DisplayMapCategoryToFullComprehensionCategory.

