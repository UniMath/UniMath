(** * Bicategory of Display Map Categories *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayMapCat.

Require Import UniMath.Bicategories.Core.Bicat.
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Base. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor. *)
(* Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor. *)
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.DispCatTerminal.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FibTerminal.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.CompCat.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.FullCompCat.

Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.
Local Open Scope cat.

Definition prebicat_display_map_cat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact (∑ C : univalent_category, Terminal C × display_map_class C).
  - intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]].                                                        exact (∑ (F : display_map_class_functor D₁ D₂), preserves_terminal (pr1 F)).
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
  intros [C [TC D]]. use make_full_comp_cat.
  - use make_comp_cat.
    + use make_cat_with_terminal_cleaving.
      * use make_cat_with_terminal_disp_cat.
        -- exact C.
        -- exact TC.
        -- exact (univalent_display_map_cat D).
      * exact (display_map_cleaving).
    + exact (cartesian_ι D).
  - exact (ι_ff D).
Defined.

Definition display_map_functor_to_comp_cat_functor
  : ∏ t₁ t₂ : bicat_display_map_cat,
      bicat_display_map_cat ⟦ t₁, t₂ ⟧
      → bicat_full_comp_cat ⟦ display_map_cat_to_full_comp_cat t₁, display_map_cat_to_full_comp_cat t₂ ⟧.
Proof.
  intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] F; use make_full_comp_cat_functor.
  - use make_comp_cat_functor.
    + use make_functor_with_terminal_cleaving.
      * use make_functor_with_terminal_disp_cat.
        -- exact (pr11 F).
        -- exact (pr2 F).
        -- exact (display_map_functor (pr1 F)).
      * exact (is_cartesian_display_map_functor (pr1 F)).
    + exact (map_ι_is_ι_map (pr1 F)).
  - abstract (exact (λ x dx, pr1 (map_ι_is_ι_map (pr1 F) x dx) ,, id_left _ ,, id_right _ )).
Defined.

Definition display_map_transformation_to_comp_cat_transformation
  : ∏ (D₁ D₂ : bicat_display_map_cat) (F G : bicat_display_map_cat ⟦ D₁, D₂ ⟧),
    prebicat_cells bicat_display_map_cat F G
    → prebicat_cells bicat_full_comp_cat (display_map_functor_to_comp_cat_functor D₁ D₂ F)
        (display_map_functor_to_comp_cat_functor D₁ D₂ G).
Proof.
  intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [F pT_F] [G pT_G] α. simpl in *.
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
  intros [C [TC D]]. use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
  - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
    + exact (nat_trans_id _).
    + cbn. use (_ ,, _).
      * intros x dx; simpl in *. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
      * abstract (intros x₁ x₂ f dx₁ dx₂ df;
        use eq_display_map_cat_mor; rewrite (transportb_display_map _ (identity (pr1 dx₁) · pr1 df ,, _));
        exact (id_right _ @ !id_left _)).
  - abstract (intros x dx; exact (id_right _ @ !id_left _)).
Qed.

Definition display_map_to_comp_cat_comp_1cell
  : ∏ (D₁ D₂ D₃ : bicat_display_map_cat) (F : bicat_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_display_map_cat ⟦ D₂, D₃ ⟧),
    prebicat_cells bicat_full_comp_cat
      (display_map_functor_to_comp_cat_functor D₁ D₂ F · display_map_functor_to_comp_cat_functor D₂ D₃ G)
      (display_map_functor_to_comp_cat_functor D₁ D₃ (F · G)).
Proof.
  intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] [F pT_F] [G pT_G]. use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
  - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
    + exact (nat_trans_id _).
    + cbn. unfold display_map_class_functor_composite, display_map_functor_data. simpl.
      use (_ ,, _).
      * intros x dx. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
      * simpl. intros x₁ x₂ f dx₁ dx₂ df. simpl.
        symmetry. etrans.
        all: use subtypePath; try exact (λ _, homset_property _ _ _ _ _).
        -- apply (transportb_display_map_mor (is_nat_trans_id (functor_composite F G) _ _ _) _).
        use subtypePath. { exact (λ _ , homset_property _ _ _ _ _). }
        cbn. symmetry. etrans.
        -- unfold mor_disp, disp_map_ob_mor. apply (@transportb_display_map C₃ _ (pr1 G (pr1 F x₁)) (G (F x₂)) _ _ _ _ (is_nat_trans_id (functor_composite_data (pr1 F) (pr1 G)) x₁ x₂ f) _).
        -- exact (transportb_display_map _ (identity (G (F (pr1 dx₁))) · # G (# F (pr1 df)) ,, _)).
        -- rewrite id_right. rewrite <- id_left with (f := #G (#F (pr1 df))). exact (idpath _).
        -- symmetry. apply transportb_display_map.
Admitted.

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
Admitted.

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_vcomp2_law
  : psfunctor_vcomp2_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
Proof.
Admitted.

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_lunitor_law
  : psfunctor_lunitor_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
Proof.
Admitted.

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_runitor_law
  : psfunctor_runitor_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
Proof.
Admitted.

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_lassociator_law
  : psfunctor_lassociator_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
Proof.
Admitted.

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_lwhisker_law
  : psfunctor_lwhisker_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
Proof.
Admitted.

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_rwhisker_law
  : psfunctor_rwhisker_law bicat_display_map_cat_to_bicat_full_comp_cat_data.
Proof.
Admitted.

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

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_invertible_id_2cell
  : ∏ D : bicat_display_map_cat,
      is_invertible_2cell (PseudoFunctorBicat.psfunctor_id bicat_display_map_cat_to_bicat_full_comp_cat_data D).
Proof.
  intros [C [TC D]]. cbn.
Admitted.

Lemma bicat_display_map_cat_to_bicat_full_comp_cat_invertible_comp_2cell
  : ∏ (D₁ D₂ D₃ : bicat_display_map_cat) (F : bicat_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_display_map_cat ⟦ D₂, D₃ ⟧),
    is_invertible_2cell (PseudoFunctorBicat.psfunctor_comp bicat_display_map_cat_to_bicat_full_comp_cat_data F G).
Proof.
  intros [C₁ [TC₁ D₁]] [C₂ [TC₂ D₂]] [C₃ [TC₃ D₃]] F G. cbn.
Admitted.

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
