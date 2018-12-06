(* ******************************************************************************* *)
(** * Bicategory of 1-categories

    Benedikt Ahrens, Marco Maggesi

    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.

Local Open Scope cat.

Definition cat_prebicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact category.
  - exact (λ C D, functor C D).
  - exact (λ _ _ F G, nat_trans F G).
  - exact (λ C, functor_identity C).
  - exact (λ _ _ _ F G, functor_composite F G).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ α β, nat_trans_comp _ _ _ α β).
  - exact (λ _ _ _ F _ _ α, pre_whisker F α).
  - exact (λ _ _ _ _ _ H α, post_whisker α H).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
Defined.

Definition cat_prebicat_laws : prebicat_laws cat_prebicat_data.
Proof.
  repeat split; cbn.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply id_right.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply assoc.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply functor_id.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (functor_comp i). apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (nat_trans_ax y ). apply idpath.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    rewrite (functor_id g). apply id_left.
  - intros. apply nat_trans_eq; try apply homset_property. intros. cbn.
    repeat rewrite id_left. apply functor_id.
Qed.

Definition prebicat_of_cats : prebicat := _ ,, cat_prebicat_laws.

Lemma isaset_cells_prebicat_of_cats : isaset_cells prebicat_of_cats.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition bicat_of_cats : bicat
  := (prebicat_of_cats,, isaset_cells_prebicat_of_cats).