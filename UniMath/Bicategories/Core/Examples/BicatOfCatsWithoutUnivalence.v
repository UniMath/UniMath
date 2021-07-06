(* ******************************************************************************* *)
(** * Bicategory of 1-categories

    Benedikt Ahrens, Marco Maggesi

    February 2018

a variant by Ralph Matthes in 2021 without asking for univalence of the object

 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Local Open Scope cat.

Definition cat_prebicat_nouniv_data
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

Definition cat_prebicat_nouniv_laws : prebicat_laws cat_prebicat_nouniv_data.
Proof.
  repeat split; cbn.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_right.
  - intros C D F₁ F₂ F₃ F₄ α β γ.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply assoc.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    reflexivity.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    apply functor_id.
  - intros C₁ C₂ C₃ F G₁ G₂ G₃ α β.
    apply nat_trans_eq; try apply C₃.
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ F₃ G α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (!(functor_comp G _ _)).
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G H₁ H₂ α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ G₁ H₂ α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact ((nat_trans_ax β _ _ _)).
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (id_left _ @ functor_id G _).
  - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
    apply nat_trans_eq; try apply C₅.
    intros ; cbn.
    rewrite !id_left.
    exact (functor_id F₄ _).
Qed.

Definition prebicat_of_cats_nouniv : prebicat := _ ,, cat_prebicat_nouniv_laws.

Lemma isaset_cells_prebicat_of_cats_nouniv : isaset_cells prebicat_of_cats_nouniv.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition bicat_of_cats_nouniv : bicat
  := (prebicat_of_cats_nouniv,, isaset_cells_prebicat_of_cats_nouniv).
