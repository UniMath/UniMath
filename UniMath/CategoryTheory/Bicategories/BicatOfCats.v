(* ******************************************************************************* *)
(** * Bicategories

    Benedikt Ahrens, Marco Maggesi

    February 2018

    Bicategory of 1-category and pseudofunctor "op".
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.OpCellBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor.

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



(** * The pseudofunctor op on the bicategory of categories *)

Local Notation "∁" := bicat_of_cats.

Definition op_laxfunctor_data : laxfunctor_data (op2_prebicat ∁) ∁.
Proof.
  use build_laxfunctor_data.
  - exact (λ c, op_cat c).
  - exact (λ _ _ f, functor_opp f).
  - exact (λ _ _ _ _ x, op_nt x).
  - intro C.
    use tpair.
    + cbn.
      intro.
      apply identity.
    + cbn.
      intros a b f.
      cbn in *.
      etrans. { apply id_left. } apply (! id_right _ ).
  - intros C D E F G.
    use tpair.
    + cbn.
      intro.
      apply identity.
    + intros a b f.
      cbn in *.
      etrans. { apply id_left. } apply (! id_right _ ).
Defined.

Definition op_laxfunctor_laws : laxfunctor_laws op_laxfunctor_data.
Proof.
  repeat (use tpair).
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. apply idpath.
  - intros C D F G H α β ; cbn in *.
    apply nat_trans_eq ; [apply (homset_property (op_cat D) )|].
    intro x ; cbn in *.
    reflexivity.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite !id_left.
    apply functor_id.
  - intros C D F. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat D) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right. apply idpath.
  - intros C1 C2 C3 C4 F G H. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C4) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite !id_right.
    rewrite functor_id.
    reflexivity.
  - intros C1 C2 C3  F G H alpha. cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C3) )|].
    intro. cbn. apply pathsinv0.
    rewrite id_left. rewrite id_right.
    apply idpath.
  - intros C1 C2 C3 F1 F2 F3 α ; cbn in *.
    apply nat_trans_eq; [apply (homset_property (op_cat C3) )|].
    intros x ; cbn.
    rewrite id_left, id_right.
    reflexivity.
Qed.

Definition op_laxfunctor : laxfunctor (op2_prebicat ∁) ∁ := _ ,, op_laxfunctor_laws.

Definition op_is_pseudofunctor
  : is_pseudofunctor op_laxfunctor.
Proof.
  split.
  - intro C.
    use tpair.
    + use tpair.
      * cbn. intro. apply identity.
      * intros a b f.
        cbn in *.
        etrans. { apply id_left. } apply (! id_right _ ).
    + split.
      * apply nat_trans_eq. apply homset_property.
        cbn. intro. apply id_left.
      * apply nat_trans_eq. apply homset_property.
        cbn. intro. apply id_left.
  - intros.
    + use tpair.
      * cbn.
        use tpair.
        ** intros x ; cbn.
           apply identity.
        ** intros x y z.
           cbn in *.
           etrans. { apply id_left. } apply (! id_right _ ).
      * split.
        ** apply nat_trans_eq. apply homset_property.
           cbn. intro. apply id_left.
        ** apply nat_trans_eq. apply homset_property.
           cbn. intro. apply id_left.
Defined.

Definition op_pspseudo : psfunctor (op2_prebicat ∁) ∁
  := _ ,, op_is_pseudofunctor.
