Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.bicat.bicat.
Require Import UniMath.CategoryTheory.bicat.disp_bicat.

Open Scope cat.
Open Scope mor_disp_scope.


Definition cat_precat_ob_mor : precategory_ob_mor.
Proof.
  exists category.
  intros C D. exact (functor C D).
Defined.

Definition cat_precategory_data : precategory_data.
Proof.
  exists cat_precat_ob_mor.
  use tpair.
  - intro C. cbn in C. exact (functor_identity C).
  - cbn. intros a b c f g.
    exact (functor_composite f g).
Defined.

Definition cat_prebicat_1_id_comp_cells : prebicat_1_id_comp_cells.
Proof.
  exists cat_precategory_data.
  intros a b f g. cbn in *. exact (nat_trans f g).
Defined.

Definition cat_prebicat_data : prebicat_data.
Proof.
  exists cat_prebicat_1_id_comp_cells.
  repeat (use tpair); cbn.
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b f. exact (nat_trans_id f).
  - intros a b c d f g h. exact (nat_trans_id _).
  - intros a b c d f g h. exact (nat_trans_id _).
  - intros a b f g h x y. exact (nat_trans_comp _ _ _ x y).
  - intros a b c f g1 g2 x. exact (pre_whisker f x).
  - intros a b c f1 f2 g x. exact (post_whisker x g).
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
Defined.

Definition prebicat_of_cats : prebicat := _ ,, cat_prebicat_laws.
