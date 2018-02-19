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

Definition cat_bicat_1_id_comp_cells : bicat_1_id_comp_cells.
Proof.
  exists cat_precategory_data.
  intros a b f g. cbn in *. exact (nat_trans f g).
Defined.

Definition cat_bicat_data : bicat_data.
Proof.
  exists cat_bicat_1_id_comp_cells.
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

Definition cat_bicat_laws : bicat_laws cat_bicat_data.
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

Definition bicat_of_cats : bicat := _ ,, cat_bicat_laws.

Local Notation "∁" := bicat_of_cats.
Local Notation "'Set'" := hset_category.

Definition presheaf_disp_cat_data : disp_cat_data ∁.
Proof.
  use tpair.
  - use tpair.
    + exact (λ c : category, functor c^op Set).
    + cbn. intros c d ty ty' f.
      exact (nat_trans ty (functor_composite (functor_opp f) ty')).
  - use tpair.
    + intros c f.
      set (T:= nat_trans_id (pr1 f) ).
      exact T.
    + intros c d e f g ty ty' ty''.
      intros x y.
      set (T1 := x).
      (*
      set (T2 := @pre_whisker
                   (c : category) (d : category) Set
                   (pr1 f) _ _ (y : nat_trans (ty': functor _ _ )  _  )).

      exact (nat_trans_comp x (pre_whisker f y)).
*)
Abort.

Definition disp_presheaf : disp_bicat_1_id_comp_cells bicat_of_cats.
Abort.
