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

(** * The pseudofunctor op on the bicategory of categories *)

Definition op_cat (c : category) : category := (opp_precat c,, has_homsets_opp (homset_property c) ).

Definition op_nt {c d : category} {f g : functor c d} (a : nat_trans f g)
  : nat_trans (functor_opp g) (functor_opp f).
Proof.
  use tpair.
  - exact (λ c, a c).
  - abstract
      (intros x y h;
       apply (! (nat_trans_ax a _ _ _ ))).
Defined.

Local Notation "∁" := bicat_of_cats.

Definition op_functor_data : functor_data ∁ ∁.
Proof.
  use tpair.
  - exact (λ c, op_cat c).
  - intros c d f. exact (functor_opp f).
Defined.

Definition op_psfunctor_ob_mor_cell : psfunctor_ob_mor_cell ∁ ∁.
Proof.
  exists op_functor_data.
  intros a b f g x.
  cbn in *.
  (* exact (op_nt x). *)
  admit.
Abort.

Local Notation "'Set'" := hset_category.


Definition presheaf_disp_cat_ob_mor : disp_cat_ob_mor ∁.
Proof.
  use tpair.
    + exact (λ c : category, functor c^op Set).
    + cbn. intros c d ty ty' f.
      exact (nat_trans ty (functor_composite (functor_opp f) ty')).
Defined.

Definition presheaf_disp_cat_data : disp_cat_data ∁.
Proof.
  exists presheaf_disp_cat_ob_mor.
  use tpair.
  + intros c f.
    set (T:= nat_trans_id (pr1 f) ).
    exact T.
  + intros c d e f g ty ty' ty''.
    intros x y.
    set (T1 := x).
    set (T2 := @pre_whisker
                 (op_cat c) (op_cat d) Set
                 (functor_opp f) _ _ (y : nat_trans (ty': functor _ _ )  _  )).
    exact (@nat_trans_comp (op_cat c) Set _ _ _ T1 T2 ).
Defined.

Definition presheaf_disp_bicat_1_id_comp_cells : disp_bicat_1_id_comp_cells bicat_of_cats.
Proof.
  exists presheaf_disp_cat_data.
  intros c d f g a.
  intros p p'.
  intros x y.
  exact (x = @nat_trans_comp (op_cat c) Set _  _ _ y (post_whisker (op_nt a)  p')).
Defined.

Definition presheaf_disp_bicat_ops : disp_bicat_ops _ presheaf_disp_bicat_1_id_comp_cells.
Proof.
  repeat split; cbn.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    intro. apply funextsec. intro. cbn. rewrite (functor_id y). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    intro. apply funextsec. intro. cbn. rewrite (functor_id y). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    intro. apply funextsec. intro. cbn. rewrite (functor_id y). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    intro. apply funextsec. intro. cbn. rewrite (functor_id y). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    intro. apply funextsec. intro. cbn. rewrite (functor_id y). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    intro. apply funextsec. intro. cbn. rewrite (functor_id z). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    intro. apply funextsec. intro. cbn. rewrite (functor_id z). apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set).
    intro.
    rewrite X. rewrite X0.
    cbn.
    apply funextsec. intro.
    pose (T:= @functor_comp (op_cat b) _ y).
    specialize (T _ _ _ (s x0) (r x0)).
    apply pathsinv0 in T.
    apply (toforallpaths _ _ _ T _ ).
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    rewrite X.
    intro.
    apply funextsec. intro. cbn. apply idpath.
  - intros. apply nat_trans_eq; try apply (homset_property Set); cbn.
    rewrite X.
    intros. cbn.
    apply funextsec. intro.
    pose (T:= nat_trans_ax gg).
    cbn in T.
    apply (toforallpaths _ _ _ (T _ _ _ )).
Qed.

Definition presheaf_disp_bicat_data : disp_bicat_data ∁ := _ ,,  presheaf_disp_bicat_ops.

Lemma nat_trans_eq_eq {c d : category} {f g : functor c d} {a b : nat_trans f g}
      (e e' : a = b)
  : e = e'.
Proof.
Admitted.
Lemma presheaf_disp_bicat_laws : disp_bicat_laws _ presheaf_disp_bicat_data.
Proof.
  repeat split; intro.
  - intros.
    set(T:= vcomp2_disp ∁ (id2_disp ∁ ff) ηη).
    cbn in T.
    admit.
Abort.
