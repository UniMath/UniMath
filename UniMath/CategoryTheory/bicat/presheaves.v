Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.bicat.bicat.
Require Import UniMath.CategoryTheory.bicat.disp_bicat.
Require Import UniMath.CategoryTheory.bicat.bicat_of_cats.

Open Scope cat.
Open Scope mor_disp_scope.


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

Local Notation "∁" := prebicat_of_cats.

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

Definition presheaf_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells prebicat_of_cats.
Proof.
  exists presheaf_disp_cat_data.
  intros c d f g a.
  intros p p'.
  intros x y.
  exact (x = @nat_trans_comp (op_cat c) Set _  _ _ y (post_whisker (op_nt a)  p')).
Defined.

Definition presheaf_disp_prebicat_ops : disp_prebicat_ops _ presheaf_disp_prebicat_1_id_comp_cells.
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

Definition presheaf_disp_prebicat_data : disp_prebicat_data ∁ := _ ,,  presheaf_disp_prebicat_ops.

Lemma nat_trans_eq_eq {c d : category} {f g : functor c d} {a b : nat_trans f g}
      (e e' : a = b)
  : e = e'.
Proof.
Admitted.
Lemma presheaf_disp_prebicat_laws : disp_prebicat_laws _ presheaf_disp_prebicat_data.
Proof.
  repeat split; intro.
  - intros.
    set(T:= vcomp2_disp ∁ (id2_disp ∁ ff) ηη).
    cbn in T.
    admit.
Abort.
