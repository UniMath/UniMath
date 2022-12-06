Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Cartesian.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Enriched.Enriched.

Local Open Scope cat.

Section HSETEnriched.

Definition precategory_data_from_HSET_enriched_category (C : enriched_precat (cartesian_monoidal TerminalHSET BinProductsHSET)) : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact C.
    + intros x y.
      exact (pr1hSet (enriched_cat_mor x y)).
  - intro x.
    exact (enriched_cat_id x tt).
  - intros x y z f g.
    exact (enriched_cat_comp x y z (g,, f)).
Defined.

Lemma is_precategory_precategory_data_from_HSET_enriched_category (C : enriched_precat (cartesian_monoidal TerminalHSET BinProductsHSET)) : is_precategory (precategory_data_from_HSET_enriched_category C).
Proof.
  repeat split; cbn.
  - intros x y f.
    exact (eqtohomot (enriched_id_right x y) (f,, tt)).
  - intros x y f.
    exact (eqtohomot (enriched_id_left x y) (tt,, f)).
  - intros w x y z f g h.
    exact (eqtohomot (enriched_assoc w x y z) ((h,, g),, f)).
  - intros w x y z f g h.
    apply pathsinv0.
    exact (eqtohomot (enriched_assoc w x y z) ((h,, g),, f)).
Qed.

Definition category_from_HSET_enriched_category (C : enriched_precat (cartesian_monoidal TerminalHSET BinProductsHSET)) : category.
Proof.
  use make_category.
  - use make_precategory.
    + exact (precategory_data_from_HSET_enriched_category C).
    + exact (is_precategory_precategory_data_from_HSET_enriched_category C).
  - intros x y.
    apply setproperty.
Defined.

Definition HSET_enriched_category_from_category (C : category) : enriched_precat (cartesian_monoidal TerminalHSET BinProductsHSET).
Proof.
  use make_enriched_precat.
  - use make_enriched_precat_data.
    + exact C.
    + intros x y.
      use make_hSet.
      * exact (x --> y).
      * apply homset_property.
    + intros x _.
      exact (id x).
    + intros x y z.
      cbn.
      intros f.
      destruct f as [g f].
      exact (f · g).
  - split; cbn; apply funextsec; intro.
    + apply id_right.
    + apply id_left.
  - intros w x y z.
    cbn.
    abstract (
      apply funextsec;
      intro;
      apply assoc
    ).
Defined.

Definition functor_from_HSET_enriched_functor {C D : enriched_precat (cartesian_monoidal TerminalHSET BinProductsHSET)} (F : enriched_functor C D) : functor (category_from_HSET_enriched_category C) (category_from_HSET_enriched_category D).
Proof.
  use make_functor.
  - use make_functor_data.
    + intro x.
      exact (F x).
    + intros x y f.
      exact (enriched_functor_on_morphisms F _ _ f).
  - split.
    + intro x.
      exact (eqtohomot (enriched_functor_on_identity F x) tt).
    + intros x y z f g.
      exact (eqtohomot (enriched_functor_on_comp F x y z) (g,, f)).
Defined.

Definition HSET_enriched_functor_from_functor {C D : category} (F : functor C D) : enriched_functor (HSET_enriched_category_from_category C) (HSET_enriched_category_from_category D).
Proof.
  use make_enriched_functor.
  - use make_enriched_functor_data.
    + intro x.
      exact (F x).
    + intros x y f.
      exact (#F f).
  - intro x.
    abstract (
      apply funextsec;
      intro;
      apply functor_id
    ).
  - intros x y z.
    abstract (
      apply funextsec;
      intro;
      apply functor_comp
    ).
Defined.

Definition nat_trans_from_HSET_enriched_nat_trans {C D : enriched_precat (cartesian_monoidal TerminalHSET BinProductsHSET)} {F G : enriched_functor C D} (a : enriched_nat_trans F G) : nat_trans (functor_from_HSET_enriched_functor F) (functor_from_HSET_enriched_functor G).
Proof.
  use make_nat_trans.
  - intro x.
    exact (a x tt).
  - intros x y f.
    exact (eqtohomot (enriched_nat_trans_ax a x y) f).
Defined.

Definition HSET_enriched_nat_trans_from_nat_trans {C D : category} {F G : functor C D} (a : nat_trans F G) : enriched_nat_trans (HSET_enriched_functor_from_functor F) (HSET_enriched_functor_from_functor G).
Proof.
  use make_enriched_nat_trans.
  - intros x _.
    exact (a x).
  - intros x y.
    abstract (
      apply funextsec;
      intro;
      apply nat_trans_ax
    ).
Defined.

End HSETEnriched.

Section Forgetful.

Definition forgetful_functor (Mon_V : monoidal_cat) : functor Mon_V SET := yoneda Mon_V^op (monoidal_cat_unit Mon_V).

Definition forgetful_functor_mult (Mon_V : monoidal_cat) : nat_trans (functor_composite (PrecategoryBinProduct.pair_functor (forgetful_functor Mon_V) (forgetful_functor Mon_V)) (binproduct_functor BinProductsHSET)) (functor_composite (monoidal_cat_tensor Mon_V) (forgetful_functor Mon_V)).
Proof.
  use make_nat_trans.
  - intro x.
    cbn.
    intro f.
    exact ((nat_z_iso_to_trans_inv (monoidal_cat_left_unitor Mon_V) _) · (#(monoidal_cat_tensor Mon_V) (f : Mon_V ⊠ Mon_V ⟦ (monoidal_cat_unit Mon_V, monoidal_cat_unit Mon_V), x⟧))).
  - intros x y f.
    abstract (
      apply funextsec;
      intro g;
      cbn;
      unfold prodtofuntoprod;
      cbn;
      cbn in g;
      change (?f1 · ?g1,, ?f2 · ?g2) with ((f1 #, f2) · (g1 #, g2));
      rewrite (functor_comp (monoidal_cat_tensor Mon_V));
      apply assoc
    ).
Defined.

Lemma forgetful_monoidal_functor_associativity (Mon_V : monoidal_cat) : monoidal_functor_associativity Mon_V
(cartesian_monoidal TerminalHSET BinProductsHSET) 
(forgetful_functor Mon_V) (forgetful_functor_mult Mon_V).
Proof.
  intros x y z.
  apply funextfun.
  cbn.
  intro x0.
  destruct x0 as [x0 z0].
  destruct x0 as [x0 y0].
  unfold prodtofuntoprod.
  cbn.
  rewrite assoc'.
  apply cancel_precomposition.
  rewrite <- (id_left z0).
  change (?x · ?z ,, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite <- (id_left x0).
  change (?x · ?z ,, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite !id_left.
  rewrite !(functor_comp (monoidal_cat_tensor Mon_V)).
  etrans.
  {
    rewrite assoc'.
    apply cancel_precomposition.
    apply (nat_trans_ax (monoidal_cat_associator Mon_V) _ _ ((_#, _)#, _)).
  }
  rewrite assoc.
  apply cancel_postcomposition.
  rewrite (tensor_z_isomorphism_right _ _ _ _ _ : #(monoidal_cat_tensor Mon_V) _ = _).
  rewrite (tensor_z_isomorphism_left _ _ _ _ _ : #(monoidal_cat_tensor Mon_V) _ = _).
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply (@pathscomp0 _ _ (#(monoidal_cat_tensor Mon_V)
  ((monoidal_cat_right_unitor Mon_V) (monoidal_cat_unit Mon_V) #, id _))).
  apply (maponpaths (λ f, #_ (f #, _))).
  apply (@left_unitor_right_unitor_of_unit Mon_V).
  apply monoidal_cat_triangle_eq.
Qed.

Lemma forgetful_monoidal_functor_unitality (Mon_V : monoidal_cat) : monoidal_functor_unitality Mon_V
(cartesian_monoidal TerminalHSET BinProductsHSET)
(yoneda_objects Mon_V^op (monoidal_cat_unit Mon_V))
(λ _ : unit, id _) (forgetful_functor_mult Mon_V).
Proof.
  intro x.
  cbn.
  split; apply funextfun; intro x0.
  - destruct x0 as [t x0].
    unfold prodtofuntoprod.
    cbn.
    apply pathsinv0.
    etrans.
    {
      rewrite assoc'.
      apply cancel_precomposition.
      apply (nat_trans_ax (monoidal_cat_left_unitor Mon_V)).
    }
    rewrite assoc.
    change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
    rewrite z_iso_after_z_iso_inv.
    apply id_left.
  - destruct x0 as [x0 t].
    unfold prodtofuntoprod.
    cbn.
    apply pathsinv0.
    etrans.
    {
      rewrite assoc'.
      apply cancel_precomposition.
      apply (nat_trans_ax (monoidal_cat_right_unitor Mon_V)).
    }
    rewrite assoc.
    etrans.
    {
      apply cancel_postcomposition.
      apply cancel_precomposition.
      apply pathsinv0.
      apply left_unitor_right_unitor_of_unit.
    }
    change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
    rewrite z_iso_after_z_iso_inv.
    apply id_left.
Qed.

Definition forgetful_lax_monoidal_functor (Mon_V : monoidal_cat) : lax_monoidal_functor Mon_V (cartesian_monoidal TerminalHSET BinProductsHSET).
Proof.
  exists (forgetful_functor Mon_V).
  exists (λ _, id _).
  exists (forgetful_functor_mult Mon_V).
  split.
  - exact (forgetful_monoidal_functor_associativity Mon_V).
  - exact (forgetful_monoidal_functor_unitality Mon_V).
Defined.

End Forgetful.
