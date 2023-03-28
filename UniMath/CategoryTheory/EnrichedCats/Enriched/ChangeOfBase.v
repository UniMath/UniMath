Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section Change_Of_Base.

Context {Mon_V Mon_V' : monoidal_cat} (F : lax_monoidal_functor Mon_V Mon_V').

Definition change_of_base_enriched_precat_data (A : enriched_precat Mon_V) : enriched_precat_data Mon_V'.
Proof.
  use make_enriched_precat_data.
  - exact A.
  - intros x y.
    exact (F (enriched_cat_mor x y)).
  - intro x.
    exact (mon_functor_unit F · #F (enriched_cat_identity _)).
  - intros x y z.
    exact (mon_functor_tensor F _ _ · #F (enriched_cat_comp _ y _)).
Defined.

Definition change_of_base_enriched_id_ax (A : enriched_precat Mon_V) : enriched_id_ax (change_of_base_enriched_precat_data A).
Proof.
  intros a b.
  split; cbn.
  - rewrite <- (functor_id F).
    rewrite <- (id_left (#F (identity _))).
    rewrite tensor_comp_mor.
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_mon_functor_tensor.
      apply idpath.
    }
    rewrite !assoc'.
    rewrite <- (functor_comp F).
    etrans.
    {
      do 3 apply maponpaths.
      apply enriched_id_left.
    }
    rewrite !assoc.
    exact (!(mon_functor_lunitor F _)).
  - rewrite <- (functor_id F).
    rewrite <- (id_left (#F (identity _))).
    rewrite tensor_comp_mor.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_mon_functor_tensor.
      apply idpath.
    }
    rewrite !assoc'.
    rewrite <- (functor_comp F).
    etrans.
    {
      do 3 apply maponpaths.
      apply enriched_id_right.
    }
    rewrite !assoc.
    exact (!(mon_functor_runitor F _)).
Qed.

Definition change_of_base_enriched_assoc_ax (A : enriched_precat Mon_V) : enriched_assoc_ax (change_of_base_enriched_precat_data A).
Proof.
  intros a b c d.
  simpl in a, b, c, d.
  cbn.
  rewrite <- (functor_id F).
  rewrite <- (id_left (#F (identity _))).
  rewrite tensor_comp_mor.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite tensor_mon_functor_tensor.
    rewrite !assoc'.
    rewrite <- functor_comp.
    rewrite enriched_assoc.
    rewrite !functor_comp.
    apply idpath.
  }
  rewrite !assoc.
  apply cancel_postcomposition.
  rewrite mon_functor_lassociator.
  rewrite !assoc'.
  apply maponpaths.
  rewrite tensor_comp_id_l.
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- tensor_mon_functor_tensor.
  rewrite functor_id.
  apply idpath.
Qed.

Definition change_of_base_enriched_precat (A : enriched_precat Mon_V) : enriched_precat Mon_V'.
Proof.
  use make_enriched_precat.
  - exact (change_of_base_enriched_precat_data A).
  - exact (change_of_base_enriched_id_ax A).
  - exact (change_of_base_enriched_assoc_ax A).
Defined.

Definition change_of_base_enriched_functor_data {A B : enriched_precat Mon_V} (G : enriched_functor A B) : enriched_functor_data (change_of_base_enriched_precat A) (change_of_base_enriched_precat B).
Proof.
  use make_enriched_functor_data.
  + exact G.
  + intros x y.
    exact (#F (enriched_functor_on_morphisms G _ _)).
Defined.

Definition change_of_base_enriched_functor_unit_ax {A B : enriched_precat Mon_V} (G : enriched_functor A B) : enriched_functor_unit_ax (change_of_base_enriched_functor_data G).
Proof.
  intro a.
  cbn.
  rewrite assoc'.
  apply cancel_precomposition.
  rewrite <- (functor_comp F).
  apply maponpaths.
  apply enriched_functor_on_identity.
Qed.

Definition change_of_base_enriched_functor_comp_ax {A B : enriched_precat Mon_V} (G : enriched_functor A B) : enriched_functor_comp_ax (change_of_base_enriched_functor_data G).
Proof.
  intros a b c.
  cbn.
  rewrite assoc.
  rewrite tensor_mon_functor_tensor.
  rewrite !assoc'.
  apply cancel_precomposition.
  cbn.
  rewrite <- !(functor_comp F).
  apply maponpaths.
  apply enriched_functor_on_comp.
Qed.

Definition change_of_base_enriched_functor {A B : enriched_precat Mon_V} (G : enriched_functor A B) : enriched_functor (change_of_base_enriched_precat A) (change_of_base_enriched_precat B).
Proof.
  use make_enriched_functor.
  - exact (change_of_base_enriched_functor_data G).
  - exact (change_of_base_enriched_functor_unit_ax G).
  - exact (change_of_base_enriched_functor_comp_ax G).
Defined.

Lemma lax_monoidal_functor_on_postcompose_underlying_morphism {A : enriched_precat Mon_V} (x : A) {y z : A} (f : underlying_morphism y z) : # F (postcompose_underlying_morphism x f) = @postcompose_underlying_morphism _ (change_of_base_enriched_precat _) _ _ _ (mon_functor_unit F · # F f).
Proof.
  unfold postcompose_underlying_morphism.
  do 2 rewrite (functor_comp F).
  cbn.
  rewrite assoc.
  apply cancel_postcomposition.
  rewrite <- (functor_id F).
  rewrite <- (id_left (#F (identity _))).
  rewrite tensor_comp_mor.
  rewrite assoc, assoc'.
  rewrite tensor_mon_functor_tensor.
  rewrite assoc.
  apply cancel_postcomposition.
  change (# F (is_z_isomorphism_mor ?f)) with (is_z_isomorphism_mor (functor_on_is_z_isomorphism F f)).
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply pathsinv0.
  rewrite mon_functor_linvunitor.
  apply idpath.
Qed.

Lemma lax_monoidal_functor_on_precompose_underlying_morphism {A : enriched_precat Mon_V} {x y : A} (z : A) (f : underlying_morphism x y) : # F (precompose_underlying_morphism z f) = @precompose_underlying_morphism _ (change_of_base_enriched_precat _) _ _ _ (mon_functor_unit F · # F f).
Proof.
  unfold precompose_underlying_morphism.
  do 2 rewrite (functor_comp F).
  cbn.
  rewrite assoc.
  apply cancel_postcomposition.
  rewrite <- (functor_id F).
  rewrite <- (id_left (#F (identity _))).
  rewrite tensor_comp_mor.
  rewrite assoc, assoc'.
  apply (transportb (λ g, _ = _ · g) (tensor_mon_functor_tensor F _ _)).
  rewrite assoc.
  apply cancel_postcomposition.
  change (# F (is_z_isomorphism_mor ?f)) with (is_z_isomorphism_mor (functor_on_is_z_isomorphism F f)).
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply pathsinv0.
  rewrite mon_functor_rinvunitor.
  apply idpath.
Qed.

Definition change_of_base_enriched_nat_trans {A B : enriched_precat Mon_V} {G H : enriched_functor A B} (a : enriched_nat_trans G H) : enriched_nat_trans (change_of_base_enriched_functor G) (change_of_base_enriched_functor H).
Proof.
  use make_enriched_nat_trans.
  - intro x.
    exact (mon_functor_unit F · #F (a x)).
  - abstract (intros x y;
    cbn;
    rewrite <- lax_monoidal_functor_on_postcompose_underlying_morphism;
    rewrite <- lax_monoidal_functor_on_precompose_underlying_morphism;
    rewrite <- !(functor_comp F);
    apply maponpaths;
    apply enriched_nat_trans_ax).
Defined.

End Change_Of_Base.
