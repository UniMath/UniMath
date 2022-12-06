Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Enriched.Enriched.
Require Import UniMath.Bicategories.Core.Bicat.

Local Open Scope cat.

Section BicatOfEnrichedCat.

Definition enriched_precat_prebicat_data (Mon_V : monoidal_cat) : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact (enriched_precat Mon_V).
  - exact enriched_functor.
  - exact (@enriched_nat_trans Mon_V).
  - exact enriched_functor_identity.
  - exact (@enriched_functor_comp Mon_V).
  - exact (@enriched_nat_trans_identity Mon_V).
  - exact (@enriched_nat_trans_comp Mon_V).
  - exact (@pre_whisker Mon_V).
  - exact (@post_whisker Mon_V).
  - intros C D F.
    use make_enriched_nat_trans.
    + intro x.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite postcompose_identity, precompose_identity, id_left;
        reflexivity
      ).
  - intros C D F.
    use make_enriched_nat_trans.
    + intro x.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite postcompose_identity, precompose_identity, id_left;
        reflexivity
      ).
  - intros C D F.
    use make_enriched_nat_trans.
    + intro x.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite postcompose_identity, precompose_identity, id_right;
        reflexivity
      ).
  - intros C D F.
    use make_enriched_nat_trans.
    + intro x.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite postcompose_identity, precompose_identity, !id_right;
        reflexivity
      ).
  - intros A B C D F G H.
    use make_enriched_nat_trans.
    + intro x.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite postcompose_identity, precompose_identity, assoc;
        reflexivity
      ).
  - intros A B C D F G H.
    use make_enriched_nat_trans.
    + intro x.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite postcompose_identity, precompose_identity, !assoc;
        reflexivity
      ).
Defined.

Lemma enriched_precat_prebicat_laws (Mon_V : monoidal_cat) : prebicat_laws (enriched_precat_prebicat_data Mon_V).
Proof.
  repeat split; intros; use enriched_nat_trans_eq; intro; cbn.
  - rewrite underlying_morphism_compose_swap, precompose_identity.
    apply id_right.
  - rewrite postcompose_identity.
    apply id_right.
  - rewrite postcompose_underlying_morphism_composite.
    apply assoc.
  - reflexivity.
  - apply enriched_functor_on_identity.
  - reflexivity.
  - rewrite !assoc'.
    apply cancel_precomposition.
    apply pathsinv0.
    apply enriched_functor_on_postcompose.
  - rewrite postcompose_identity.
    rewrite underlying_morphism_compose_swap.
    rewrite precompose_identity.
    reflexivity.
  - rewrite postcompose_identity.
    rewrite underlying_morphism_compose_swap.
    rewrite precompose_identity.
    apply id_right.
  - rewrite postcompose_identity.
    rewrite underlying_morphism_compose_swap.
    rewrite precompose_identity.
    reflexivity.
  - rewrite postcompose_identity.
    rewrite underlying_morphism_compose_swap.
    rewrite precompose_identity.
    reflexivity.
  - rewrite postcompose_identity.
    rewrite underlying_morphism_compose_swap.
    rewrite precompose_identity.
    rewrite assoc.
    reflexivity.
  - apply pathsinv0.
    rewrite underlying_morphism_compose_swap.
    rewrite !assoc'.
    apply cancel_precomposition.
    apply pathsinv0.
    apply (enriched_nat_trans_ax y).
  - rewrite postcompose_identity.
    apply id_right.
  - rewrite postcompose_identity.
    apply id_right.
  - rewrite postcompose_identity.
    apply id_right.
  - rewrite postcompose_identity.
    apply id_right.
  - rewrite postcompose_identity.
    apply id_right.
  - rewrite postcompose_identity.
    apply id_right.
  - rewrite underlying_morphism_compose_swap.
    rewrite precompose_identity.
    rewrite id_right.
    apply enriched_functor_on_identity.
  - rewrite enriched_functor_on_identity.
    rewrite postcompose_identity.
    apply id_right.
Qed.

Definition enriched_precat_prebicat (Mon_V : monoidal_cat) : prebicat := (_,, enriched_precat_prebicat_laws Mon_V).

Definition enriched_precat_bicat (Mon_V : monoidal_cat) : bicat.
Proof.
  exists (enriched_precat_prebicat Mon_V).
  intros C D F G.
  apply isaset_enriched_nat_trans.
Defined.

End BicatOfEnrichedCat.
