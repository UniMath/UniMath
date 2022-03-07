Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Enriched.Enriched.
Require Import UniMath.CategoryTheory.Enriched.ChangeOfBase.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.EnrichedCategories.BicatOfEnrichedCat.

Local Open Scope cat.

Section PseudoFunctor.

Context {Mon_V Mon_V' : monoidal_cat} (F : lax_monoidal_functor Mon_V Mon_V').

Definition change_of_base_psfunctor_data : psfunctor_data (enriched_precat_bicat Mon_V) (enriched_precat_bicat Mon_V').
Proof.
  use make_psfunctor_data.
  - exact (change_of_base_enriched_precat F).
  - exact (@change_of_base_enriched_functor _ _ F).
  - exact (@change_of_base_enriched_nat_trans _ _ F).
  - intro C.
    use make_enriched_nat_trans.
    + intro.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite (functor_id F), <- lax_monoidal_functor_on_postcompose_underlying_morphism, <- lax_monoidal_functor_on_precompose_underlying_morphism, postcompose_identity, precompose_identity;
        reflexivity
      ).
  - intros.
    use make_enriched_nat_trans.
    + intro.
      apply enriched_cat_id.
    + intros x y.
      cbn.
      abstract (
        rewrite <- lax_monoidal_functor_on_postcompose_underlying_morphism, <- lax_monoidal_functor_on_precompose_underlying_morphism, postcompose_identity, precompose_identity, functor_comp;
        reflexivity
      ).
Defined.

Lemma change_of_base_psfunctor_laws : psfunctor_laws change_of_base_psfunctor_data.
Proof.
  repeat split.
  - intros C D G.
    use enriched_nat_trans_eq.
    intro.
    reflexivity.
  - intros a b f g h η φ.
    use enriched_nat_trans_eq.
    cbn.
    intro x.
    rewrite functor_comp.
    rewrite lax_monoidal_functor_on_postcompose_underlying_morphism.
    rewrite assoc.
    reflexivity.
  - intros a b f.
    use enriched_nat_trans_eq.
    cbn.
    intro x.
    rewrite <- lax_monoidal_functor_on_postcompose_underlying_morphism.
    rewrite postcompose_identity.
    rewrite functor_id.
    rewrite !id_right.
    rewrite assoc'.
    rewrite <- functor_comp.
    rewrite (enriched_functor_on_identity f).
    reflexivity.
  - intros a b f.
    use enriched_nat_trans_eq.
    cbn.
    intro x.
    rewrite <- lax_monoidal_functor_on_postcompose_underlying_morphism.
    rewrite postcompose_identity.
    rewrite functor_id.
    rewrite !id_right.
    reflexivity.
  - intros a b c d f g h.
    use enriched_nat_trans_eq.
    cbn.
    intro x.
    rewrite (assoc' _ (#F _) (#F _)).
    rewrite <- functor_comp.
    rewrite (enriched_functor_on_identity h).
    reflexivity.
  - intros a b c f g₁ g₂ η.
    use enriched_nat_trans_eq.
    cbn.
    intro x.
    rewrite <- !lax_monoidal_functor_on_postcompose_underlying_morphism.
    rewrite !assoc'.
    apply cancel_precomposition.
    rewrite <- !functor_comp.
    apply maponpaths.
    etrans.
    {
      apply underlying_morphism_compose_swap.
    }
    rewrite postcompose_identity, precompose_identity.
    reflexivity.
  - intros a b c f₁ f₂ g η.
    use enriched_nat_trans_eq.
    cbn.
    intro x.
    rewrite <- !lax_monoidal_functor_on_postcompose_underlying_morphism.
    rewrite !assoc'.
    apply cancel_precomposition.
    rewrite <- !functor_comp.
    apply maponpaths.
    etrans.
    {
      apply underlying_morphism_compose_swap.
    }
    rewrite postcompose_identity, precompose_identity.
    apply assoc'.
Qed.

Definition change_of_base_psfunctor : psfunctor (enriched_precat_bicat Mon_V) (enriched_precat_bicat Mon_V').
Proof.
  use make_psfunctor.
  - exact change_of_base_psfunctor_data.
  - exact change_of_base_psfunctor_laws.
  - split.
    + intros.
      use make_is_invertible_2cell.
      * use make_enriched_nat_trans.
        -- intro x.
           apply enriched_cat_id.
        -- intros x y.
           cbn.
           abstract (
             rewrite functor_id, <- !lax_monoidal_functor_on_postcompose_underlying_morphism, <- lax_monoidal_functor_on_precompose_underlying_morphism, postcompose_identity, precompose_identity;
             reflexivity
           ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          cbn;
          rewrite <- !lax_monoidal_functor_on_postcompose_underlying_morphism, postcompose_identity, functor_id;
          apply id_right
        ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          cbn;
          rewrite <- !lax_monoidal_functor_on_postcompose_underlying_morphism, postcompose_identity, functor_id;
          apply id_right
        ).
    + intros.
      use make_is_invertible_2cell.
      * use make_enriched_nat_trans.
        -- intro x.
           apply enriched_cat_id.
        -- intros x y.
           cbn.
           abstract (
            rewrite functor_comp, <- !lax_monoidal_functor_on_postcompose_underlying_morphism, <- lax_monoidal_functor_on_precompose_underlying_morphism, postcompose_identity, precompose_identity;
            reflexivity
           ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          cbn;
          rewrite <- !lax_monoidal_functor_on_postcompose_underlying_morphism, postcompose_identity, functor_id;
          apply id_right
        ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          cbn;
          rewrite <- !lax_monoidal_functor_on_postcompose_underlying_morphism, postcompose_identity, functor_id;
          apply id_right
        ).
Defined.

End PseudoFunctor.
