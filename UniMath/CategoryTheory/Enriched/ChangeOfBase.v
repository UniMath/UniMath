Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Enriched.Enriched.
Require Import UniMath.CategoryTheory.Enriched.BicatOfEnrichedCat.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.

Local Open Scope cat.

Section Change_Of_Base.

Context {Mon_V Mon_V' : monoidal_cat} (F : lax_monoidal_functor Mon_V Mon_V').

Definition change_of_base_enriched_precat_data (A : enriched_precat Mon_V) : enriched_precat_data Mon_V'.
Proof.
  use make_enriched_precat_data.
  - exact A.
  - intros x y.
    exact (F (enriched_cat_mor x y)).
  - intro x.
    exact (lax_monoidal_functor_ϵ F · #F (enriched_cat_id _)).
  - intros x y z.
    exact (lax_monoidal_functor_μ F (_, _) · #F (enriched_cat_comp _ y _)).
Defined.

Definition change_of_base_enriched_id_ax (A : enriched_precat Mon_V) : enriched_id_ax (change_of_base_enriched_precat_data A).
Proof.
  intros a b.
  split; cbn.
  - rewrite <- (functor_id F).
    rewrite <- (id_left (#F (id _))).
    change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
    rewrite (functor_comp (monoidal_cat_tensor Mon_V')).
    rewrite assoc.
    rewrite (assoc' _ (#(monoidal_cat_tensor Mon_V') _)).
    apply (transportb (λ f, _ · f · _ = _) (nat_trans_ax (lax_monoidal_functor_μ F) _ _ (_ #, _))).
    simpl.
    rewrite assoc, assoc'.
    rewrite <- (functor_comp F).
    apply (transportb (λ f, _ · #F f = _) (enriched_id_left _ _)).
    apply pathsinv0.
    apply (lax_monoidal_functor_unital F).
  - rewrite <- (functor_id F).
    rewrite <- (id_left (#F (id _))).
    change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
    rewrite (functor_comp (monoidal_cat_tensor Mon_V')).
    rewrite assoc.
    rewrite (assoc' _ (#(monoidal_cat_tensor Mon_V') _)).
    apply (transportb (λ k, _ · k · _ = _) (nat_trans_ax (lax_monoidal_functor_μ F) _ _ (_ #, _))).
    simpl.
    rewrite assoc, assoc'.
    rewrite <- (functor_comp F).
    apply (transportb (λ k, _ · #F k = _) (enriched_id_right _ _)).
    apply pathsinv0.
    apply (lax_monoidal_functor_unital F).
Qed.

Definition change_of_base_enriched_assoc_ax (A : enriched_precat Mon_V) : enriched_assoc_ax (change_of_base_enriched_precat_data A).
Proof.
  intros a b c d.
  simpl in a, b, c, d.
  cbn.
  rewrite <- (functor_id F).
  rewrite <- (id_left (#F (id _))).
  change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite (functor_comp (monoidal_cat_tensor Mon_V')).
  rewrite <- (functor_id F (enriched_cat_mor c _)).
  rewrite <- (id_left (#F (id enriched_cat_mor c _))).
  change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite (functor_comp (monoidal_cat_tensor Mon_V')).
  rewrite !assoc.
  rewrite (assoc' _ (#(monoidal_cat_tensor Mon_V') _)).
  apply (transportb (λ k, _ · k · _ = _) (nat_trans_ax (lax_monoidal_functor_μ F) _ _ (_ #, _))).
  match goal with [|- _ = _ · _ · ?f · _ · _] => rewrite (assoc' _ f) end.
  apply (transportb (λ k, _ = _ · k · _) (nat_trans_ax (lax_monoidal_functor_μ F) _ _ (_ #, _))).
  cbn.
  rewrite !assoc.
  do 2 rewrite (assoc' _ (#F _) (#F _)).
  do 2 rewrite <- (functor_comp F).
  apply (transportb (λ k, _ · #F k = _) (enriched_assoc _ _ _ _)).
  rewrite (functor_comp F), assoc.
  apply cancel_postcomposition.
  apply lax_monoidal_functor_assoc.
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
  apply (transportb (λ h, _ = h · _) (nat_trans_ax (lax_monoidal_functor_μ F) _ _ (_ #, _))).
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

Lemma lax_monoidal_functor_on_postcompose_underlying_morphism {A : enriched_precat Mon_V} (x : A) {y z : A} (f : underlying_morphism y z) : # F (postcompose_underlying_morphism x f) = @postcompose_underlying_morphism _ (change_of_base_enriched_precat _) _ _ _ (lax_monoidal_functor_ϵ F · # F f).
Proof.
  unfold postcompose_underlying_morphism.
  do 2 rewrite (functor_comp F).
  cbn.
  rewrite assoc.
  apply cancel_postcomposition.
  rewrite <- (functor_id F).
  rewrite <- (id_left (#F (id _))).
  change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite (functor_comp (monoidal_cat_tensor Mon_V')).
  rewrite assoc, assoc'.
  apply (transportb (λ g, _ = _ · g) (nat_trans_ax (lax_monoidal_functor_μ F) _ _ (_ #, _))).
  rewrite assoc.
  apply cancel_postcomposition.
  change (# F (is_z_isomorphism_mor ?f)) with (is_z_isomorphism_mor (functor_on_is_z_isomorphism F f)).
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply pathsinv0.
  rewrite assoc'.
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply (lax_monoidal_functor_unital F).
Qed.

Lemma lax_monoidal_functor_on_precompose_underlying_morphism {A : enriched_precat Mon_V} {x y : A} (z : A) (f : underlying_morphism x y) : # F (precompose_underlying_morphism z f) = @precompose_underlying_morphism _ (change_of_base_enriched_precat _) _ _ _ (lax_monoidal_functor_ϵ F · # F f).
Proof.
  unfold precompose_underlying_morphism.
  do 2 rewrite (functor_comp F).
  cbn.
  rewrite assoc.
  apply cancel_postcomposition.
  rewrite <- (functor_id F).
  rewrite <- (id_left (#F (id _))).
  change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite (functor_comp (monoidal_cat_tensor Mon_V')).
  rewrite assoc, assoc'.
  apply (transportb (λ g, _ = _ · g) (nat_trans_ax (lax_monoidal_functor_μ F) _ _ (_ #, _))).
  rewrite assoc.
  apply cancel_postcomposition.
  change (# F (is_z_isomorphism_mor ?f)) with (is_z_isomorphism_mor (functor_on_is_z_isomorphism F f)).
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply pathsinv0.
  rewrite assoc'.
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply (lax_monoidal_functor_unital F).
Qed.

Definition change_of_base_enriched_nat_trans {A B : enriched_precat Mon_V} {G H : enriched_functor A B} (a : enriched_nat_trans G H) : enriched_nat_trans (change_of_base_enriched_functor G) (change_of_base_enriched_functor H).
Proof.
  use make_enriched_nat_trans.
  - intro x.
    exact (lax_monoidal_functor_ϵ F · #F (a x)).
  - abstract (intros x y;
    cbn;
    rewrite <- lax_monoidal_functor_on_postcompose_underlying_morphism;
    rewrite <- lax_monoidal_functor_on_precompose_underlying_morphism;
    rewrite <- !(functor_comp F);
    apply maponpaths;
    apply enriched_nat_trans_ax).
Defined.

End Change_Of_Base.

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
