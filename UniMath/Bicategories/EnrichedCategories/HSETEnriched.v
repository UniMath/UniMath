Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Cartesian.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.Enriched.Enriched.
Require Import UniMath.CategoryTheory.Enriched.HSETEnriched.
Require Import UniMath.CategoryTheory.Enriched.ChangeOfBase.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.EnrichedCategories.BicatOfEnrichedCat.
Require Import UniMath.Bicategories.EnrichedCategories.ChangeOfBase.

Local Open Scope cat.

Section HSETEnriched.

Definition HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_data : psfunctor_data (enriched_precat_bicat (cartesian_monoidal TerminalHSET BinProductsHSET)) bicat_of_cats.
Proof.
  use make_psfunctor_data.
  - exact category_from_HSET_enriched_category.
  - exact @functor_from_HSET_enriched_functor.
  - exact @nat_trans_from_HSET_enriched_nat_trans.
  - intro C.
    use make_nat_trans.
    + intro x.
      exact (enriched_cat_id x tt).
    + intros x y f.
      cbn.
      abstract(
        etrans;
        [
          apply (eqtohomot (enriched_id_left x y) (tt,, f))
          | apply pathsinv0; apply (eqtohomot (enriched_id_right x y) (f,, tt))
        ]
      ).
  - cbn.
    intros C D E F G.
    use make_nat_trans.
    + intro x.
      exact (enriched_cat_id (G (F x)) tt).
    + intros x y f.
      cbn.
      abstract(
        etrans;
        [
          apply (eqtohomot (enriched_id_left (G (F x)) (G (F y))) (tt,, _))
          | apply pathsinv0; apply (eqtohomot (enriched_id_right (G (F x)) (G (F y))) (_,, tt))
        ]
      ).
Defined.

Lemma HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_laws : psfunctor_laws HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_data.
Proof.
  repeat split.
  - intros a b f.
    use nat_trans_eq.
    + apply homset_property.
    + cbn.
      intro x.
      reflexivity.
  - intros a b f g h η φ.
    use nat_trans_eq.
    + apply homset_property.
    + cbn.
      intro x.
      reflexivity.
  - intros a b f.
    use nat_trans_eq.
    + apply homset_property.
    + cbn.
      intro x.
      unfold prodtofuntoprod.
      cbn.
      apply pathsinv0.
      cbn in f.
      etrans.
      {
        apply (eqtohomot (enriched_id_left (f x) (f x)) (tt,, _)).
      }
      etrans.
      {
        apply (eqtohomot (enriched_id_left (f x) (f x)) (tt,, _)).
      }
      apply (eqtohomot (enriched_functor_on_identity f x) tt).
  - intros a b f.
    use nat_trans_eq.
    + apply homset_property.
    + cbn.
      intro x.
      apply pathsinv0.
      cbn in f.
      etrans.
      {
        apply (eqtohomot (enriched_id_left (f x) (f x)) (tt,, _)).
      }
      apply (eqtohomot (enriched_id_left (f x) (f x)) (tt,, _)).
  - intros a b c d f g h.
    use nat_trans_eq.
    + apply homset_property.
    + cbn.
      intro x.
      cbn in f, g, h.
      rewrite (eqtohomot (enriched_functor_on_identity h (g (f x))) tt : enriched_functor_on_morphisms h _ _ _ = _).
      reflexivity.
  - intros a b c f g₁ g₂ η.
    use nat_trans_eq.
    + apply homset_property.
    + cbn.
      intro x.
      cbn in f, g₁, g₂.
      etrans.
      {
        apply (eqtohomot (enriched_id_right (g₁ (f x)) (g₂ (f x))) (_,, tt)).
      }
      apply pathsinv0.
      apply (eqtohomot (enriched_id_left (g₁ (f x)) (g₂ (f x))) (tt,, _)).
  - intros a b c f₁ f₂ g η.
    use nat_trans_eq.
    + apply homset_property.
    + cbn.
      intro x.
      cbn in f₁, f₂, g.
      etrans.
      {
        apply (eqtohomot (enriched_id_right (g (f₁ x)) (g (f₂ x))) (_,, tt)).
      }
      apply pathsinv0.
      apply (eqtohomot (enriched_id_left (g (f₁ x)) (g (f₂ x))) (tt,, _)).
Qed.

Definition HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_invertible_cells : invertible_cells HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_data.
Proof.
  split.
  - intros.
    use make_is_invertible_2cell.
    + use make_nat_trans.
      * intro x.
        exact (enriched_cat_id x tt).
      * intros x y f.
        cbn.
        abstract(
          etrans;
          [
            apply (eqtohomot (enriched_id_left x y) (tt,, _))|
            apply pathsinv0;
            apply (eqtohomot (enriched_id_right x y) (_,, tt))
          ]
        ).
    + abstract (
        use nat_trans_eq;
        [
          apply homset_property|
          intro x;
          cbn;
          apply (eqtohomot (enriched_id_right x x) (_,, tt))
        ]
      ).
    + abstract (
        use nat_trans_eq;
        [
          apply homset_property|
          intro x;
          cbn;
          apply (eqtohomot (enriched_id_right x x) (_,, tt))
        ]
      ).
  - intros.
    use make_is_invertible_2cell.
    + use make_nat_trans.
      * intro x.
        cbn in f, g.
        exact (enriched_cat_id (g (f x)) tt).
      * intros x y h.
        cbn.
        cbn in f, g.
        abstract (apply (eqtohomot (enriched_id_left (g (f x)) (g (f y))) (tt,, _) @ (! eqtohomot (enriched_id_right (g (f x)) (g (f y))) (_,, tt)))).
    + abstract (
        use nat_trans_eq;
        [
          apply homset_property|
          intro x;
          cbn;
          apply (eqtohomot (@enriched_id_right _ c _ _) (_,, tt))
        ]
      ).
    + abstract (
        use nat_trans_eq;
        [
          apply homset_property|
          intro x;
          cbn;
          apply (eqtohomot (@enriched_id_right _ c _ _) (_,, tt))
        ]
      ).
Defined.

Definition HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor : psfunctor (enriched_precat_bicat (cartesian_monoidal TerminalHSET BinProductsHSET)) bicat_of_cats.
  use make_psfunctor.
  - exact HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_data.
  - exact HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_laws.
  - exact HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_invertible_cells.
Defined.

Definition bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor_data : psfunctor_data bicat_of_cats (enriched_precat_bicat (cartesian_monoidal TerminalHSET BinProductsHSET)).
Proof.
  use make_psfunctor_data.
  - exact HSET_enriched_category_from_category.
  - exact @HSET_enriched_functor_from_functor.
  - exact @HSET_enriched_nat_trans_from_nat_trans.
  - intro C.
    use make_enriched_nat_trans.
    + intros x _.
      exact (id x).
    + intros x y.
      abstract(
        apply funextfun;
        intro f;
        cbn;
        apply (id_right _ @ (! id_left _))
      ).
  - intros C D E F G.
    use make_enriched_nat_trans.
    + intros x _.
      cbn in F, G.
      exact (id (G (F x))).
    + intros x y.
      abstract(
        apply funextfun;
        intro f;
        cbn;
        apply (id_right _ @ (! id_left _))
      ).
Defined.

Lemma bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor_law : psfunctor_laws bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor_data.
Proof.
  repeat split.
  - intros a b f.
    use enriched_nat_trans_eq.
    intro x.
    reflexivity.
  - intros a b f g h η φ.
    use enriched_nat_trans_eq.
    intro x.
    reflexivity.
  - intros a b f.
    use enriched_nat_trans_eq.
    intro x.
    apply funextfun.
    intro y.
    cbn.
    rewrite functor_id, !id_left.
    reflexivity.
  - intros a b f.
    use enriched_nat_trans_eq.
    intro x.
    apply funextfun.
    intro y.
    cbn.
    rewrite !id_left.
    reflexivity.
  - intros a b c d f g h.
    use enriched_nat_trans_eq.
    intro x.
    apply funextfun.
    intro y.
    cbn.
    rewrite functor_id.
    reflexivity.
  - intros a b c f g₁ g₂ η.
    use enriched_nat_trans_eq.
    intro x.
    apply funextfun.
    intro y.
    cbn.
    apply (id_left _ @ (! id_right _)).
  - intros a b c f₁ f₂ g η.
    use enriched_nat_trans_eq.
    intro x.
    apply funextfun.
    intro y.
    cbn.
    apply (id_left _ @ (! id_right _)).
Qed.

Definition bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor : psfunctor bicat_of_cats (enriched_precat_bicat (cartesian_monoidal TerminalHSET BinProductsHSET)).
Proof.
  use make_psfunctor.
  - exact bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor_data.
  - exact bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor_law.
  - split.
    + intro a.
      use make_is_invertible_2cell.
      * use make_enriched_nat_trans.
        -- intros x _.
           exact (id x).
        -- intros x y.
           abstract (
             apply funextfun;
             intro f;
             cbn;
             apply (id_right _ @ (! id_left _))
           ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          apply funextfun;
          intro;
          apply id_left
        ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          apply funextfun;
          intro;
          apply id_left
        ).
    + intros a b c f g.
      use make_is_invertible_2cell.
      * use make_enriched_nat_trans.
        -- intros x _.
           cbn in f, g.
           exact (id (g (f x))).
        -- intros x y.
           abstract (
             apply funextfun;
             intro;
             cbn;
             apply (id_right _ @ (! id_left _))
           ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          apply funextfun;
          intro;
          apply id_left
        ).
      * abstract (
          use enriched_nat_trans_eq;
          intro x;
          apply funextfun;
          intro;
          apply id_left
        ).
Defined.

(* TODO
Definition HSET_enriched_precat_bicat_bicat_of_cats_biequivalence : biequivalence (enriched_precat_bicat (cartesian_monoidal TerminalHSET BinProductsHSET)) bicat_of_cats.
Proof.
  exists HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor.
  use make_is_biequivalence_from_unit_counit.
  - exact bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor.
  - split.
    + use make_pstrans.
      * use make_pstrans_data.
        -- intro C.
           use make_enriched_functor.
           ++ use make_enriched_functor_data.
              ** exact (λ x, x).
              ** intros x y.
                 exact (λ z, z).
           ++ intro F.
              apply funextfun.
              intro t.
              case t.
              reflexivity.
           ++ cbn.
              intros x y z.
              apply funextfun.
              intro.
              reflexivity.
        -- cbn.
           intros C D F.
           use make_invertible_2cell.
           ++ use make_enriched_nat_trans.
              ** intro x.
                 exact (enriched_cat_id (F x)).
              ** intros x y.
                 apply funextfun.
                 cbn.
                 intro.
                 unfold prodtofuntoprod.
                 cbn.
Defined.
*)

Definition underlying_psfunctor (Mon_V : monoidal_cat) : psfunctor (enriched_precat_bicat Mon_V) bicat_of_cats := comp_psfunctor HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor (change_of_base_psfunctor (forgetful_lax_monoidal_functor Mon_V)).

End HSETEnriched.