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
Require Import UniMath.CategoryTheory.Enriched.BicatOfEnrichedCat.
Require Import UniMath.CategoryTheory.Enriched.ChangeOfBase.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
(*Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.*)

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

Definition category_from_HSET_enriched_category (C : enriched_precat (cartesian_monoidal TerminalHSET BinProductsHSET)) : category.
Proof.
  use make_category.
  - use make_precategory.
    + exact (precategory_data_from_HSET_enriched_category C).
    + repeat split; cbn.
      * intros x y f.
        exact (eqtohomot (enriched_id_right x y) (f,, tt)).
      * intros x y f.
        exact (eqtohomot (enriched_id_left x y) (tt,, f)).
      * intros w x y z f g h.
        exact (eqtohomot (enriched_assoc w x y z) ((h,, g),, f)).
      * intros w x y z f g h.
        apply pathsinv0.
        exact (eqtohomot (enriched_assoc w x y z) ((h,, g),, f)).
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
    apply funextsec.
    intro.
    apply assoc.
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
    apply funextsec.
    intro.
    apply functor_id.
  - intros x y z.
    apply funextsec.
    intro.
    apply functor_comp.
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
    apply funextsec.
    intro.
    apply nat_trans_ax.
Defined.

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
      abstract(etrans; [
        apply (eqtohomot (enriched_id_left x y) (tt,, f))
        | apply pathsinv0; apply (eqtohomot (enriched_id_right x y) (f,, tt))
      ]).
  - cbn.
    intros C D E F G.
    use make_nat_trans.
    + intro x.
      exact (enriched_cat_id (G (F x)) tt).
    + intros x y f.
      cbn.
      abstract(etrans; [
        apply (eqtohomot (enriched_id_left (G (F x)) (G (F y))) (tt,, _))
        | apply pathsinv0; apply (eqtohomot (enriched_id_right (G (F x)) (G (F y))) (_,, tt))
      ]).
Defined.

Definition HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_laws : psfunctor_laws HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor_data.
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
        etrans.
        {
          apply (eqtohomot (enriched_id_left x y) (tt,, _)).
        }
        apply pathsinv0.
        apply (eqtohomot (enriched_id_right x y) (_,, tt)).
    + use nat_trans_eq.
      apply homset_property.
      intro x.
      cbn.
      apply (eqtohomot (enriched_id_right x x) (_,, tt)).
    + use nat_trans_eq.
      apply homset_property.
      intro x.
      cbn.
      apply (eqtohomot (enriched_id_right x x) (_,, tt)).
  - intros.
    use make_is_invertible_2cell.
    + use make_nat_trans.
      * intro x.
        cbn in f, g.
        exact (enriched_cat_id (g (f x)) tt).
      * intros x y h.
        cbn.
        cbn in f, g.
        apply (eqtohomot (enriched_id_left (g (f x)) (g (f y))) (tt,, _) @ (! eqtohomot (enriched_id_right (g (f x)) (g (f y))) (_,, tt))).
    + use nat_trans_eq.
      apply homset_property.
      intro x.
      cbn.
      apply (eqtohomot (@enriched_id_right _ c _ _) (_,, tt)).
    + use nat_trans_eq.
      apply homset_property.
      intro x.
      cbn.
      apply (eqtohomot (@enriched_id_right _ c _ _) (_,, tt)).
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
      apply funextfun.
      intro f.
      cbn.
      apply (id_right _ @ (! id_left _)).
  - intros C D E F G.
    use make_enriched_nat_trans.
    + intros x _.
      cbn in F, G.
      exact (id (G (F x))).
    + intros x y.
      apply funextfun.
      intro f.
      cbn.
      apply (id_right _ @ (! id_left _)).
Defined.

Definition bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor : psfunctor bicat_of_cats (enriched_precat_bicat (cartesian_monoidal TerminalHSET BinProductsHSET)).
Proof.
  use make_psfunctor.
  - exact bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor_data.
  - repeat split.
    + intros a b f.
      use enriched_nat_trans_eq.
      intro x.
      reflexivity.
    + intros a b f g h η φ.
      use enriched_nat_trans_eq.
      intro x.
      reflexivity.
    + intros a b f.
      use enriched_nat_trans_eq.
      intro x.
      apply funextfun.
      intro y.
      cbn.
      rewrite functor_id, !id_left.
      reflexivity.
    + intros a b f.
      use enriched_nat_trans_eq.
      intro x.
      apply funextfun.
      intro y.
      cbn.
      rewrite !id_left.
      reflexivity.
    + intros a b c d f g h.
      use enriched_nat_trans_eq.
      intro x.
      apply funextfun.
      intro y.
      cbn.
      rewrite functor_id.
      reflexivity.
    + intros a b c f g₁ g₂ η.
      use enriched_nat_trans_eq.
      intro x.
      apply funextfun.
      intro y.
      cbn.
      apply (id_left _ @ (! id_right _)).
    + intros a b c f₁ f₂ g η.
      use enriched_nat_trans_eq.
      intro x.
      apply funextfun.
      intro y.
      cbn.
      apply (id_left _ @ (! id_right _)).
  - split.
    + intro a.
      use make_is_invertible_2cell.
      * use make_enriched_nat_trans.
        intros x _.
        exact (id x).
        intros x y.
        apply funextfun.
        intro f.
        cbn.
        apply (id_right _ @ (! id_left _)).
      * use enriched_nat_trans_eq.
        intro x.
        apply funextfun.
        intro.
        apply id_left.
      * use enriched_nat_trans_eq.
        intro x.
        apply funextfun.
        intro.
        apply id_left.
    + intros a b c f g.
      use make_is_invertible_2cell.
      * use make_enriched_nat_trans.
        intros x _.
        cbn in f, g.
        exact (id (g (f x))).
        intros x y.
        apply funextfun.
        intro.
        cbn.
        apply (id_right _ @ (! id_left _)).
      * use enriched_nat_trans_eq.
        intro x.
        apply funextfun.
        intro.
        apply id_left.
      * use enriched_nat_trans_eq.
        intro x.
        apply funextfun.
        intro.
        apply id_left.
Defined.

(* TODO
Definition HSET_enriched_precat_bicat_bicat_of_cats_biequivalence : biequivalence (enriched_precat_bicat (cartesian_monoidal TerminalHSET BinProductsHSET)) bicat_of_cats.
Proof.
  exists HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor.
  exists bicat_of_cats_to_HSET_enriched_precat_bicat_psfunctor.
  use tpair.
  - split.
    + use make_pstrans.
      * use make_pstrans_data.
        intro C.
        use make_enriched_functor.
        use make_enriched_functor_data.
        exact (λ x, x).
        intros x y.
        exact (λ z, z).
        intro.
        cbn.
Defined.
*)

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
    apply funextsec.
    intro g.
    cbn.
    unfold prodtofuntoprod.
    cbn.
    cbn in g.
    change (?f1 · ?g1,, ?f2 · ?g2) with ((f1 #, f2) · (g1 #, g2)).
    rewrite (functor_comp (monoidal_cat_tensor Mon_V)).
    apply assoc.
Defined.

Definition forgetful_lax_monoidal_functor (Mon_V : monoidal_cat) : lax_monoidal_functor Mon_V (cartesian_monoidal TerminalHSET BinProductsHSET).
Proof.
  exists (forgetful_functor Mon_V).
  exists (λ _, id _).
  exists (forgetful_functor_mult Mon_V).
  split.
  - intros x y z.
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
  - intro x.
    cbn.
    split; apply funextfun; intro x0.
    + destruct x0 as [t x0].
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
    + destruct x0 as [x0 t].
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
Defined.

Definition underlying_psfunctor (Mon_V : monoidal_cat) : psfunctor (enriched_precat_bicat Mon_V) bicat_of_cats := comp_psfunctor HSET_enriched_precat_bicat_to_bicat_of_cats_psfunctor (change_of_base_psfunctor (forgetful_lax_monoidal_functor Mon_V)).

End Forgetful.
