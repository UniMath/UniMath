(* The category of relations, i.e. the objects are sets and the morphisms are relations of sets,
   becomes a dagger category by taking the "opposite" relation.
   Furthermore, we show that it is dagger univalent. In order to do this,
   we show that the of isomorphisms is equivalent to type of dagger isomorphisms.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Relations.

Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerCategories.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerIsos.
Require Import UniMath.CategoryTheory.DaggerCategories.Core.DaggerUnivalence.

Local Open Scope cat.

Section RelationsAsDaggers.

  Definition REL_dagger_structure : dagger_structure REL
    := λ _ _ f y x, f x y.

  Lemma REL_dagger_laws : dagger_laws REL_dagger_structure.
  Proof.
    repeat split ; intro ; intros ; repeat (apply funextsec ; intro) ; cbn.
    - use (invweq (weqeqweqhProp _ _)).
      use weqimplimpl.
      + exact (λ p, ! p).
      + exact (λ p, ! p).
      + apply Relations.eq_set.
      + apply Relations.eq_set.
    - use (invweq (weqeqweqhProp _ _)).
      use weqimplimpl.
      + intro p.
        use (factor_through_squash_hProp _ _ p).
        clear p ; intro p.
        apply hinhpr.
        exact (pr1 p ,, pr22 p ,, pr12 p).
      + intro p.
        use (factor_through_squash_hProp _ _ p).
        clear p ; intro p.
        apply hinhpr.
        exact (pr1 p ,, pr22 p ,, pr12 p).
      + apply isapropishinh.
      + apply isapropishinh.
  Qed.

  Definition REL_dagger : dagger REL
    := _ ,, REL_dagger_laws.

End RelationsAsDaggers.

Section DaggerIsosInREL.

  Context (X Y : REL).

  Definition z_iso_REL_equiv_dagger_z_iso
    : z_iso (C := REL) X Y ≃ unitary REL_dagger_structure X Y.
  Proof.
    apply weqfibtototal.
    intro r.
    apply weqimplimpl.
    - intro i.
      unfold is_unitary.
      unfold REL_dagger_structure.

      unfold is_inverse_in_precat.
      Check unique_image_to_inverse_law_in_REL.
      cbn.
      split ; do 2 (apply funextsec ; intro).
      + apply unique_image_to_inverse_law_in_REL.
        * apply is_z_iso_in_REL_to_unique_image.
          use (pr2 (is_z_iso_in_REL_simplified _)).
          split.
          -- exact (pr2 (pr1 (is_z_iso_in_REL_simplified r) i)).
          -- exact (pr1 (pr1 (is_z_iso_in_REL_simplified r) i)).
        * exact (is_z_iso_in_REL_to_unique_image _ i).
      + etrans.
        2: {
          use (unique_image_to_inverse_law_in_REL (r := pr1 i)).
          - exact (pr2 (pr1 (is_z_iso_in_REL_simplified _) (pr2 (z_iso_inv (r,,i))))).
          - apply (is_z_iso_in_REL_to_unique_image).
            exact (pr2 (z_iso_inv (r,,i))).
        }

        apply hPropUnivalence.
        * intro px.
          use (factor_through_squash_hProp _ _ px).
          clear px ; intro px.
          apply hinhpr.
          refine (pr1 px ,, _ ,, _) ;
            apply inverse_swap_relation, (pr2 px).
        * intro px.
          use (factor_through_squash_hProp _ _ px).
          clear px ; intro px.
          apply hinhpr.
          refine (pr1 px ,, _ ,, _) ; apply (inverse_swap_relation_iff i _ _), (pr2 px).
    - exact (λ i, _ ,, (i : is_inverse_in_precat _ _)).
    - apply isaprop_is_z_isomorphism.
    - apply isaprop_is_unitary.
  Defined.

End DaggerIsosInREL.

Section UnivalenceOfRelations.

  Lemma is_dagger_univalent_REL : is_univalent_dagger REL_dagger.
  Proof.
    intros X Y.
    use weqhomot.
    - exact (z_iso_REL_equiv_dagger_z_iso X Y ∘ make_weq _ (is_univalent_REL X Y))%weq.
    - intro p ; induction p.
      use unitary_eq.
      do 2 (apply funextsec ; intro).
      apply idpath.
  Qed.

End UnivalenceOfRelations.
