(**************************************************************************************************

  The Karoubi Envelope

  Defines the universal property of a Karoubi envelope, an idempotent completion, a category of
  retracts or a Cauchy completion of a category C. This is a completion of C in which every
  idempotent splits.
  Presheaves (and functors) from C to a category with colimits (or coequalizers) can be lifted to
  functors on its Karoubi envelope, and this constitutes an adjoint equivalence.

  Contents
  1. The definition of a karoubi envelope
    [univalent_karoubi_envelope] [set_karoubi_envelope]
  2. Functors on C are equivalent to functors on the setcategory Karoubi envelope
    [karoubi_pullback_equivalence]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Retracts.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SurjectivePrecomposition.

Local Open Scope cat.

Lemma retract_functor_is_equalizer
  {C D : category}
  (F : C ⟶ D)
  {a b : C}
  (H : retraction b a)
  : Equalizer (#F (retraction_retraction H) · #F (retraction_section H)) (identity (F a)).
Proof.
  exact (retract_is_equalizer (functor_preserves_retraction F H)).
Defined.

Lemma retract_functor_is_coequalizer
  {C D : category}
  (F : C ⟶ D)
  {a b : C}
  (H : retraction b a)
  : Coequalizer (#F (retraction_retraction H) · #F (retraction_section H)) (identity (F a)).
Proof.
  exact (retract_is_coequalizer (functor_preserves_retraction F H)).
Defined.

(** * 1. The definition of a karoubi envelope *)

Definition karoubi_envelope_data
  (C : category)
  : UU
  := ∑ (D : category), C ⟶ D.

Definition make_karoubi_envelope_data
  {C : category}
  (D : category)
  (F : C ⟶ D)
  : karoubi_envelope_data C
  := D ,, F.

Coercion karoubi_envelope_data_category
  {C : category}
  (D : karoubi_envelope_data C)
  : category
  := pr1 D.

Definition karoubi_envelope_functor
  {C : category}
  (D : karoubi_envelope_data C)
  : C ⟶ D
  := pr2 D.


Definition idempotents_split
  (D : category)
  : UU
  := ∏ (X : D) (f : idempotent X), ∥ is_split_idempotent f ∥.

Definition objects_are_retracts
  {C D : category}
  (F : C ⟶ D)
  : UU
  := ∏ (X : D), ∃ (Y : C), retraction X (F Y).

Definition is_karoubi_envelope
  {C : category}
  (D : karoubi_envelope_data C)
  : UU
  := idempotents_split D ×
    fully_faithful (karoubi_envelope_functor D) ×
    objects_are_retracts (karoubi_envelope_functor D).

Definition make_is_karoubi_envelope
  {C : category}
  {D : karoubi_envelope_data C}
  (H1 : idempotents_split D)
  (H2 : fully_faithful (karoubi_envelope_functor D))
  (H3 : objects_are_retracts (karoubi_envelope_functor D))
  : is_karoubi_envelope D
  := H1 ,, H2 ,, H3.

Definition karoubi_envelope
  (C : category)
  : UU
  := ∑ (D : karoubi_envelope_data C), is_karoubi_envelope D.

Definition make_karoubi_envelope
  {C : category}
  (D : karoubi_envelope_data C)
  (H : is_karoubi_envelope D)
  : karoubi_envelope C
  := D ,, H.

Coercion karoubi_envelope_to_data
  {C : category}
  (D : karoubi_envelope C)
  : karoubi_envelope_data C
  := pr1 D.

Definition karoubi_envelope_idempotents_split
  {C : category}
  (D : karoubi_envelope C)
  : idempotents_split D
  := pr12 D.

Definition karoubi_envelope_fully_faithful
  {C : category}
  (D : karoubi_envelope C)
  : fully_faithful (karoubi_envelope_functor D)
  := pr122 D.

Definition karoubi_envelope_objects_are_retracts
  {C : category}
  (D : karoubi_envelope C)
  : objects_are_retracts (karoubi_envelope_functor D)
  := pr222 D.


Definition univalent_karoubi_envelope
  (C : category)
  : UU
  := ∑ (D : karoubi_envelope C), is_univalent D.

Definition make_univalent_karoubi_envelope
  {C : category}
  (D : karoubi_envelope C)
  (H : is_univalent D)
  : univalent_karoubi_envelope C
  := D ,, H.

Coercion univalent_karoubi_envelope_to_karoubi_envelope
  {C : category}
  (D : univalent_karoubi_envelope C)
  : karoubi_envelope C
  := pr1 D.

Definition univalent_karoubi_envelope_is_univalent
  {C : category}
  (D : univalent_karoubi_envelope C)
  : is_univalent D
  := pr2 D.


Definition set_karoubi_envelope
  (C : category)
  : UU
  := ∑ (D : karoubi_envelope C), isaset D.

Definition make_set_karoubi_envelope
  {C : category}
  (D : karoubi_envelope C)
  (H : isaset D)
  : set_karoubi_envelope C
  := D ,, H.

Coercion set_karoubi_envelope_to_karoubi_envelope
  {C : category}
  (D : set_karoubi_envelope C)
  : karoubi_envelope C
  := pr1 D.

Definition set_karoubi_envelope_isaset
  {C : category}
  (D : set_karoubi_envelope C)
  : isaset D
  := pr2 D.

(** * 2. Functors on C are equivalent to functors on the setcategory Karoubi envelope *)

Section Functors.

  Context {C : category}.
  Context (D : karoubi_envelope C).
  Context (E : category).
  Context (HE : Colims E).

  Section Iso.

    Context (P : D ⟶ E).
    Context (d : D).
    Context (c : C).
    Context (f : retraction d (karoubi_envelope_functor D c)).

    Definition karoubi_functor_iso_inv
      : E ⟦ P d, lan_point HE (karoubi_envelope_functor D) (functor_compose (karoubi_envelope_functor D) P) d⟧.
    Proof.
      refine (_ · colimIn _ ((
        (c ,, tt) ,, (f : _ --> _)
      ) : vertex (lan_comma _ _))).
      apply (#P).
      exact (retraction_section f).
    Defined.

    Lemma karoubi_functor_iso_is_inverse
      : is_inverse_in_precat
        ((counit_from_right_adjoint (is_right_adjoint_precomposition HE (karoubi_envelope_functor D)) P : _ ⟹ _) d)
        karoubi_functor_iso_inv.
    Proof.
      split.
      - refine (assoc _ _ _ @ _).
        apply colim_mor_eq.
        intro v.
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
        refine (maponpaths (λ x, x · _ · _) (lan_precomposition_counit_point_colimIn HE _ P d _ _ _) @ _).
        refine (!maponpaths (λ x, x · _) (functor_comp P _ _) @ _).
        refine (_ @ !id_right _).
        simple refine (_ @ colimInCommutes (lan_colim HE _ (pre_comp_functor _ P) _) v ((c ,, tt) ,, (f : _ --> _)) ((fully_faithful_inv_hom (karoubi_envelope_fully_faithful D) _ _ (pr2 v · retraction_section f) ,, pr2 iscontrunit _) ,, _)).
        + apply (maponpaths (λ x, #P x · _)).
          exact (!functor_on_fully_faithful_inv_hom _ _ _).
        + refine (_ @ !maponpaths (λ x, x · _) (functor_on_fully_faithful_inv_hom _ _ _)).
          refine (_ @ assoc _ _ _).
          apply maponpaths.
          exact (!retraction_is_retraction _).
      - refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (lan_precomposition_counit_point_colimIn HE _ P d _ _ _) @ _).
        refine (!functor_comp _ _ _ @ _).
        refine (_ @ functor_id P _).
        apply maponpaths.
        apply retraction_is_retraction.
    Qed.

  End Iso.

  Definition karoubi_functor_iso
    (P : D ⟶ E)
    : is_z_isomorphism (counit_from_right_adjoint (is_right_adjoint_precomposition HE (karoubi_envelope_functor D)) P).
  Proof.
    apply nat_trafo_z_iso_if_pointwise_z_iso.
    intro d.
    refine (factor_through_squash (isaprop_is_z_isomorphism _) _ (karoubi_envelope_objects_are_retracts D d)).
    intro c.
    refine (make_is_z_isomorphism _ _ (karoubi_functor_iso_is_inverse _ _ (pr1 c) (pr2 c))).
  Defined.

  Definition karoubi_pullback_equivalence
    : adj_equivalence_of_cats
      (pre_comp_functor (C := E) (karoubi_envelope_functor D)).
  Proof.
    use adj_equivalence_from_right_adjoint.
    - apply (is_right_adjoint_precomposition HE).
    - intro P.
      exact (z_iso_is_z_isomorphism (pre_comp_after_lan_iso _ (karoubi_envelope_fully_faithful D) _ HE P)).
    - exact karoubi_functor_iso.
  Defined.

End Functors.
