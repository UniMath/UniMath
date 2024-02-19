(**************************************************************************************************

  The Karoubi Envelope

  Defines the Karoubi envelope, the idempotent completion, the category of retracts or the Cauchy
  completion of a category C. This is the completion of C in which every idempotent splits. Its
  objects are the idempotent morphisms on objects of C. Equivalently, one can define the Karoubi
  envelope as the category with an embedding from C such that every element is a retract of an
  object of C, and such that every idempotent splits.
  Presheaves (and functors) from C to a category with colimits (or coequalizers) can be lifted to
  functors on its Karoubi envelope, and this constitutes an adjoint equivalence.

  Contents
  1. The Karoubi envelope and its embedding of C [karoubi_envelope] [karoubi_envelope_inclusion]
  1.1. Every object of the karoubi envelope is a retract of an element of C
    [karoubi_envelope_is_retract]
  1.2. Every idempotent in the karoubi envelope splits [karoubi_envelope_idempotent_splits]
  2. Functors on C are equivalent to functors on the Karoubi envelope [karoubi_pullback_equivalence]
  3. The formations of the opposite category and the Karoubi envelope commute [opp_karoubi]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.Limits.Graphs.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Equalizers.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.SurjectivePrecomposition.

Local Open Scope cat.

Lemma retract_functor_is_equalizer
  {C D : category}
  (F : C ⟶ D)
  {a b : C}
  (H : retraction b a)
  : Equalizer D (#F (retraction_retraction H) · #F (retraction_section H)) (identity (F a)).
Proof.
  exact (retract_is_equalizer (functor_preserves_retraction F H)).
Defined.

Lemma retract_functor_is_coequalizer
  {C D : category}
  (F : C ⟶ D)
  {a b : C}
  (H : retraction b a)
  : Coequalizer D (#F (retraction_retraction H) · #F (retraction_section H)) (identity (F a)).
Proof.
  exact (retract_is_coequalizer (functor_preserves_retraction F H)).
Defined.

Section KaroubiEnvelope.

  Context (C : category).

(** * 1. The Karoubi envelope and its embedding of C *)

  Definition karoubi_envelope_ob_mor
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (∑ (c : C), idempotent c).
    - intros f f'.
      exact (∑ (g : C⟦pr1 f, pr1 f'⟧), pr12 f · g = g × g · pr12 f' = g).
  Defined.

  Definition make_karoubi_ob
    (c : C)
    (f : C⟦c, c⟧)
    (H : f · f = f)
    : karoubi_envelope_ob_mor
    := c ,, f ,, H.

  Definition make_karoubi_mor
    {c d : karoubi_envelope_ob_mor}
    (f : C⟦pr1 c, pr1 d⟧)
    (Hl : pr12 c · f = f)
    (Hr : f · pr12 d = f)
    : karoubi_envelope_ob_mor⟦c, d⟧
    := f ,, Hl ,, Hr.

  Definition karoubi_envelope_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact karoubi_envelope_ob_mor.
    - intro f.
      exact (make_karoubi_mor (pr12 f) (pr22 f) (pr22 f)).
    - intros f f' f'' g g'.
      use make_karoubi_mor.
      + exact (pr1 g · pr1 g').
      + abstract now rewrite assoc, (pr12 g).
      + abstract now rewrite assoc', (pr22 g').
  Defined.

  Definition karoubi_mor_eq
    {a b : karoubi_envelope_data}
    (f g : karoubi_envelope_data⟦a, b⟧)
    (H : pr1 f = pr1 g)
    : f = g.
  Proof.
    apply subtypePath.
    {
      intro c.
      apply isapropdirprod;
        apply homset_property.
    }
    exact H.
  Qed.

  Lemma karoubi_envelope_is_precategory
    : is_precategory karoubi_envelope_data.
  Proof.
    apply make_is_precategory_one_assoc.
    - intros m n f.
      apply karoubi_mor_eq.
      exact (pr12 f).
    - intros m n f.
      apply karoubi_mor_eq.
      exact (pr22 f).
    - intros k l m n f g h.
      apply karoubi_mor_eq.
      apply assoc.
  Qed.

  Lemma karoubi_envelope_has_homsets
    : has_homsets karoubi_envelope_data.
  Proof.
    intros m n.
    apply isaset_total2.
    - apply homset_property.
    - intro x.
      apply isasetaprop.
      apply isapropdirprod;
        apply homset_property.
  Qed.

  Definition karoubi_envelope
    : category
    := make_category
      (make_precategory
        karoubi_envelope_data
        karoubi_envelope_is_precategory)
      karoubi_envelope_has_homsets.

  Definition karoubi_envelope_inclusion
    : C ⟶ karoubi_envelope.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro c.
        exact (make_karoubi_ob c (identity _) (id_left _)).
      + intros a b f.
        use make_karoubi_mor.
        * exact f.
        * apply id_left.
        * apply id_right.
    - split.
      + abstract (
          intro a;
          now apply karoubi_mor_eq
        ).
      + abstract (
          intros a b c f g;
          now apply karoubi_mor_eq
        ).
  Defined.

  Lemma karoubi_envelope_inclusion_fully_faithful
    : fully_faithful karoubi_envelope_inclusion.
  Proof.
    intros c c'.
    use isweq_iso.
    - intro f.
      exact (pr1 f).
    - apply idpath.
    - intro f.
      now apply karoubi_mor_eq.
  Qed.

(** ** 1.1. Every object of the karoubi envelope is a retract of an element of C *)

  Definition karoubi_envelope_is_retract
    (d : karoubi_envelope)
    : ∑ c, retraction d (karoubi_envelope_inclusion c).
  Proof.
    exists (pr1 d).
    use (_ ,, _ ,, _).
    - exists (pr12 d).
      abstract (
        split;
        [ exact (idempotent_is_idempotent (pr2 d))
        | apply id_right ]
      ).
    - exists (pr12 d).
      abstract (
        split;
        [ apply id_left
        | exact (idempotent_is_idempotent (pr2 d)) ]
      ).
    - abstract (
        apply karoubi_mor_eq;
        apply (idempotent_is_idempotent (pr2 d))
      ).
  Defined.

(** ** 1.2. Every idempotent in the karoubi envelope splits *)

  Definition karoubi_envelope_idempotent_splits
    (c : karoubi_envelope)
    (e : idempotent c)
    : is_split_idempotent e.
  Proof.
    use (_ ,, _ ,, _).
    - exists (pr1 c).
      exists (pr1 (e : c --> c)).
      abstract exact (base_paths _ _ (idempotent_is_idempotent e)).
    - use (_ ,, _ ,, _).
      + exists (pr1 (e : c --> c)).
        abstract (
          split;
          [ exact (base_paths _ _ (idempotent_is_idempotent e))
          | exact (pr22 (e : c --> c)) ]
        ).
      + exists (pr1 (e : c --> c)).
        abstract (
          split;
          [ exact (pr12 (e : c --> c))
          | exact (base_paths _ _ (idempotent_is_idempotent e)) ]
        ).
      + abstract (
          apply karoubi_mor_eq;
          exact (base_paths _ _ (idempotent_is_idempotent e))
        ).
    - abstract (
        apply karoubi_mor_eq;
        exact (!base_paths _ _ (idempotent_is_idempotent e))
      ).
  Defined.

(** * 2. Functors on C are equivalent to functors on the Karoubi envelope *)

  Context (D : category).
  Context (HD : Colims D).

  Section Iso.

    Context (P : karoubi_envelope ⟶ D).
    Context (c : karoubi_envelope).

    Definition karoubi_functor_iso_inv
      : D ⟦ P c, lan_point HD karoubi_envelope_inclusion (functor_compose karoubi_envelope_inclusion P) c⟧.
    Proof.
      refine (_ · colimIn _ (((pr1 c ,, tt) ,, pr12 c ,, id_left _ ,, pr22 c) : (vertex (lan_comma karoubi_envelope_inclusion c)))).
      apply (#P).
      use make_karoubi_mor.
      - exact (pr12 c).
      - exact (pr22 c).
      - exact (id_right _).
    Defined.

    Lemma karoubi_functor_iso_is_inverse
      : is_inverse_in_precat
        (pr1 (Core.counit_from_right_adjoint (is_right_adjoint_precomposition HD karoubi_envelope_inclusion) P) c)
        karoubi_functor_iso_inv.
    Proof.
      split.
      - refine (assoc _ _ _ @ _).
        apply colim_mor_eq.
        intro v.
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _).
        refine (maponpaths (λ x, x · _ · _) (lan_precomposition_counit_point_colimIn HD _ P c _ _ _) @ _).
        refine (_ @ !id_right _).
        refine (!maponpaths (λ x, x · _) (functor_comp P _ _) @ _).
        use (maponpaths (λ x, #P x · _) _
          @ colimInCommutes
            (lan_colim HD karoubi_envelope_inclusion (pre_comp_functor karoubi_envelope_inclusion P) c)
            v
            ((pr1 c ,, tt) ,, (make_karoubi_mor (c := make_karoubi_ob _ (identity _) _) (pr12 c) (id_left _) (pr22 c)))
            ((pr12 v ,, (pr2 iscontrunit _)) ,, _));
        apply karoubi_mor_eq.
        + exact (pr222 v).
        + apply idpath.
      - refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (lan_precomposition_counit_point_colimIn HD _ P c _ _ _) @ _).
        refine (!functor_comp _ _ _ @ _).
        refine (_ @ functor_id P _).
        apply maponpaths.
        apply karoubi_mor_eq.
        exact (pr22 c).
    Qed.

  End Iso.

  Definition karoubi_functor_iso
    (P : karoubi_envelope ⟶ D)
    : is_z_isomorphism (Core.counit_from_right_adjoint (is_right_adjoint_precomposition HD karoubi_envelope_inclusion) P)
    := nat_trafo_z_iso_if_pointwise_z_iso _ _
      (λ c, (make_is_z_isomorphism _ _ (karoubi_functor_iso_is_inverse P c))).

  Definition karoubi_pullback_equivalence
    : adj_equivalence_of_cats
      (pre_comp_functor (C := D) karoubi_envelope_inclusion).
  Proof.
    use adj_equivalence_from_right_adjoint.
    - apply (is_right_adjoint_precomposition HD).
    - intro P.
      exact (z_iso_is_z_isomorphism (pre_comp_after_lan_iso _ karoubi_envelope_inclusion_fully_faithful _ HD P)).
    - exact karoubi_functor_iso.
  Defined.

End KaroubiEnvelope.

(** * 3. The formations of the opposite category and the Karoubi envelope commute *)

Section OppKaroubiEquiv.

  Context (C : category).

  Definition opp_karoubi_functor_data
    : functor_data (op_cat (karoubi_envelope C)) (karoubi_envelope (op_cat C)).
  Proof.
    use make_functor_data.
    - exact (idfun _).
    - intros a b f.
      use make_karoubi_mor.
      + exact (pr1 f).
      + exact (pr22 f).
      + exact (pr12 f).
  Defined.

  Lemma opp_karoubi_functor_is_functor
    : is_functor opp_karoubi_functor_data.
  Proof.
    split.
    - easy.
    - intros a b c f g.
      now apply karoubi_mor_eq.
  Qed.

  Definition opp_karoubi_functor
    : op_cat (karoubi_envelope C) ⟶ karoubi_envelope (op_cat C)
    := make_functor _ opp_karoubi_functor_is_functor.

  Definition opp_karoubi_ob_lift
    : karoubi_envelope (op_cat C) → op_cat (karoubi_envelope C)
    := idfun _.

  Definition opp_karoubi_ob_lift_mor
    (c : karoubi_envelope (op_cat C))
    : karoubi_envelope (op_cat C) ⟦ opp_karoubi_functor (opp_karoubi_ob_lift c), c ⟧
    := make_karoubi_mor _ (pr12 c) (pr22 c) (pr22 c).

  Section OppKaroubiOfLiftIsUniversalArrow.

    Context (c : karoubi_envelope (op_cat C)).
    Context (c': op_cat (karoubi_envelope C)).
    Context (f: karoubi_envelope (op_cat C) ⟦ opp_karoubi_functor c', c ⟧).

    Definition opp_karoubi_universal_mor
      : op_cat (karoubi_envelope C) ⟦ c', opp_karoubi_ob_lift c ⟧.
    Proof.
      use make_karoubi_mor.
      - exact (pr1 f).
      - exact (pr22 f).
      - exact (pr12 f).
    Defined.

    Lemma opp_karoubi_universal_eq
      : f = # opp_karoubi_functor opp_karoubi_universal_mor · opp_karoubi_ob_lift_mor c.
    Proof.
      apply karoubi_mor_eq.
      exact (!pr22 f).
    Qed.

    Lemma opp_karoubi_universal_prop
      (g : op_cat (karoubi_envelope C) ⟦ c', opp_karoubi_ob_lift c ⟧)
      : isaprop (f = # opp_karoubi_functor g · opp_karoubi_ob_lift_mor c).
    Proof.
      apply homset_property.
    Qed.

    Lemma opp_karoubi_universal_eq'
      (g: op_cat (karoubi_envelope C) ⟦ c', opp_karoubi_ob_lift c ⟧)
      (H: f = # opp_karoubi_functor g · opp_karoubi_ob_lift_mor c)
      : g = opp_karoubi_universal_mor.
    Proof.
      apply karoubi_mor_eq.
      refine (_ @ !base_paths _ _ H).
      exact (!pr12 g).
    Qed.

    Definition opp_karoubi_universal
      : ∃! f', f = # opp_karoubi_functor f' · opp_karoubi_ob_lift_mor c
      := unique_exists
        opp_karoubi_universal_mor
        opp_karoubi_universal_eq
        opp_karoubi_universal_prop
        opp_karoubi_universal_eq'.

  End OppKaroubiOfLiftIsUniversalArrow.

  Definition opp_karoubi_is_adjoint
    : is_left_adjoint opp_karoubi_functor
    := left_adjoint_from_partial _
      opp_karoubi_ob_lift
      opp_karoubi_ob_lift_mor
      opp_karoubi_universal.

  Section OppKaroubiUnitIso.

    Context (c : op_cat (karoubi_envelope C)).

    Definition opp_karoubi_unit_iso_inv
      : karoubi_envelope C ⟦ c, c ⟧
      := make_karoubi_mor _ (pr12 c) (pr22 c) (pr22 c).

    Lemma opp_karoubi_unit_is_inverse
      : is_inverse_in_precat (adjunit opp_karoubi_is_adjoint c) opp_karoubi_unit_iso_inv.
    Proof.
      split.
      - apply karoubi_mor_eq.
        exact (pr22 c).
      - apply karoubi_mor_eq.
        exact (pr22 c).
    Qed.

    Definition opp_karoubi_unit_is_iso
      : is_z_isomorphism (adjunit opp_karoubi_is_adjoint c)
      := make_is_z_isomorphism _ _ opp_karoubi_unit_is_inverse.

  End OppKaroubiUnitIso.

  Section OppKaroubiCounitIso.

    Context (c : karoubi_envelope (op_cat C)).

    Definition opp_karoubi_counit_iso_inv
      : karoubi_envelope (op_cat C) ⟦ c, opp_karoubi_ob_lift c ⟧
      := make_karoubi_mor _ (pr12 c) (pr22 c) (pr22 c).

    Lemma opp_karoubi_counit_is_inverse
      : is_inverse_in_precat (adjcounit opp_karoubi_is_adjoint c) opp_karoubi_counit_iso_inv.
    Proof.
      split.
      - apply karoubi_mor_eq.
        exact (pr22 c).
      - apply karoubi_mor_eq.
        exact (pr22 c).
    Qed.

    Definition opp_karoubi_counit_is_iso
      : is_z_isomorphism (adjcounit opp_karoubi_is_adjoint c)
      := make_is_z_isomorphism _ _ opp_karoubi_counit_is_inverse.

  End OppKaroubiCounitIso.

  Definition opp_karoubi
    : adj_equiv (op_cat (karoubi_envelope C)) (karoubi_envelope (op_cat C))
    := opp_karoubi_functor ,,
      opp_karoubi_is_adjoint ,,
      opp_karoubi_unit_is_iso ,,
      opp_karoubi_counit_is_iso.

End OppKaroubiEquiv.
