(**************************************************************************************************

  The Karoubi Envelope

  Defines the Karoubi envelope, the idempotent completion, the category of retracts or the Cauchy
  completion of a category C. This is the completion of C in which every idempotent splits. Its
  objects are the idempotent morphisms on objects of C.
  Equivalently, one can define the Karoubi envelope as a displayed category over the presheaf
  category over C, in which every presheaf is endowed with a retraction from the Yoneda embedding of
  some object in C.
  Presheaves (and functors) from C to a category with colimits (or coequalizers) can be lifted to
  functors on its Karoubi envelope, and this constitutes an adjoint equivalence.

  Contents
  1. The Karoubi envelope and its embedding of C
  1.1. The objects and morphisms and their constructors and accessors [karoubi_ob] [karoubi_mor]
  1.2. The category [karoubi_envelope]
  1.3. The embedding [karoubi_envelope_inclusion]
  1.1. Every object of the karoubi envelope is a retract of an element of C
    [karoubi_envelope_is_retract]
  1.2. Every idempotent in the karoubi envelope splits [karoubi_envelope_idempotent_splits]
  2. Functors on C are equivalent to functors on the Karoubi envelope [karoubi_pullback_equivalence]
  3. The alternative definition, using the presheaf category [karoubi_envelope']
  3.1. The equivalence between the two definitions [karoubi_equivalence]
  4. The formations of the opposite category and the Karoubi envelope commute [opp_karoubi]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Retracts.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.yoneda.

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

Section KaroubiEnvelope.

  Context (C : category).

(** * 1. The Karoubi envelope and its embedding of C *)
(** ** 1.1. The objects and morphisms and their constructors and accessors *)

  Definition karoubi_ob
    : UU
    := ∑ (X : C),
      idempotent X.

  Definition make_karoubi_ob
    (X : C)
    (f : C⟦X, X⟧)
    (H : f · f = f)
    : karoubi_ob
    := X ,, f ,, H.

  Coercion karoubi_ob_object
    (X : karoubi_ob)
    : C
    := pr1 X.

  Definition karoubi_ob_idempotent
    (X : karoubi_ob)
    : idempotent X
    := pr2 X.

  Definition karoubi_mor
    (X Y : karoubi_ob)
    : UU
    := ∑ (f : C⟦X, Y⟧),
      karoubi_ob_idempotent X · f = f ×
      f · karoubi_ob_idempotent Y = f.

  Definition make_karoubi_mor
    {X Y : karoubi_ob}
    (f : C⟦X, Y⟧)
    (Hl : karoubi_ob_idempotent X · f = f)
    (Hr : f · karoubi_ob_idempotent Y = f)
    : karoubi_mor X Y
    := f ,, Hl ,, Hr.

  Coercion karoubi_mor_morphism
    {X Y : karoubi_ob}
    (f : karoubi_mor X Y)
    : C⟦X, Y⟧
    := pr1 f.

  Definition karoubi_mor_commutes_left
    {X Y : karoubi_ob}
    (f : karoubi_mor X Y)
    : karoubi_ob_idempotent X · f = f
    := pr12 f.

  Definition karoubi_mor_commutes_right
    {X Y : karoubi_ob}
    (f : karoubi_mor X Y)
    : f · karoubi_ob_idempotent Y = f
    := pr22 f.

  Definition karoubi_mor_eq
    {X Y : karoubi_ob}
    (f g : karoubi_mor X Y)
    (H : pr1 f = pr1 g)
    : f = g.
  Proof.
    apply subtypePath.
    {
      intro x.
      apply isapropdirprod;
        apply homset_property.
    }
    exact H.
  Qed.

(** ** 1.2. The category *)

  Definition karoubi_envelope_ob_mor
    : precategory_ob_mor
    := make_precategory_ob_mor
      karoubi_ob
      karoubi_mor.

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

(** ** 1.3. The embedding *)

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
    exists (d : karoubi_ob).
    use (_ ,, _ ,, _).
    - exists (karoubi_ob_idempotent d).
      abstract (
        split;
        [ apply idempotent_is_idempotent
        | apply id_right ]
      ).
    - exists (karoubi_ob_idempotent d).
      abstract (
        split;
        [ apply id_left
        | apply idempotent_is_idempotent ]
      ).
    - abstract (
        apply karoubi_mor_eq;
        apply idempotent_is_idempotent
      ).
  Defined.

(** ** 1.2. Every idempotent in the karoubi envelope splits *)

  Definition karoubi_envelope_idempotent_splits
    (c : karoubi_envelope)
    (e : idempotent c)
    : is_split_idempotent e.
  Proof.
    use (_ ,, _ ,, _).
    - exists (c : karoubi_ob).
      exists ((e : c --> c) : karoubi_mor _ _).
      abstract exact (base_paths _ _ (idempotent_is_idempotent e)).
    - use (_ ,, _ ,, _).
      + exists ((e : c --> c) : karoubi_mor _ _).
        abstract (
          split;
          [ exact (base_paths _ _ (idempotent_is_idempotent e))
          | exact (karoubi_mor_commutes_right (e : c --> c)) ]
        ).
      + exists ((e : c --> c) : karoubi_mor _ _).
        abstract (
          split;
          [ exact (karoubi_mor_commutes_left (e : c --> c))
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
      refine (_ · colimIn _ ((
          (karoubi_ob_object c ,, tt) ,,
          (karoubi_ob_idempotent c : _ --> _) ,,
          id_left _ ,,
          idempotent_is_idempotent _
        ) : (vertex (lan_comma karoubi_envelope_inclusion c)))).
      apply (#P).
      use make_karoubi_mor.
      - exact (karoubi_ob_idempotent c).
      - apply idempotent_is_idempotent.
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
            ((karoubi_ob_object c ,, tt) ,, (make_karoubi_mor (X := make_karoubi_ob _ (identity _) _) (karoubi_ob_idempotent c) (id_left _) (idempotent_is_idempotent _)))
            ((pr12 v ,, pr2 iscontrunit _) ,, _));
        apply karoubi_mor_eq.
        + exact (pr222 v).
        + apply idpath.
      - refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (lan_precomposition_counit_point_colimIn HD _ P c _ _ _) @ _).
        refine (!functor_comp _ _ _ @ _).
        refine (_ @ functor_id P _).
        apply maponpaths.
        apply karoubi_mor_eq.
        apply idempotent_is_idempotent.
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

  Section AlternativeDefinition.

(** * 3. The alternative definition, using the presheaf category *)

    Definition karoubi_envelope'
      : category
      := full_subcat
        (PreShv C)
        (λ P, ∑ (A : C), retraction P (yoneda _ A)).

    Definition karoubi'_mor_eq
      {A B : karoubi_envelope'}
      (f f' : karoubi_envelope'⟦A, B⟧)
      (H : pr1 f = pr1 f')
      : f = f'
      := pathsdirprod H (pr1 (isapropunit _ _)).

    Definition make_karoubi'_z_iso
      {A B : karoubi_envelope'}
      (f : PreShv C⟦pr1 A, pr1 B⟧)
      (g : PreShv C⟦pr1 B, pr1 A⟧)
      (H : is_inverse_in_precat f g)
      : z_iso A B.
    Proof.
      refine ((f ,, tt) ,, (g ,, tt) ,, _).
      abstract now (
        induction H;
        split;
        apply karoubi'_mor_eq
      ).
    Defined.

(** ** 3.1. The equivalence between the two definitions *)

    Definition karoubi_equivalence_functor_data
      : functor_data karoubi_envelope karoubi_envelope'.
    Proof.
      use make_functor_data.
      - intro A.
        use (_ ,, _ ,, _ ,, _ ,, _).
        + exact (Equalizers_PreShv _ _ (identity _) (# (yoneda _) (pr12 A))).
        + exact (A : karoubi_ob).
        + apply EqualizerArrow.
        + apply (EqualizerIn _ _ (# (yoneda _) (karoubi_ob_idempotent A))).
          abstract (
            refine (id_right _ @ _);
            refine (_ @ functor_comp _ _ _);
            apply maponpaths;
            exact (!idempotent_is_idempotent _)
          ).
        + abstract (
            apply EqualizerInsEq;
            refine (assoc' _ _ _ @ _);
            refine (maponpaths _ (EqualizerCommutes _ _ _ _) @ _);
            refine (!EqualizerEqAr _ @ _);
            refine (_ @ !id_left _);
            apply id_right
          ).
      - intros A B f.
        refine (_ ,, tt).
        apply (EqualizerIn _ _ (EqualizerArrow _ · # (yoneda _) (f : karoubi_mor _ _))).
        abstract (
          do 2 refine (assoc' _ _ _ @ !_);
          apply maponpaths;
          refine (id_right _ @ _);
          refine (_ @ functor_comp _ _ _);
          apply maponpaths;
          exact (!karoubi_mor_commutes_right f)
        ).
    Defined.

    Lemma karoubi_equivalence_is_functor
      : is_functor karoubi_equivalence_functor_data.
    Proof.
      split.
      - intro A.
        apply karoubi'_mor_eq.
        refine (EqualizerInsEq _ _ _ _).
        refine (EqualizerCommutes _ _ _ _ @ _).
        refine (!EqualizerEqAr _ @ _).
        refine (_ @ !id_left _).
        apply id_right.
      - intros X Y Z f g.
        apply karoubi'_mor_eq.
        refine (EqualizerInsEq _ _ _ _).
        refine (EqualizerCommutes _ _ _ _ @ _).
        refine (_ @ assoc _ _ _).
        refine (_ @ !maponpaths (λ x, _ · x) (EqualizerCommutes _ _ _ _)).
        refine (_ @ assoc' _ _ _).
        refine (_ @ !maponpaths (λ x, x · _) (EqualizerCommutes _ _ _ _)).
        refine (_ @ assoc _ _ _).
        apply maponpaths.
        apply functor_comp.
    Qed.

    Definition karoubi_equivalence_functor
      : karoubi_envelope ⟶ karoubi_envelope'
      := make_functor
        karoubi_equivalence_functor_data
        karoubi_equivalence_is_functor.

    Section FullyFaithful.

      Context {A B : karoubi_envelope}.

      Definition karoubi_equivalence_invmap_mor
        (f : karoubi_equivalence_functor A --> karoubi_equivalence_functor B)
        : C⟦(A : karoubi_ob), (B : karoubi_ob)⟧
        := invmap (weq_from_fully_faithful (yoneda_fully_faithful C) _ _)
            (pr22 (karoubi_equivalence_functor A) ·
              pr1 f ·
              retraction_section (pr22 (karoubi_equivalence_functor B))).

      Lemma karoubi_equivalence_invmap_mor_left
        (f : karoubi_equivalence_functor A --> karoubi_equivalence_functor B)
        : karoubi_ob_idempotent A · karoubi_equivalence_invmap_mor f
          = karoubi_equivalence_invmap_mor f.
      Proof.
        refine (!invmap_eq _ _ _ (!_)).
        refine (functor_comp _ _ _ @ _).
        refine (maponpaths (λ x, _ · x) (homotweqinvweq (weq_from_fully_faithful _ _ _) _) @ _).
        do 2 refine (assoc _ _ _ @ maponpaths (λ x, x · _) _).
        apply EqualizerInsEq.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths (λ x, _ · x) (EqualizerCommutes _ _ _ _) @ _).
        refine (_ @ !EqualizerCommutes _ _ _ _).
        refine (!functor_comp _ _ _ @ _).
        apply maponpaths.
        apply idempotent_is_idempotent.
      Qed.

      Lemma karoubi_equivalence_invmap_mor_right
        (f : karoubi_equivalence_functor A --> karoubi_equivalence_functor B)
        : karoubi_equivalence_invmap_mor f · karoubi_ob_idempotent B
          = karoubi_equivalence_invmap_mor f.
      Proof.
        refine (!invmap_eq _ _ _ (!_)).
        refine (functor_comp _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (homotweqinvweq (weq_from_fully_faithful _ _ _) _) @ _).
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (!EqualizerEqAr _ @ _).
        apply id_right.
      Qed.

      Definition karoubi_equivalence_invmap
        (f : karoubi_equivalence_functor A --> karoubi_equivalence_functor B)
        : A --> B
        := karoubi_equivalence_invmap_mor f ,,
          karoubi_equivalence_invmap_mor_left f ,,
          karoubi_equivalence_invmap_mor_right f.

      Lemma karoubi_equivalence_invweqweq
        (f: karoubi_envelope⟦ A, B ⟧)
        : karoubi_equivalence_invmap (# karoubi_equivalence_functor f)
          = f.
      Proof.
        use subtypePath.
        {
          intro.
          apply isapropdirprod;
          apply homset_property.
        }
        apply invmap_eq.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (EqualizerCommutes _ _ _ _) @ _).
        refine (assoc _ _ _ @ _).
        refine (maponpaths (λ x, x · _) (EqualizerCommutes _ _ _ _) @ _).
        refine (!functor_comp _ _ _ @ _).
        apply maponpaths.
        apply karoubi_mor_commutes_left.
      Qed.

      Lemma karoubi_equivalence_weqinvweq
        (f : karoubi_equivalence_functor A --> karoubi_equivalence_functor B)
        : # karoubi_equivalence_functor (karoubi_equivalence_invmap f)
          = f.
      Proof.
        apply karoubi'_mor_eq.
        apply EqualizerInsEq.
        refine (EqualizerCommutes _ _ _ _ @ _).
        refine (maponpaths (λ x, _ · x) (homotweqinvweq (weq_from_fully_faithful _ _ _) _) @ _).
        refine (assoc _ _ _ @ _).
        apply (maponpaths (λ x, x · _)).
        refine (assoc _ _ _ @ _).
        refine (_ @ id_left _).
        apply (maponpaths (λ x, x · _)).
        apply EqualizerInsEq.
        refine (assoc' _ _ _ @ _).
        refine (maponpaths _ (EqualizerCommutes _ _ _ _) @ _).
        refine (_ @ !id_left _).
        refine (!EqualizerEqAr _ @ _).
        apply id_right.
      Qed.

    End FullyFaithful.

    Definition karoubi_equivalence_fully_faithful
      : fully_faithful karoubi_equivalence_functor
      := λ A B, isweq_iso _
        karoubi_equivalence_invmap
        karoubi_equivalence_invweqweq
        karoubi_equivalence_weqinvweq.

    Section SplitEssentiallySurjective.

      Context (P : karoubi_envelope').

      Definition karoubi_equivalence_preimage
        : karoubi_envelope.
      Proof.
        use make_karoubi_ob.
        - exact (pr12 P).
        - exact (invmap (weq_from_fully_faithful (yoneda_fully_faithful C) _ _)
            (pr22 P · retraction_section (pr22 P))).
        - abstract (
            apply (invmaponpathsweq (weq_from_fully_faithful (yoneda_fully_faithful C) _ _));
            refine (functor_comp _ _ _ @ _);
            refine (maponpaths (λ x, x · x) (homotweqinvweq (weq_from_fully_faithful _ _ _) _) @ _);
            refine (_ @ !(homotweqinvweq (weq_from_fully_faithful _ _ _) _));
            refine (assoc _ _ _ @ _);
            refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _);
            refine (maponpaths (λ x, _ · x · _) (retraction_is_retraction _) @ _);
            exact (maponpaths (λ x, x · _) (id_right _))
          ).
      Defined.

      Definition karoubi_equivalence_preimage_iso_mor
        : PreShv C⟦
          pr1 (karoubi_equivalence_functor karoubi_equivalence_preimage),
          pr1 P⟧
        := EqualizerArrow _ · retraction_retraction (pr22 P).

      Definition karoubi_equivalence_preimage_iso_inv
        : PreShv C⟦pr1 P,
          pr1 (karoubi_equivalence_functor karoubi_equivalence_preimage)⟧.
      Proof.
        use EqualizerIn.
        - apply (retraction_section (pr22 P)).
        - abstract (
            refine (_ @ !maponpaths (λ x, _ · x) (homotweqinvweq (weq_from_fully_faithful _ _ _) _));
            refine (_ @ assoc' _ _ _);
            refine (_ @ !maponpaths (λ x, x · _) (retraction_is_retraction _));
            refine (_ @ !id_left _);
            apply id_right
          ).
      Defined.

      Lemma karoubi_equivalence_preimage_is_inverse
        : is_inverse_in_precat
          karoubi_equivalence_preimage_iso_mor
          karoubi_equivalence_preimage_iso_inv.
      Proof.
        split.
        - apply EqualizerInsEq.
          refine (assoc' _ _ _ @ _).
          refine (maponpaths (λ x, _ · x) (EqualizerCommutes _ _ _ _) @ _).
          refine (assoc' _ _ _ @ _).
          refine (!maponpaths (λ x, _ · x) (homotweqinvweq (weq_from_fully_faithful (yoneda_fully_faithful C) _ _) _) @ _).
          refine (!EqualizerEqAr _ @ _).
          refine (_ @ !id_left _).
          apply id_right.
        - refine (assoc _ _ _ @ _).
          refine (maponpaths (λ x, x · _) (EqualizerCommutes _ _ _ _) @ _).
          apply retraction_is_retraction.
      Qed.

    End SplitEssentiallySurjective.

    Definition karoubi_equivalence_split_essentially_surjective
      : split_essentially_surjective karoubi_equivalence_functor
      := λ P,
        karoubi_equivalence_preimage P ,,
        make_karoubi'_z_iso _ _ (karoubi_equivalence_preimage_is_inverse P).

    Definition karoubi_equivalence
      : adj_equivalence_of_cats karoubi_equivalence_functor
      := rad_equivalence_of_cats' _ _ _
        karoubi_equivalence_fully_faithful
        karoubi_equivalence_split_essentially_surjective.

  End AlternativeDefinition.

End KaroubiEnvelope.

(** * 4. The formations of the opposite category and the Karoubi envelope commute *)

Section OppKaroubiEquiv.

  Context (C : category).

  Definition opp_karoubi_functor_data
    : functor_data (op_cat (karoubi_envelope C)) (karoubi_envelope (op_cat C)).
  Proof.
    use make_functor_data.
    - exact (idfun _).
    - intros a b.
      apply totalfun.
      intro f.
      exact (pr1weq (weqdirprodcomm _ _)).
  Defined.

  Lemma opp_karoubi_functor_is_functor
    : is_functor opp_karoubi_functor_data.
  Proof.
    split.
    - easy.
    - do 5 intro.
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
    := make_karoubi_mor _
      (karoubi_ob_idempotent _ c)
      (idempotent_is_idempotent _)
      (idempotent_is_idempotent _).

  Section OppKaroubiOfLiftIsUniversalArrow.

    Context (c : karoubi_envelope (op_cat C)).
    Context (c': op_cat (karoubi_envelope C)).
    Context (f: karoubi_envelope (op_cat C) ⟦ opp_karoubi_functor c', c ⟧).

    Definition opp_karoubi_universal_mor
      : op_cat (karoubi_envelope C) ⟦ c', opp_karoubi_ob_lift c ⟧.
    Proof.
      revert f.
      refine (totalfun _ _ _).
      intro f.
      exact (invmap (weqdirprodcomm _ _)).
    Defined.

    Lemma opp_karoubi_universal_eq
      : f = # opp_karoubi_functor opp_karoubi_universal_mor · opp_karoubi_ob_lift_mor c.
    Proof.
      apply karoubi_mor_eq.
      exact (!karoubi_mor_commutes_right _ f).
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
      exact (!karoubi_mor_commutes_left _ g).
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
      := make_karoubi_mor _
        (karoubi_ob_idempotent _ c)
        (idempotent_is_idempotent _)
        (idempotent_is_idempotent _).

    Lemma opp_karoubi_unit_is_inverse
      : is_inverse_in_precat (adjunit opp_karoubi_is_adjoint c) opp_karoubi_unit_iso_inv.
    Proof.
      split;
        apply karoubi_mor_eq;
        apply (idempotent_is_idempotent (karoubi_ob_idempotent _ c)).
    Qed.

    Definition opp_karoubi_unit_is_iso
      : is_z_isomorphism (adjunit opp_karoubi_is_adjoint c)
      := make_is_z_isomorphism _ _ opp_karoubi_unit_is_inverse.

  End OppKaroubiUnitIso.

  Section OppKaroubiCounitIso.

    Context (c : karoubi_envelope (op_cat C)).

    Definition opp_karoubi_counit_iso_inv
      : karoubi_envelope (op_cat C) ⟦ c, opp_karoubi_ob_lift c ⟧
      := make_karoubi_mor _
        (karoubi_ob_idempotent _ c)
        (idempotent_is_idempotent _)
        (idempotent_is_idempotent _).

    Lemma opp_karoubi_counit_is_inverse
      : is_inverse_in_precat (adjcounit opp_karoubi_is_adjoint c) opp_karoubi_counit_iso_inv.
    Proof.
      split;
        apply karoubi_mor_eq;
        apply (idempotent_is_idempotent (karoubi_ob_idempotent _ c)).
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
