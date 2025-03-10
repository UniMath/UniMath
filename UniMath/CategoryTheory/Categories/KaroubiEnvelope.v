(**************************************************************************************************

  The Karoubi Envelope

  Defines the Karoubi envelope, the idempotent completion, the category of retracts or the Cauchy
  completion of a category C. This is the completion of C in which every idempotent splits. Its
  objects are the idempotent morphisms on objects of C.
  The fully faithful embedding of C into this Karoubi envelope induces an equivalence on
  isomorphisms, but also an equivalence on path types. Using these equivalences, one can show that
  C is univalent if its Karoubi envelope is. Note that the converse does not necessarily hold: C
  can be univalent when the Karoubi envelope is not univalent.
  One can also define the Karoubi envelope as a displayed category over the presheaf category over
  C, in which every presheaf is endowed with a retraction from the Yoneda embedding of some object
  in C.
  Presheaves (and functors) from C to a category with colimits (or coequalizers) can be lifted to
  functors on its Karoubi envelope, and this constitutes an adjoint equivalence.

  Contents
  1. The Karoubi envelope and its embedding of C
  1.1. The objects and morphisms and their constructors and accessors [set_karoubi_ob] [set_karoubi_mor]
  1.2. The category [set_karoubi]
  1.3. The embedding [set_karoubi_inclusion]
  1.4. Every object of the karoubi envelope is a retract of an element of C
    [set_karoubi_is_retract]
  1.5. Every idempotent in the karoubi envelope splits [set_karoubi_idempotent_splits]
  1.6. If the karoubi envelope is univalent, C is univalent [set_karoubi_univalence]
  2. Functors on C are equivalent to functors on the Karoubi envelope [set_karoubi_pullback_equivalence]
  3. The alternative definition, using the presheaf category [set_karoubi_envelope']
  3.1. The equivalence between the two definitions [set_karoubi_equivalence]
  4. The formations of the opposite category and the Karoubi envelope commute [opp_set_karoubi]
  5. The Karoubi envelope construction gives a monad on the category of setcategories
    [set_karoubi_monad]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.LeftKanExtension.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Monads.Monads.
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

(* Data *)

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

(* Karoubi envelope *)

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

(* Univalent *)

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

(* Set *)

Definition set_karoubi_envelope
  (C : category)
  : UU
  := ∑ (D : karoubi_envelope C), is_setcategory D.

Definition make_set_karoubi_envelope
  {C : category}
  (D : karoubi_envelope C)
  (H : is_setcategory D)
  : set_karoubi_envelope C
  := D ,, H.

Coercion set_karoubi_envelope_to_karoubi_envelope
  {C : category}
  (D : set_karoubi_envelope C)
  : karoubi_envelope C
  := pr1 D.

Definition set_karoubi_envelope_is_setcategory
  {C : category}
  (D : set_karoubi_envelope C)
  : is_setcategory D
  := pr2 D.

Section SetKaroubi.

  Context (C : category).

(** * 1. The setcategory Karoubi envelope and its embedding of C *)
(** ** 1.1. The objects and morphisms and their constructors and accessors *)

  Definition set_karoubi_ob
    : UU
    := ∑ (X : C),
      idempotent X.

  Definition make_set_karoubi_ob
    (X : C)
    (f : C⟦X, X⟧)
    (H : f · f = f)
    : set_karoubi_ob
    := X ,, f ,, H.

  Coercion set_karoubi_ob_object
    (X : set_karoubi_ob)
    : C
    := pr1 X.

  Definition set_karoubi_ob_idempotent
    (X : set_karoubi_ob)
    : idempotent X
    := pr2 X.

  Definition set_karoubi_mor
    (X Y : set_karoubi_ob)
    : UU
    := ∑ (f : C⟦X, Y⟧),
      set_karoubi_ob_idempotent X · f = f ×
      f · set_karoubi_ob_idempotent Y = f.

  Definition make_set_karoubi_mor
    {X Y : set_karoubi_ob}
    (f : C⟦X, Y⟧)
    (Hl : set_karoubi_ob_idempotent X · f = f)
    (Hr : f · set_karoubi_ob_idempotent Y = f)
    : set_karoubi_mor X Y
    := f ,, Hl ,, Hr.

  Coercion set_karoubi_mor_morphism
    {X Y : set_karoubi_ob}
    (f : set_karoubi_mor X Y)
    : C⟦X, Y⟧
    := pr1 f.

  Definition set_karoubi_mor_commutes_left
    {X Y : set_karoubi_ob}
    (f : set_karoubi_mor X Y)
    : set_karoubi_ob_idempotent X · f = f
    := pr12 f.

  Definition set_karoubi_mor_commutes_right
    {X Y : set_karoubi_ob}
    (f : set_karoubi_mor X Y)
    : f · set_karoubi_ob_idempotent Y = f
    := pr22 f.

  Definition set_karoubi_mor_eq
    {X Y : set_karoubi_ob}
    (f g : set_karoubi_mor X Y)
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

  Definition set_karoubi_ob_mor
    : precategory_ob_mor
    := make_precategory_ob_mor
      set_karoubi_ob
      set_karoubi_mor.

  Definition set_karoubi_cat_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact set_karoubi_ob_mor.
    - intro f.
      exact (make_set_karoubi_mor (pr12 f) (pr22 f) (pr22 f)).
    - intros f f' f'' g g'.
      use make_set_karoubi_mor.
      + exact (pr1 g · pr1 g').
      + abstract now rewrite assoc, (pr12 g).
      + abstract now rewrite assoc', (pr22 g').
  Defined.

  Lemma set_karoubi_is_precategory
    : is_precategory set_karoubi_cat_data.
  Proof.
    apply make_is_precategory_one_assoc.
    - intros m n f.
      apply set_karoubi_mor_eq.
      exact (pr12 f).
    - intros m n f.
      apply set_karoubi_mor_eq.
      exact (pr22 f).
    - intros k l m n f g h.
      apply set_karoubi_mor_eq.
      apply assoc.
  Qed.

  Lemma set_karoubi_has_homsets
    : has_homsets set_karoubi_cat_data.
  Proof.
    intros m n.
    apply isaset_total2.
    - apply homset_property.
    - intro x.
      apply isasetaprop.
      apply isapropdirprod;
        apply homset_property.
  Qed.

  Definition set_karoubi_cat
    : category
    := make_category
      (make_precategory
        set_karoubi_cat_data
        set_karoubi_is_precategory)
      set_karoubi_has_homsets.

(** ** 1.3. The embedding *)

  Definition set_karoubi_inclusion
    : C ⟶ set_karoubi_cat.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro c.
        exact (make_set_karoubi_ob c (identity _) (id_left _)).
      + intros a b f.
        use make_set_karoubi_mor.
        * exact f.
        * apply id_left.
        * apply id_right.
    - apply make_is_functor.
      + abstract (
          intro a;
          now apply set_karoubi_mor_eq
        ).
      + abstract (
          intros a b c f g;
          now apply set_karoubi_mor_eq
        ).
  Defined.

  Lemma set_karoubi_inclusion_fully_faithful
    : fully_faithful set_karoubi_inclusion.
  Proof.
    intros c c'.
    use isweq_iso.
    - intro f.
      exact (pr1 f).
    - abstract reflexivity.
    - abstract (
        intro f;
        now apply set_karoubi_mor_eq
      ).
  Defined.

(** ** 1.5. Every idempotent in the setcategory karoubi envelope splits *)

  Definition set_karoubi_idempotent_splits
    (c : set_karoubi_cat)
    (e : idempotent c)
    : is_split_idempotent e.
  Proof.
    use (_ ,, _ ,, _).
    - exists (c : set_karoubi_ob).
      exists ((e : c --> c) : set_karoubi_mor _ _).
      abstract exact (base_paths _ _ (idempotent_is_idempotent e)).
    - use (_ ,, _ ,, _).
      + exists ((e : c --> c) : set_karoubi_mor _ _).
        abstract (
          split;
          [ exact (base_paths _ _ (idempotent_is_idempotent e))
          | exact (set_karoubi_mor_commutes_right (e : c --> c)) ]
        ).
      + exists ((e : c --> c) : set_karoubi_mor _ _).
        abstract (
          split;
          [ exact (set_karoubi_mor_commutes_left (e : c --> c))
          | exact (base_paths _ _ (idempotent_is_idempotent e)) ]
        ).
      + abstract (
          apply set_karoubi_mor_eq;
          exact (base_paths _ _ (idempotent_is_idempotent e))
        ).
    - abstract (
        apply set_karoubi_mor_eq;
        exact (!base_paths _ _ (idempotent_is_idempotent e))
      ).
  Defined.

(** ** 1.4. Every object of the setcategory karoubi envelope is a retract of an element of C *)

  Definition set_karoubi_is_retract
    (d : set_karoubi_cat)
    : ∑ c, retraction d (set_karoubi_inclusion c).
  Proof.
    exists (d : set_karoubi_ob).
    use (_ ,, _ ,, _).
    - exists (set_karoubi_ob_idempotent d).
      abstract (
        split;
        [ apply idempotent_is_idempotent
        | apply id_right ]
      ).
    - exists (set_karoubi_ob_idempotent d).
      abstract (
        split;
        [ apply id_left
        | apply idempotent_is_idempotent ]
      ).
    - abstract (
        apply set_karoubi_mor_eq;
        apply idempotent_is_idempotent
      ).
  Defined.

(** ** 1.6. If the karoubi envelope is univalent, C is univalent *)

  Definition set_karoubi_embedding_paths_weq
    (X Y : C)
    : (X = Y) ≃ (set_karoubi_inclusion X = set_karoubi_inclusion Y).
  Proof.
    use weq_iso.
    - intro h.
      use total2_paths_f.
      + exact h.
      + now induction h.
    - exact (base_paths _ _).
    - abstract (
        intro h;
        now induction h
      ).
    - abstract (
        intro h;
        refine (_ @ total2_fiber_paths _);
        apply maponpaths;
        refine (pr1 ((_ : isaset _) _ _ _ _));
        refine (isaset_carrier_subset (homset _ _) (λ _, make_hProp _ _));
        apply homset_property
      ).
  Defined.

  Lemma set_karoubi_univalence
    (H : is_univalent set_karoubi_cat)
    : is_univalent C.
  Proof.
    intros X Y.
    use weqhomot.
    - refine (_ ∘ set_karoubi_embedding_paths_weq X Y)%weq.
      refine (_ ∘ make_weq _ (H _ _))%weq.
      exact (invweq (weq_ff_functor_on_z_iso set_karoubi_inclusion_fully_faithful _ _)).
    - abstract (
        intro h;
        apply z_iso_eq;
        now induction h
      ).
  Defined.

  Definition set_karoubi_data
    : karoubi_envelope_data C
    := make_karoubi_envelope_data
        set_karoubi_cat
        set_karoubi_inclusion.

End SetKaroubi.

Lemma set_karoubi_is_karoubi
  (C : category)
  : is_karoubi_envelope (set_karoubi_data C).
Proof.
  use make_is_karoubi_envelope.
  - intros X f.
    apply hinhpr.
    apply set_karoubi_idempotent_splits.
  - apply set_karoubi_inclusion_fully_faithful.
  - intros X.
    apply hinhpr.
    apply set_karoubi_is_retract.
Qed.

Lemma isaset_set_karoubi
  (C : setcategory)
  : is_setcategory (set_karoubi_cat C).
Proof.
  split.
  - apply isaset_total2.
    + apply isaset_ob.
    + intro x.
      refine (isaset_carrier_subset (homset _ _) (λ _, make_hProp _ _)).
      apply homset_property.
  - apply homset_property.
Qed.

Definition set_karoubi
  (C : setcategory)
  : set_karoubi_envelope C
  := make_set_karoubi_envelope
    (make_karoubi_envelope
      (set_karoubi_data C)
      (set_karoubi_is_karoubi C))
    (isaset_set_karoubi C).

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

    Definition set_karoubi_functor_iso_inv
      : E ⟦ P d, lan_point HE (karoubi_envelope_functor D) (functor_compose (karoubi_envelope_functor D) P) d⟧.
    Proof.
      refine (_ · colimIn _ ((
        (c ,, tt) ,, (f : _ --> _)
      ) : vertex (lan_comma _ _))).
      apply (#P).
      exact (retraction_section f).
    Defined.

    Lemma set_karoubi_functor_iso_is_inverse
      : is_inverse_in_precat
        (pr1 (Core.counit_from_right_adjoint (is_right_adjoint_precomposition HE (karoubi_envelope_functor D)) P) d)
        set_karoubi_functor_iso_inv.
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

  Definition set_karoubi_functor_iso
    (P : D ⟶ E)
    : is_z_isomorphism (Core.counit_from_right_adjoint (is_right_adjoint_precomposition HE (karoubi_envelope_functor D)) P).
  Proof.
    apply nat_trafo_z_iso_if_pointwise_z_iso.
    intro d.
    refine (factor_through_squash (isaprop_is_z_isomorphism _) _ (karoubi_envelope_objects_are_retracts D d)).
    intro c.
    refine (make_is_z_isomorphism _ _ (set_karoubi_functor_iso_is_inverse _ _ (pr1 c) (pr2 c))).
  Defined.

  Definition set_karoubi_pullback_equivalence
    : adj_equivalence_of_cats
      (pre_comp_functor (C := E) (karoubi_envelope_functor D)).
  Proof.
    use adj_equivalence_from_right_adjoint.
    - apply (is_right_adjoint_precomposition HE).
    - intro P.
      exact (z_iso_is_z_isomorphism (pre_comp_after_lan_iso _ (karoubi_envelope_fully_faithful D) _ HE P)).
    - exact set_karoubi_functor_iso.
  Defined.

End Functors.

Section AlternativeDefinition.

  Context (C : category).

(** * 3. The alternative definition, using the presheaf category *)

  Definition set_karoubi'
    : category
    := full_subcat
      (PreShv C)
      (λ P, ∑ (A : C), retraction P (yoneda _ A)).

  Lemma set_karoubi'_mor_eq
    {A B : set_karoubi'}
    (f f' : set_karoubi'⟦A, B⟧)
    (H : pr1 f = pr1 f')
    : f = f'.
  Proof.
    use pathsdirprod.
    - apply H.
    - apply isapropunit.
  Qed.

  Definition make_set_karoubi'_z_iso
    {A B : set_karoubi'}
    (f : PreShv C⟦pr1 A, pr1 B⟧)
    (g : PreShv C⟦pr1 B, pr1 A⟧)
    (H : is_inverse_in_precat f g)
    : z_iso A B.
  Proof.
    refine ((f ,, tt) ,, (g ,, tt) ,, _).
    abstract now (
      induction H;
      split;
      apply set_karoubi'_mor_eq
    ).
  Defined.

(** ** 3.1. The equivalence between the two definitions *)

  Definition set_karoubi_equivalence_functor_data
    : functor_data (set_karoubi_cat C) set_karoubi'.
  Proof.
    use make_functor_data.
    - intro A.
      use (_ ,, _ ,, _ ,, _ ,, _).
      + exact (Equalizers_PreShv _ _ (identity _) (# (yoneda _) (pr12 A))).
      + exact (A : set_karoubi_ob _).
      + apply EqualizerArrow.
      + apply (EqualizerIn _ _ (# (yoneda _) (set_karoubi_ob_idempotent _ A))).
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
      apply (EqualizerIn _ _ (EqualizerArrow _ · # (yoneda _) (f : set_karoubi_mor _ _ _))).
      abstract (
        do 2 refine (assoc' _ _ _ @ !_);
        apply maponpaths;
        refine (id_right _ @ _);
        refine (_ @ functor_comp _ _ _);
        apply maponpaths;
        exact (!set_karoubi_mor_commutes_right _ f)
      ).
  Defined.

  Lemma set_karoubi_equivalence_is_functor
    : is_functor set_karoubi_equivalence_functor_data.
  Proof.
    apply make_is_functor.
    - intro A.
      apply set_karoubi'_mor_eq.
      refine (EqualizerInsEq _ _ _ _).
      refine (EqualizerCommutes _ _ _ _ @ _).
      refine (!EqualizerEqAr _ @ _).
      refine (_ @ !id_left _).
      apply id_right.
    - intros X Y Z f g.
      apply set_karoubi'_mor_eq.
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

  Definition set_karoubi_equivalence_functor
    : set_karoubi_cat C ⟶ set_karoubi'
    := make_functor
      set_karoubi_equivalence_functor_data
      set_karoubi_equivalence_is_functor.

  Section FullyFaithful.

    Context {A B : set_karoubi_cat C}.

    Definition set_karoubi_equivalence_invmap_mor
      (f : set_karoubi_equivalence_functor A --> set_karoubi_equivalence_functor B)
      : C⟦(A : set_karoubi_ob C), (B : set_karoubi_ob C)⟧
      := invmap (weq_from_fully_faithful (yoneda_fully_faithful C) _ _)
          (pr22 (set_karoubi_equivalence_functor A) ·
            pr1 f ·
            retraction_section (pr22 (set_karoubi_equivalence_functor B))).

    Lemma set_karoubi_equivalence_invmap_mor_left
      (f : set_karoubi_equivalence_functor A --> set_karoubi_equivalence_functor B)
      : set_karoubi_ob_idempotent _ A · set_karoubi_equivalence_invmap_mor f
        = set_karoubi_equivalence_invmap_mor f.
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

    Lemma set_karoubi_equivalence_invmap_mor_right
      (f : set_karoubi_equivalence_functor A --> set_karoubi_equivalence_functor B)
      : set_karoubi_equivalence_invmap_mor f · set_karoubi_ob_idempotent _ B
        = set_karoubi_equivalence_invmap_mor f.
    Proof.
      refine (!invmap_eq _ _ _ (!_)).
      refine (functor_comp _ _ _ @ _).
      refine (maponpaths (λ x, x · _) (homotweqinvweq (weq_from_fully_faithful _ _ _) _) @ _).
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!EqualizerEqAr _ @ _).
      apply id_right.
    Qed.

    Definition set_karoubi_equivalence_invmap
      (f : set_karoubi_equivalence_functor A --> set_karoubi_equivalence_functor B)
      : A --> B
      := set_karoubi_equivalence_invmap_mor f ,,
        set_karoubi_equivalence_invmap_mor_left f ,,
        set_karoubi_equivalence_invmap_mor_right f.

    Lemma set_karoubi_equivalence_invweqweq
      (f: set_karoubi_cat C⟦ A, B ⟧)
      : set_karoubi_equivalence_invmap (# set_karoubi_equivalence_functor f)
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
      apply set_karoubi_mor_commutes_left.
    Qed.

    Lemma set_karoubi_equivalence_weqinvweq
      (f : set_karoubi_equivalence_functor A --> set_karoubi_equivalence_functor B)
      : # set_karoubi_equivalence_functor (set_karoubi_equivalence_invmap f)
        = f.
    Proof.
      apply set_karoubi'_mor_eq.
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

  Definition set_karoubi_equivalence_fully_faithful
    : fully_faithful set_karoubi_equivalence_functor
    := λ A B, isweq_iso _
      set_karoubi_equivalence_invmap
      set_karoubi_equivalence_invweqweq
      set_karoubi_equivalence_weqinvweq.

  Section SplitEssentiallySurjective.

    Context (P : set_karoubi').

    Definition set_karoubi_equivalence_preimage
      : set_karoubi_cat C.
    Proof.
      use make_set_karoubi_ob.
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

    Definition set_karoubi_equivalence_preimage_iso_mor
      : PreShv C⟦
        pr1 (set_karoubi_equivalence_functor set_karoubi_equivalence_preimage),
        pr1 P⟧
      := EqualizerArrow _ · retraction_retraction (pr22 P).

    Definition set_karoubi_equivalence_preimage_iso_inv
      : PreShv C⟦pr1 P,
        pr1 (set_karoubi_equivalence_functor set_karoubi_equivalence_preimage)⟧.
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

    Lemma set_karoubi_equivalence_preimage_is_inverse
      : is_inverse_in_precat
        set_karoubi_equivalence_preimage_iso_mor
        set_karoubi_equivalence_preimage_iso_inv.
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

  Definition set_karoubi_equivalence_split_essentially_surjective
    : split_essentially_surjective set_karoubi_equivalence_functor
    := λ P,
      set_karoubi_equivalence_preimage P ,,
      make_set_karoubi'_z_iso _ _ (set_karoubi_equivalence_preimage_is_inverse P).

  Definition set_karoubi_equivalence
    : adj_equivalence_of_cats set_karoubi_equivalence_functor
    := rad_equivalence_of_cats' _ _ _
      set_karoubi_equivalence_fully_faithful
      set_karoubi_equivalence_split_essentially_surjective.

End AlternativeDefinition.

(** * 4. The formations of the opposite category and the Karoubi envelope commute *)

Section OppKaroubiEquiv.

  Context (C : category).

  Definition opp_set_karoubi_functor_data
    : functor_data (op_cat (set_karoubi_cat C)) (set_karoubi_cat (op_cat C)).
  Proof.
    use make_functor_data.
    - exact (idfun _).
    - intros a b.
      apply totalfun.
      intro f.
      exact (pr1weq (weqdirprodcomm _ _)).
  Defined.

  Lemma opp_set_karoubi_functor_is_functor
    : is_functor opp_set_karoubi_functor_data.
  Proof.
    apply make_is_functor.
    - easy.
    - do 5 intro.
      now apply set_karoubi_mor_eq.
  Qed.

  Definition opp_set_karoubi_functor
    : op_cat (set_karoubi_cat C) ⟶ set_karoubi_cat (op_cat C)
    := make_functor _ opp_set_karoubi_functor_is_functor.

  Definition opp_set_karoubi_ob_lift
    : set_karoubi_cat (op_cat C) → op_cat (set_karoubi_cat C)
    := idfun _.

  Definition opp_set_karoubi_ob_lift_mor
    (c : set_karoubi_cat (op_cat C))
    : set_karoubi_cat (op_cat C) ⟦ opp_set_karoubi_functor (opp_set_karoubi_ob_lift c), c ⟧
    := make_set_karoubi_mor _
      (set_karoubi_ob_idempotent _ c)
      (idempotent_is_idempotent _)
      (idempotent_is_idempotent _).

  Section OppKaroubiOfLiftIsUniversalArrow.

    Context (c : set_karoubi_cat (op_cat C)).
    Context (c': op_cat (set_karoubi_cat C)).
    Context (f: set_karoubi_cat (op_cat C) ⟦ opp_set_karoubi_functor c', c ⟧).

    Definition opp_set_karoubi_universal_mor
      : op_cat (set_karoubi_cat C) ⟦ c', opp_set_karoubi_ob_lift c ⟧.
    Proof.
      revert f.
      refine (totalfun _ _ _).
      intro f.
      exact (invmap (weqdirprodcomm _ _)).
    Defined.

    Lemma opp_set_karoubi_universal_eq
      : f = # opp_set_karoubi_functor opp_set_karoubi_universal_mor · opp_set_karoubi_ob_lift_mor c.
    Proof.
      apply set_karoubi_mor_eq.
      exact (!set_karoubi_mor_commutes_right _ f).
    Qed.

    Lemma opp_set_karoubi_universal_prop
      (g : op_cat (set_karoubi_cat C) ⟦ c', opp_set_karoubi_ob_lift c ⟧)
      : isaprop (f = # opp_set_karoubi_functor g · opp_set_karoubi_ob_lift_mor c).
    Proof.
      apply homset_property.
    Qed.

    Lemma opp_set_karoubi_universal_eq'
      (g: op_cat (set_karoubi_cat C) ⟦ c', opp_set_karoubi_ob_lift c ⟧)
      (H: f = # opp_set_karoubi_functor g · opp_set_karoubi_ob_lift_mor c)
      : g = opp_set_karoubi_universal_mor.
    Proof.
      apply set_karoubi_mor_eq.
      refine (_ @ !base_paths _ _ H).
      exact (!set_karoubi_mor_commutes_left _ g).
    Qed.

    Definition opp_set_karoubi_universal
      : ∃! f', f = # opp_set_karoubi_functor f' · opp_set_karoubi_ob_lift_mor c
      := unique_exists
        opp_set_karoubi_universal_mor
        opp_set_karoubi_universal_eq
        opp_set_karoubi_universal_prop
        opp_set_karoubi_universal_eq'.

  End OppKaroubiOfLiftIsUniversalArrow.

  Definition opp_set_karoubi_is_adjoint
    : is_left_adjoint opp_set_karoubi_functor
    := left_adjoint_from_partial _
      opp_set_karoubi_ob_lift
      opp_set_karoubi_ob_lift_mor
      opp_set_karoubi_universal.

  Section OppKaroubiUnitIso.

    Context (c : op_cat (set_karoubi_cat C)).

    Definition opp_set_karoubi_unit_iso_inv
      : set_karoubi_cat C ⟦ c, c ⟧
      := make_set_karoubi_mor _
        (set_karoubi_ob_idempotent _ c)
        (idempotent_is_idempotent _)
        (idempotent_is_idempotent _).

    Lemma opp_set_karoubi_unit_is_inverse
      : is_inverse_in_precat (adjunit opp_set_karoubi_is_adjoint c) opp_set_karoubi_unit_iso_inv.
    Proof.
      split;
        apply set_karoubi_mor_eq;
        apply (idempotent_is_idempotent (set_karoubi_ob_idempotent _ c)).
    Qed.

    Definition opp_set_karoubi_unit_is_iso
      : is_z_isomorphism (adjunit opp_set_karoubi_is_adjoint c)
      := make_is_z_isomorphism _ _ opp_set_karoubi_unit_is_inverse.

  End OppKaroubiUnitIso.

  Section OppKaroubiCounitIso.

    Context (c : set_karoubi_cat (op_cat C)).

    Definition opp_set_karoubi_counit_iso_inv
      : set_karoubi_cat (op_cat C) ⟦ c, opp_set_karoubi_ob_lift c ⟧
      := make_set_karoubi_mor _
        (set_karoubi_ob_idempotent _ c)
        (idempotent_is_idempotent _)
        (idempotent_is_idempotent _).

    Lemma opp_set_karoubi_counit_is_inverse
      : is_inverse_in_precat (adjcounit opp_set_karoubi_is_adjoint c) opp_set_karoubi_counit_iso_inv.
    Proof.
      split;
        apply set_karoubi_mor_eq;
        apply (idempotent_is_idempotent (set_karoubi_ob_idempotent _ c)).
    Qed.

    Definition opp_set_karoubi_counit_is_iso
      : is_z_isomorphism (adjcounit opp_set_karoubi_is_adjoint c)
      := make_is_z_isomorphism _ _ opp_set_karoubi_counit_is_inverse.

  End OppKaroubiCounitIso.

  Definition opp_set_karoubi
    : adj_equiv (op_cat (set_karoubi_cat C)) (set_karoubi_cat (op_cat C))
    := opp_set_karoubi_functor ,,
      opp_set_karoubi_is_adjoint ,,
      opp_set_karoubi_unit_is_iso ,,
      opp_set_karoubi_counit_is_iso.

End OppKaroubiEquiv.

(** * 5. The Karoubi envelope construction gives a monad on the category of setcategories *)

Definition set_set_karoubi
  (C : setcategory)
  : setcategory.
Proof.
  use make_setcategory.
  - exact (set_karoubi (C : setcategory)).
  - apply isaset_set_karoubi.
Defined.

Definition setcategory_set_karoubi_functor_mor_data
  {C D : setcategory}
  (F : C ⟶ D)
  : functor_data (set_set_karoubi C) (set_set_karoubi D).
Proof.
 use make_functor_data.
  - refine (λ (c : set_karoubi_ob C), _).
    refine (make_set_karoubi_ob _ (F c) _ _).
    apply (functor_preserves_is_idempotent _ (set_karoubi_ob_idempotent _ c)).
  - refine (λ c d (f : set_karoubi_mor _ c d), _).
    use make_set_karoubi_mor.
    + exact (#F f).
    + abstract (
        refine (!functor_comp F _ _ @ _);
        apply maponpaths;
        apply set_karoubi_mor_commutes_left
      ).
    + abstract (
        refine (!functor_comp F _ _ @ _);
        apply maponpaths;
        apply set_karoubi_mor_commutes_right
      ).
Defined.

Lemma setcategory_set_karoubi_functor_mor_is_functor
  {C D : setcategory}
  (F : C ⟶ D)
  : is_functor (setcategory_set_karoubi_functor_mor_data F).
Proof.
  apply make_is_functor.
  - intro c.
    now apply set_karoubi_mor_eq.
  - intros c d e f g.
    apply set_karoubi_mor_eq.
    apply functor_comp.
Qed.

Definition setcategory_set_karoubi_functor_mor
  {C D : setcategory}
  (F : C ⟶ D)
  : set_set_karoubi C ⟶ set_set_karoubi D
  := make_functor
    (setcategory_set_karoubi_functor_mor_data F)
    (setcategory_set_karoubi_functor_mor_is_functor F).

Definition setcategory_set_karoubi_functor_data
  : functor_data cat_of_setcategory cat_of_setcategory
  := make_functor_data (C := cat_of_setcategory) (C' := cat_of_setcategory)
    set_set_karoubi
    (λ C D F, setcategory_set_karoubi_functor_mor F).

Definition set_karoubi_functor_eq
  {C D : category}
  (F G : C ⟶ set_karoubi_cat D)
  (H1 : ∏ c, set_karoubi_ob_object _ (F c) = set_karoubi_ob_object _ (G c))
  (H2 : ∏ c, transportf (λ x, D⟦x, x⟧) (H1 c) (idempotent_morphism (set_karoubi_ob_idempotent _ (F c))) = idempotent_morphism (set_karoubi_ob_idempotent _ (G c)))
  (H3 : ∏ c d f, double_transport (H1 c) (H1 d) (set_karoubi_mor_morphism _ (#F f)) = set_karoubi_mor_morphism _ (#G f))
  : F = G.
Proof.
  apply (functor_eq _ _ (homset_property _)).
  use functor_data_eq.
  - intro c.
    use total2_paths_f.
    + exact (H1 c).
    + use subtypePath.
      {
        intro.
        use homset_property.
      }
      refine (pr1_transportf (B := λ x, D⟦x, x⟧) _ _ @ _).
      abstract (exact (H2 c)).
  - intros c d f.
    apply set_karoubi_mor_eq.
    refine (_ @ H3 _ _ _).
    refine (pr1_transportf (B := λ (x : set_karoubi_ob D), D⟦(G c : set_karoubi_ob D), x⟧) (total2_paths_f _ _) _ @ _).
    refine (functtransportf (set_karoubi_ob_object D) _ _ _ @ _).
    refine (maponpaths (λ x, transportf (λ x, D⟦_, x⟧) x _) (base_total2_paths _) @ _).
    apply (maponpaths (transportf _ _)).
    refine (pr1_transportf (B := λ (x : set_karoubi_ob D), D⟦x, (F d : set_karoubi_ob D)⟧) (total2_paths_f _ _) (# F f) @ _).
    refine (functtransportf (set_karoubi_ob_object D) (λ x, D⟦x, (F d : set_karoubi_ob D)⟧) (total2_paths_f _ _) (pr1 (#F f)) @ _).
    apply (maponpaths (λ x, transportf (λ y, D⟦y, _⟧) x _)).
    exact (base_total2_paths _).
Qed.

Lemma setcategory_set_karoubi_is_functor
  : is_functor setcategory_set_karoubi_functor_data.
Proof.
  apply make_is_functor.
  - refine (λ (C : setcategory), _).
    now use set_karoubi_functor_eq.
  - refine (λ (C D E : setcategory) (f : C ⟶ D) (g : D ⟶ E), _).
    now use set_karoubi_functor_eq.
Qed.

Definition setcategory_set_karoubi_functor
  : cat_of_setcategory ⟶ cat_of_setcategory
  := make_functor
    setcategory_set_karoubi_functor_data
    setcategory_set_karoubi_is_functor.

Definition setcategory_set_karoubi_monad_multiplication_data_data
  (C : setcategory)
  : functor_data (setcategory_set_karoubi_functor (setcategory_set_karoubi_functor C) : setcategory)
  (setcategory_set_karoubi_functor C : setcategory).
Proof.
  use make_functor_data.
  - intro c.
    use make_set_karoubi_ob.
    + exact (set_karoubi_ob_object _ (set_karoubi_ob_object _ c)).
    + exact (set_karoubi_mor_morphism _ (idempotent_morphism (set_karoubi_ob_idempotent _ c))).
    + exact (maponpaths (set_karoubi_mor_morphism _) (idempotent_is_idempotent (set_karoubi_ob_idempotent _ c))).
  - intros a b f.
    use make_set_karoubi_mor.
    + exact (set_karoubi_mor_morphism _ (set_karoubi_mor_morphism _ f)).
    + exact (maponpaths (set_karoubi_mor_morphism _) (set_karoubi_mor_commutes_left _ f)).
    + exact (maponpaths (set_karoubi_mor_morphism _) (set_karoubi_mor_commutes_right _ f)).
Defined.

Lemma setcategory_set_karoubi_monad_multiplication_data_is_functor
  (C : setcategory)
  : is_functor (setcategory_set_karoubi_monad_multiplication_data_data C).
Proof.
  apply make_is_functor;
  repeat intro;
  now apply set_karoubi_mor_eq.
Qed.

Definition setcategory_set_karoubi_monad_multiplication_data
  : nat_trans_data (setcategory_set_karoubi_functor ∙ setcategory_set_karoubi_functor) setcategory_set_karoubi_functor
  := λ C, make_functor
    (setcategory_set_karoubi_monad_multiplication_data_data C)
    (setcategory_set_karoubi_monad_multiplication_data_is_functor C).

Lemma setcategory_set_karoubi_monad_multiplication_is_nat_trans
  : is_nat_trans _ _ setcategory_set_karoubi_monad_multiplication_data.
Proof.
  intros C D F.
  now use set_karoubi_functor_eq.
Qed.

Definition setcategory_set_karoubi_monad_multiplication
  : setcategory_set_karoubi_functor ∙ setcategory_set_karoubi_functor ⟹ setcategory_set_karoubi_functor
  := make_nat_trans _ _
    setcategory_set_karoubi_monad_multiplication_data
    setcategory_set_karoubi_monad_multiplication_is_nat_trans.

Definition setcategory_set_karoubi_monad_unit
  : functor_identity cat_of_setcategory ⟹ setcategory_set_karoubi_functor.
Proof.
  use make_nat_trans.
  - exact (λ (C : setcategory), set_karoubi_inclusion C).
  - abstract (
      intros C D F;
      use set_karoubi_functor_eq;
        intro c;
        try reflexivity;
        exact (!functor_id _ _)
    ).
Defined.

Definition setcategory_set_karoubi_monad_data
  : disp_Monad_data setcategory_set_karoubi_functor
  := setcategory_set_karoubi_monad_multiplication ,,
    setcategory_set_karoubi_monad_unit.

Lemma setcategory_set_karoubi_is_monad
  : disp_Monad_laws setcategory_set_karoubi_monad_data.
Proof.
  repeat split;
    intro C;
    now use set_karoubi_functor_eq.
Qed.

Definition setcategory_set_karoubi_monad
  : Monad cat_of_setcategory
  := setcategory_set_karoubi_functor ,,
    setcategory_set_karoubi_monad_data ,,
    setcategory_set_karoubi_is_monad.
