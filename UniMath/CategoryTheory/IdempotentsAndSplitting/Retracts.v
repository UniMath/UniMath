(**************************************************************************************************

  Retracts and (split) idempotents

  Defines the types of retractions, idempotents and split idempotents in a category and shows that
  these are preserved by functors.

  Contents
  1. Retractions [retraction]
  2. Sections
  3. Idempotents and split idempotents [idempotent] [split_idempotent]
  3.1. Split idempotent implies idempotent [split_idempotent_is_idempotent]
  3.2. In a univalent category, being split idempotent is a mere proposition
    [isaprop_is_split_idempotent]
  4. Functors
  4.1. Retractions are preserved by functors [functor_preserves_retraction]
  4.2. Idempotents are preserved by functors [functor_preserves_idempotent]
  4.3. Split idempotents are preserved by functors [functor_preserves_split_idempotent]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Local Open Scope cat.

(** * 1. Retractions *)
Section SectionsAndRetractions.
  Context {C : precategory}.

  Definition is_retraction
    {A B : C}
    (s : A --> B)
    (r : B --> A)
    : UU
    := s · r = identity A.

  Lemma isaprop_is_retraction
    {A B : C}
    (s : A --> B)
    (r : B --> A)
    (H : has_homsets C)
    : isaprop (is_retraction s r).
  Proof.
    apply H.
  Qed.

  (** A retraction of B onto A *)
  Definition retraction
    (A B : C)
    : UU
    := ∑ (s : A --> B)
        (r : B --> A),
        is_retraction s r.

  Definition make_retraction
    {A B : C}
    (s : A --> B)
    (r : B --> A)
    (H : is_retraction s r)
    : retraction A B
    := s ,, r ,, H.

  Section Accessors.

    Context {A B : C}.
    Context (H : retraction A B).

    Definition retraction_section
      : A --> B
      := pr1 H.

    Definition retraction_retraction
      : B --> A
      := pr12 H.

    Definition retraction_is_retraction
      : retraction_section · retraction_retraction = identity A
      := pr22 H.

  End Accessors.

  Coercion retraction_retraction
    : retraction >-> precategory_morphisms.

  Lemma isaset_retraction
    (A B : ob C)
    (H : has_homsets C)
    : isaset (retraction A B).
  Proof.
    do 2 (apply isaset_total2; [apply H | intro]).
    apply isasetaprop.
    apply isaprop_is_retraction.
    apply H.
  Qed.

  Definition compose_retraction
    {X Y Z : C}
    (f : retraction X Y)
    (g : retraction Y Z)
    : retraction X Z.
  Proof.
    use make_retraction.
    - exact (retraction_section f · retraction_section g).
    - exact (g · f).
    - abstract (
        refine (assoc _ _ _ @ _);
        refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _);
        refine (maponpaths (λ x, _ · x · _) (retraction_is_retraction _) @ _);
        refine (maponpaths (λ x, x · _) (id_right _) @ _);
        apply retraction_is_retraction
      ).
  Defined.

  (** * 2. Sections *)
  Definition section_of_mor
             {x y : C}
             (r : x --> y)
    : UU
    := ∑ (s : y --> x),
       is_retraction s r.

  Definition make_section_of_mor
             {x y : C}
             (r : x --> y)
             (s : y --> x)
             (sr : is_retraction s r)
    : section_of_mor r.
  Proof.
    simple refine (_ ,, _).
    - exact s.
    - exact sr.
  Defined.

  Coercion section_of_mor_to_mor
           {x y : C}
           {r : x --> y}
           (s : section_of_mor r)
    : y --> x
    := pr1 s.

  Proposition section_of_mor_eq
              {x y : C}
              {r : x --> y}
              (s : section_of_mor r)
    : s · r = identity _.
  Proof.
    exact (pr2 s).
  Defined.
End SectionsAndRetractions.

Proposition eq_section_of_mor
            {C : category}
            {x y : C}
            {r : x --> y}
            {s₁ s₂ : section_of_mor r}
            (p : (s₁ : y --> x) = s₂)
  : s₁ = s₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_is_retraction.
    apply homset_property.
  }
  exact p.
Qed.

Definition functor_on_section
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {x y : C₁}
           {r : x --> y}
           (s : section_of_mor r)
  : section_of_mor (#F r).
Proof.
  use make_section_of_mor.
  - exact (#F s).
  - abstract
      (unfold is_retraction ;
       rewrite <- functor_comp ;
       rewrite section_of_mor_eq ;
       apply functor_id).
Defined.

(** * 3. Idempotents and split idempotents *)
Section Idempotents.

  Context {C : precategory}.

  Definition is_idempotent
    {c : C}
    (e : c --> c)
    : UU
    := e · e = e.

  Definition idempotent
    (c : C)
    : UU
    := ∑ (e : c --> c), is_idempotent e.

  Coercion idempotent_morphism
    {c : C}
    (e : idempotent c)
    : c --> c
    := pr1 e.

  Definition idempotent_is_idempotent
    {c : C}
    (e : idempotent c)
    : is_idempotent e
    := pr2 e.

  Definition is_split_idempotent
    {c : C}
    (e : c --> c)
    : UU
    := ∑ c' (H : retraction c' c), e = retraction_retraction H · retraction_section H.

  Definition make_is_split_idempotent
    {c : C}
    {e : c --> c}
    (c' : C)
    (H1 : retraction c' c)
    (H2 : e = retraction_retraction H1 · retraction_section H1)
    : is_split_idempotent e
    := c' ,, H1 ,, H2.

  Definition split_idempotent
    (c : C)
    : UU
    := ∑ (e : c --> c), is_split_idempotent e.

  Coercion split_idempotent_morphism
    {c : C}
    (e : split_idempotent c)
    : c --> c
    := pr1 e.

  Definition split_idempotent_is_split_idempotent
    {c : C}
    (e : split_idempotent c)
    : is_split_idempotent e
    := pr2 e.

  Definition split_idempotent_object
    {c : C}
    (e : split_idempotent c)
    : C
    := pr12 e.

  Definition split_idempotent_retraction
    {c : C}
    (e : split_idempotent c)
    : retraction (split_idempotent_object e) c
    := pr122 e.

  Definition split_idempotent_is_split
    {c : C}
    (e : split_idempotent c)
    : split_idempotent_morphism e = split_idempotent_retraction e · retraction_section (split_idempotent_retraction e)
    := pr222 e.

(** ** 3.1. Split idempotent implies idempotent *)
  Lemma split_idempotent_is_idempotent
    {c : C}
    (e : split_idempotent c)
    : is_idempotent e.
  Proof.
    induction (!split_idempotent_is_split e).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ x, x · _) _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths _ (retraction_is_retraction _) @ _).
    apply id_right.
  Qed.

End Idempotents.

Definition idempotents_split
  (C : category)
  : UU
  := ∏ (x : C) (f : idempotent x), ∥ is_split_idempotent f ∥.

(** ** 3.2. In a univalent category, being split idempotent is a mere proposition *)

Definition is_split_idempotent_eq
  {C : category}
  {X : C}
  {f : C⟦X, X⟧}
  (g g' : is_split_idempotent f)
  (H1 : pr1 g = pr1 g')
  (H2 : transportf (λ Y, C⟦Y, X⟧) H1 (pr112 g) = pr112 g')
  (H3 : transportf (λ Y, C⟦X, Y⟧) H1 (pr1 (pr212 g)) = pr1 (pr212 g'))
  : g = g'.
Proof.
  repeat use total2_paths_f.
  - exact H1.
  - refine (_ @ H2).
    clear H2 H3.
    now induction H1.
  - refine (_ @ H3).
    refine (pr1_transportf (B := λ _, C⟦X, _⟧) _ _ @ _).
    refine (eqtohomot (transportf_const _ _) _ @ _).
    clear H3 H2.
    now induction H1.
  - apply homset_property.
  - apply homset_property.
Qed.

Lemma isaprop_is_split_idempotent
  {C : category}
  {x : C}
  (f : C⟦x, x⟧)
  (C_is_univ : is_univalent C)
  : isaprop (is_split_idempotent f).
Proof.
  apply invproofirrelevance.
  intros X X'.
  induction X as [X HX], HX as [r HX].
  induction X' as [X' HX'], HX' as [r' HX'].
  use is_split_idempotent_eq.
  - apply (isotoid _ C_is_univ).
    use make_z_iso.
    + exact (retraction_section r · r').
    + exact (retraction_section r' · r).
    + abstract (
        use make_is_inverse_in_precat;
        refine (assoc _ _ _ @ _);
        refine (maponpaths (λ x, x · _) (assoc' _ _ _) @ _);
        [ refine (maponpaths (λ x, _ · x · _) (!HX' @ HX) @ _)
        | refine (maponpaths (λ x, _ · x · _) (!HX @ HX') @ _) ];
        refine (maponpaths (λ x, x · _) (assoc _ _ _) @ _);
        refine (assoc' _ _ _ @ _);
        refine (maponpaths _ (retraction_is_retraction _) @ _);
        refine (id_right _ @ _);
        apply retraction_is_retraction
      ).
  - refine (transportf_isotoid _ _ _ _ _ _ _ @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (λ x, _ · x) (!HX @ HX') @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ x, x · _) (retraction_is_retraction _) @ _).
    apply id_left.
  - refine (transportf_isotoid' _ _ _ _ _ _ _ @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ x, x · _) (!HX @ HX') @ _).
    refine (assoc' _ _ _ @ _).
    refine (maponpaths _ (retraction_is_retraction _) @ _).
    apply id_right.
Qed.

(** * 4. Functors *)
Section Functors.

  Context {C D : category}.
  Context (F : C ⟶ D).
  Context (H : fully_faithful F).

(** ** 4.1. Retractions are preserved by functors *)
  Lemma functor_preserves_is_retraction
    {a b : C}
    (f : retraction b a)
    : is_retraction (#F (retraction_section f)) (#F f).
  Proof.
    refine (!functor_comp _ _ _ @ _).
    refine (maponpaths _ (retraction_is_retraction f) @ _).
    apply functor_id.
  Qed.

  Definition functor_preserves_retraction
    {a b : C}
    (H : retraction b a)
    : retraction (F b) (F a)
    := _ ,, _ ,, functor_preserves_is_retraction H.

  Lemma fully_faithful_functor_reflects_is_retraction
    {a b : C}
    (f : retraction (F b) (F a))
    : is_retraction (fully_faithful_inv_hom H _ _ (retraction_section f)) (fully_faithful_inv_hom H _ _ f).
  Proof.
    refine (!fully_faithful_inv_comp _ _ _ _ _ _ _ _ _ @ _).
    refine (maponpaths _ (retraction_is_retraction _) @ _).
    apply fully_faithful_inv_identity.
  Qed.

  Definition fully_faithful_functor_reflects_retraction
    {a b : C}
    (f : retraction (F b) (F a))
    : retraction b a
    := _ ,, _ ,, fully_faithful_functor_reflects_is_retraction f.

(** ** 4.2. Idempotents are preserved by functors *)
  Lemma functor_preserves_is_idempotent
    {c : C}
    (f : idempotent c)
    : is_idempotent (#F f).
  Proof.
    refine (!functor_comp _ _ _ @ _).
    apply maponpaths.
    apply idempotent_is_idempotent.
  Qed.

  Definition functor_preserves_idempotent
    {c : C}
    (H : idempotent c)
    : idempotent (F c)
    := _ ,, functor_preserves_is_idempotent H.

  Lemma fully_faithful_functor_reflects_is_idempotent
    {c : C}
    (f : idempotent (F c))
    : is_idempotent (fully_faithful_inv_hom H _ _ f).
  Proof.
    refine (!fully_faithful_inv_comp _ _ _ _ _ _ _ _ _ @ _).
    apply maponpaths.
    apply idempotent_is_idempotent.
  Qed.

  Definition fully_faithful_functor_reflects_idempotent
    {c : C}
    (f : idempotent (F c))
    : idempotent c
    := _ ,, fully_faithful_functor_reflects_is_idempotent f.

(** ** 4.3. Split idempotents are preserved by functors *)
  Lemma functor_preserves_is_split_idempotent
    {c : C}
    (f : split_idempotent c)
    : is_split_idempotent (#F f).
  Proof.
    exists (F (split_idempotent_object f)).
    exists (functor_preserves_retraction (split_idempotent_retraction f)).
    refine (_ @ functor_comp _ _ _).
    apply maponpaths.
    apply split_idempotent_is_split.
  Qed.

  Definition functor_preserves_split_idempotent
    {c : C}
    (f : split_idempotent c)
    : split_idempotent (F c)
    := _ ,, (functor_preserves_is_split_idempotent f).

End Functors.

Section Opp.

  Context (C : category).
  Context (A B : C).
  Context (r : retraction A B).

  Definition opp_retraction
    : retraction (A : C^opp) (B : C^opp)
    := retraction_retraction r ,, retraction_section r ,, retraction_is_retraction r.

End Opp.
