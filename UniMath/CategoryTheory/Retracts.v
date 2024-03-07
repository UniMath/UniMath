(**************************************************************************************************

  Retracts and (split) idempotents

  Defines the types of retractions, idempotents and split idempotents in a category and shows that
  these are preserved by functors.

  Contents
  1. Retractions [retraction]
  2. Idempotents and split idempotents [idempotent] [split_idempotent]
  2.2. Split idempotent implies idempotent [split_idempotent_is_idempotent]
  3. Functors
  3.1. Retractions are preserved by functors [functor_preserves_retraction]
  3.2. Idempotents are preserved by functors [functor_preserves_idempotent]
  3.3. Split idempotents are preserved by functors [functor_preserves_split_idempotent]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

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

End SectionsAndRetractions.

(** * 2. Idempotents and split idempotents *)
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

  #[reversible=no] Coercion idempotent_morphism
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

  Definition split_idempotent
    (c : C)
    : UU
    := ∑ (e : c --> c), is_split_idempotent e.

  #[reversible=no] Coercion split_idempotent_morphism
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

(** ** 2.2. Split idempotent implies idempotent *)
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

(** * 3. Functors *)
Section Functors.

  Context {C D : category}.
  Context (F : C ⟶ D).

(** ** 3.1. Retractions are preserved by functors *)
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

(** ** 3.2. Idempotents are preserved by functors *)
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

(** ** 3.3. Split idempotents are preserved by functors *)
  Lemma functor_preserves_is_split_idempotent
    {c : C}
    (f : split_idempotent c)
    : is_split_idempotent (#F f).
  Proof.
    unfold is_split_idempotent.
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
