(**************************************************************************************************

  Rezk Completions

  Given a category A, a univalent category D, together with a weak equivalence F : A ⟶ D is called a
  Rezk completion.
  Since F is a weak equivalence, precomposition with it gives an adjoint equivalence between the
  functor categories [A, C] and [D, C], and also between [A^op, C] and [D^op, C], for any univalent
  category C.
  From this, we can deduce that F is the "initial functor from A".
  This file defines Rezk completions and initial functors from a category, together with their
  accessors, and then shows the results mentioned above.

  Contents
  1. The definition and accessors of a Rezk completion [rezk_completion] [RezkCat]
  1.1. The Rezk completion of a univalent category is equivalent to the original category
    [rezk_completion_of_univalent]
  2. The definition an initial functor from a category [functor_from] [initial_functor_from]
  2.1. The proof that for an initial functor F, any functor G is the identity if F ∙ G = F
    [initial_functor_endo_is_identity]
  3. The equivalence between the covariant functor categories
    [rezk_completion_functor_equivalence] [rezk_completion_universal_property]
  3.1. The proof that F is the initial functor from A
    [rezk_completion_initial_functor_from]
  4. The equivalence between the contravariant functor categories
    [rezk_completion_opp_functor_equivalence] [rezk_completion_opp_universal_property]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecompEquivalence.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** * 1. The definition and accessors of a Rezk completion *)

Definition rezk_completion
  (A : category)
  : UU
  := ∑ (D : univalent_category), weak_equiv A D.

Definition RezkCat : UU
  := ∏ C : category, rezk_completion C.


Definition make_rezk_completion
  {A : category}
  (D : univalent_category)
  (F : A ⟶ D)
  (HE : essentially_surjective F)
  (HF : fully_faithful F)
  : rezk_completion A
  := D ,, F ,, HE ,, HF.

Coercion rezk_completion_to_category
  {A : category}
  (D : rezk_completion A)
  : univalent_category
  := pr1 D.

Definition rezk_completion_weak_equivalence
  {A : category}
  (D : rezk_completion A)
  : weak_equiv A D
  := pr2 D.

Definition rezk_completion_functor
  {A : category}
  (D : rezk_completion A)
  : A ⟶ D
  := pr1 (rezk_completion_weak_equivalence D).

Definition rezk_completion_is_weak_equivalence
  {A : category}
  (D : rezk_completion A)
  : is_weak_equiv (rezk_completion_functor D)
  := pr2 (rezk_completion_weak_equivalence D).

Definition rezk_completion_essentially_surjective
  {A : category}
  (D : rezk_completion A)
  : essentially_surjective (rezk_completion_functor D)
  := eso_from_weak_equiv _ (rezk_completion_is_weak_equivalence D).

Definition rezk_completion_fully_faithful
  {A : category}
  (D : rezk_completion A)
  : fully_faithful (rezk_completion_functor D)
  := ff_from_weak_equiv _ (rezk_completion_is_weak_equivalence D).

Definition rezk_completion_of_univalent
  {A : univalent_category}
  (D : rezk_completion A)
  : adj_equivalence_of_cats (rezk_completion_functor D).
Proof.
  apply rad_equivalence_of_cats.
  - apply univalent_category_is_univalent.
  - apply rezk_completion_fully_faithful.
  - apply rezk_completion_essentially_surjective.
Defined.

(** * 2. The definition an initial functor from a category *)

Definition functor_from (C : precategory) : UU
  := ∑ D : univalent_category, functor C D.

Definition make_functor_from
  {C : precategory}
  (D : univalent_category)
  (F : C ⟶ D)
  : functor_from C
  := D ,, F.

#[reversible=no] Coercion func_functor_from
  {C : precategory}
  (X : functor_from C)
  : functor C (pr1 X)
  := pr2 X.

Definition target_category
  {C : precategory}
  (X : functor_from C)
  : univalent_category
  := pr1 X.

Definition is_initial_functor_from
  {C : precategory}
  (F : functor_from C)
  : UU
  := ∏ F' : functor_from C, ∃! (G : target_category F ⟶ target_category F'), F ∙ G = F'.

Definition isaprop_is_initial_functor_from
  {C : precategory}
  (F : functor_from C)
  : isaprop (is_initial_functor_from F).
Proof.
  apply impred_isaprop.
  intro F'.
  apply isapropiscontr.
Qed.

Definition initial_functor_from
  (C : precategory)
  : UU
  := ∑ (F : functor_from C), is_initial_functor_from F.

#[reversible=no] Coercion initial_functor_from_to_functor_from
  {C : precategory}
  (F : initial_functor_from C)
  : functor_from C
  := pr1 F.

Definition initial_functor_from_is_initial
  {C : precategory}
  (F : initial_functor_from C)
  : is_initial_functor_from F
  := pr2 F.

Definition initial_functor_arrow
  {C : precategory}
  (F : initial_functor_from C)
  (F' : functor_from C)
  : target_category F ⟶ target_category F'
  := pr11 (initial_functor_from_is_initial F F').

Definition initial_functor_arrow_commutes
  {C : precategory}
  (F : initial_functor_from C)
  (F' : functor_from C)
  : F ∙ initial_functor_arrow F F' = F'
  := pr21 (initial_functor_from_is_initial F F').

Definition initial_functor_arrow_unique
  {C : precategory}
  (F : initial_functor_from C)
  (F' : functor_from C)
  (G' : target_category F ⟶ target_category F')
  (HG' : F ∙ G' = F')
  : G' = initial_functor_arrow F F'
  := base_paths _ _ (pr2 (initial_functor_from_is_initial F F') (G' ,, HG')).

(** ** 2.1. The proof that for an initial functor F, any functor G is the identity if F ∙ G = F *)

Definition initial_functor_endo_is_identity
    {A : category}
    (F : initial_functor_from A)
    (G : target_category F ⟶ target_category F)
    (H : F ∙ G = F)
  : G = functor_identity (target_category F).
Proof.
  apply (uniqueExists (initial_functor_from_is_initial F F)).
  - exact H.
  - apply functor_identity_right.
Defined.

(** * 3. The equivalence between the covariant functor categories *)

Section UniversalProperty.

  Context (A : category).
  Context (D : rezk_completion A).

  Section FunctorEquivalence.

    Context (C : category).
    Context (HC : is_univalent C).

    Definition rezk_completion_functor_equivalence
      : adj_equivalence_of_cats (pre_composition_functor _ _ C (rezk_completion_functor D)).
    Proof.
      use (precomp_adjoint_equivalence (make_univalent_category _ _)).
      - apply HC.
      - apply rezk_completion_essentially_surjective.
      - apply rezk_completion_fully_faithful.
    Defined.

    Theorem rezk_completion_universal_property :
      isweq (pre_composition_functor _ _ C (rezk_completion_functor D)).
    Proof.
      apply adj_equiv_of_cats_is_weq_of_objects.
      - apply is_univalent_functor_category;
        exact HC.
      - apply is_univalent_functor_category;
        exact HC.
      - apply rezk_completion_functor_equivalence.
    Defined.

  End FunctorEquivalence.

(** ** 3.1. The proof that F is the initial functor from A *)

  Lemma rezk_completion_initial_functor_from
    : is_initial_functor_from (make_functor_from D (rezk_completion_functor D)).
  Proof.
    intro F.
    refine (rezk_completion_universal_property _ _ (F : _ ⟶ _)).
    apply univalent_category_is_univalent.
  Defined.

(** * 4. The equivalence between the contravariant functor categories *)

  Section OppFunctorEquivalence.

    Context (C : category).
    Context (HC : is_univalent C).

    Definition rezk_completion_opp_functor_equivalence :
      adj_equivalence_of_cats
        (pre_composition_functor A^op D^op C
            (functor_opp (rezk_completion_functor D))).
    Proof.
      use (precomp_adjoint_equivalence (make_univalent_category _ _)).
      - apply HC.
      - apply opp_functor_essentially_surjective.
        apply rezk_completion_essentially_surjective.
      - apply opp_functor_fully_faithful.
        apply rezk_completion_fully_faithful.
    Defined.

    Theorem rezk_completion_opp_universal_property :
      isweq (pre_composition_functor A^op D^op C
            (functor_opp (rezk_completion_functor D))).
    Proof.
      apply adj_equiv_of_cats_is_weq_of_objects.
      - apply is_univalent_functor_category;
        exact HC.
      - apply is_univalent_functor_category;
        exact HC.
      - apply rezk_completion_opp_functor_equivalence.
    Defined.

  End OppFunctorEquivalence.

End UniversalProperty.
