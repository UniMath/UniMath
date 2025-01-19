(**************************************************************************************************

  Uniqueness of the Rezk completion

  In RezkCompletion it is shown that the weak equivalence F of a Rezk completion D of A is an
  initial functor from A: any functor from A to a univalent category factors uniquely through F.
  Now, given two initial functors F : A ⟶ D and F' : A ⟶ D', they factor uniquely through each
  other, which gives functors G and G' between D and D' that compose to the identity on both sides.
  In other words: we have an equivalence of categories. We can turn this into an adjoint
  equivalence, and since D and D' are univalent we know that D = D'.
  In fact, since F ∙ G = F', we get an equality of initial functors (D, F) = (D', F').
  Now, if we apply this to the initial functors obtained from Rezk completions, we see that two Rezk
  completions are equal as well.

  Note: In this file we prove equality of functors and categories. These particular proofs use a lot
  of rewriting and induction on paths, which makes them unpleasant to compute with. Therefore, they
  have been made opaque, even though their types are not a proposition.

  Contents
  1. An equality lemma for the type `functor_from A` [functor_from_eq]
  2. Two initial functors from a type are equal [initial_functor_unique]
  3. Two Rezk completions are equal [rezk_completion_unique]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.RezkCompletions.RezkCompletions.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Local Open Scope cat.

(** * 1. An equality lemma for the type `functor_from A` *)

Definition functor_from_eq
  {A : category}
  (F F' : functor_from A)
  (H1 : adjoint_equivalence (B := bicat_of_univ_cats) (target_category F) (target_category F'))
  (H2 : F ∙ (H1 : bicat_of_univ_cats⟦_, _⟧) = F')
  : F = F'.
Proof.
  induction F as [D F].
  induction F' as [D' F'].
  cbn in H1.
  rewrite <- (idtoiso_2_0_isotoid_2_0 univalent_cat_is_univalent_2_0 H1) in H2.
  induction (isotoid_2_0 univalent_cat_is_univalent_2_0 H1).
  apply maponpaths.
  refine (_ @ H2).
  exact (!functor_identity_right _ _ _).
Qed.

(** * 2. Two initial functors from a type are equal *)

Section InitialFunctorUnique.

  Context {A : category}.
  Context (F F' : initial_functor_from A).

  Let D : univalent_category := target_category F.
  Let D' : univalent_category := target_category F'.

  Let G := initial_functor_arrow F F' : D ⟶ D'.
  Let G' := initial_functor_arrow F' F : D' ⟶ D.

  Local Lemma G'_after_G : functor_identity D = G ∙ G'.
  Proof.
    refine (!initial_functor_endo_is_identity F _ _).
    refine (!functor_assoc _ _ _ _ _ _ _ @ _).
    refine (maponpaths (λ x, x ∙ _) (initial_functor_arrow_commutes _ _) @ _).
    apply initial_functor_arrow_commutes.
  Qed.

  Local Lemma G_after_G' : G' ∙ G = functor_identity D'.
  Proof.
    refine (initial_functor_endo_is_identity F' _ _).
    refine (!functor_assoc _ _ _ _ _ _ _ @ _).
    refine (maponpaths (λ x, x ∙ _) (initial_functor_arrow_commutes _ _) @ _).
    apply initial_functor_arrow_commutes.
  Qed.

  Let η := idtoiso (C := [_, _]) G'_after_G : z_iso (C := [_, _]) (functor_identity D) (G ∙ G').
  Let ɛ := idtoiso (C := [_, _]) G_after_G' : z_iso (C := [_, _]) (G' ∙ G) (functor_identity D').

  Definition initial_functor_category_equivalence
    : adjoint_equivalence (B := bicat_of_univ_cats) D D'.
  Proof.
    exists G.
    apply (invmap (adj_equiv_is_equiv_cat _)).
    use (adjointification (make_equivalence_of_cats (make_adjunction_data G _ _ _) (make_forms_equivalence _ _ _))).
    + exact G'.
    + exact (z_iso_mor η).
    + exact (z_iso_mor ɛ).
    + intro.
      apply (is_functor_z_iso_pointwise_if_z_iso _ _ (homset_property _)).
      apply z_iso_is_z_isomorphism.
    + intro.
      apply (is_functor_z_iso_pointwise_if_z_iso _ _ (homset_property _)).
      apply z_iso_is_z_isomorphism.
  Defined.

  Definition initial_functor_unique
    : F = F'.
  Proof.
    apply subtypePath.
    {
      intro.
      apply isaprop_is_initial_functor_from.
    }
    use functor_from_eq.
    - exact initial_functor_category_equivalence.
    - apply initial_functor_arrow_commutes.
  Qed.

End InitialFunctorUnique.

(** * 3. Two Rezk completions are equal *)

Definition rezk_completion_unique
  {A : category}
  (D D' : rezk_completion A)
  : D = D'.
Proof.
  refine (invmaponpathsweq (weqtotal2asstol _ (λ F, is_weak_equiv (pr2 F))) _ _ _).
  apply subtypePath.
  {
    intro.
    apply isaprop_is_weak_equiv.
  }
  pose (F := (_ ,, rezk_completion_initial_functor_from _ D) : initial_functor_from A).
  pose (F' := (_ ,, rezk_completion_initial_functor_from _ D') : initial_functor_from A).
  apply (base_paths F F').
  apply initial_functor_unique.
Qed.
