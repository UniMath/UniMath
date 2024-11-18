(**

Section ``WeakEquivalences'' contains:
   1. the definition of a weak equivalence (i.e., essentially surjective and fully faithful);
   2. together with accessors;
   3. a proof that ``is a weak equivalence'' is a proposition;
   4. a proof that every identity functor (resp. the composite of weak equivalences) is a weak equivalence

Section ``WeakEquivalenceInducesIsoOnUnivalentFunctorCategories'' contains a proof for the statement:
Let H : C → D be a weak equivalence (between not-necesssarily univalent categories) and E a univalent category.
Then, the functor (H · -) : [D, E] → [C, E] is an isomorphism of (univalent) categories; and hence an isomorphism.

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Local Open Scope cat.

Section WeakEquivalences.

  Definition is_weak_equiv
    {C D : category} (H : functor C D) : UU
    := essentially_surjective H × fully_faithful H.

  Definition eso_from_weak_equiv
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F → essentially_surjective F
    := pr1.

  Definition ff_from_weak_equiv
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F → fully_faithful F
    := pr2.

  Lemma isaprop_is_weak_equiv
    {C D : category} (H : functor C D)
    : isaprop (is_weak_equiv H).
  Proof.
    apply isapropdirprod.
    - apply isaprop_essentially_surjective.
    - apply isaprop_fully_faithful.
  Qed.

  Lemma id_is_weak_equiv
    (C : category)
    : is_weak_equiv (functor_identity C).
  Proof.
    split.
    - apply identity_functor_is_essentially_surjective.
    - apply identity_functor_is_fully_faithful.
  Qed.

  Definition comp_is_weak_equiv
    {C D E : category}
    (H : C ⟶ D) (I : D ⟶ E)
    : is_weak_equiv H → is_weak_equiv I
      → is_weak_equiv (H ∙ I).
  Proof.
    intros Hw Iw.
    split.
    - exact (comp_essentially_surjective
        _ (eso_from_weak_equiv _ Hw)
        _ (eso_from_weak_equiv _ Iw)).
    - exact (comp_ff_is_ff _ _ _
               _ (ff_from_weak_equiv _ Hw)
               _ (ff_from_weak_equiv _ Iw)).
  Qed.

  Definition weak_equiv
    (C D : category) : UU
    := ∑ H : C ⟶ D, is_weak_equiv H.

End WeakEquivalences.

Section WeakEquivalenceInducesIsoOnUnivalentFunctorCategories.

  Context {C D : category}
    (H : C ⟶ D)
    (Hw : is_weak_equiv H).

  Definition precomp_is_iso
    : ∏ E : univalent_category, is_catiso (pre_composition_functor _ _ E H).
  Proof.
    intro E.
    transparent assert (a : (Core.adj_equivalence_of_cats (pre_composition_functor _ _ (pr1 E) H))). {
      apply precomp_adjoint_equivalence ; apply Hw.
    }

    use (pr2 (adj_equivalence_of_cats_to_cat_iso a _ _))
    ; apply is_univalent_functor_category ; apply E.
  Defined.

  Definition precomp_is_equality
    : ∏ E : univalent_category,  [D, E] = [C, E].
  Proof.
    intro E.
    apply catiso_to_category_path.
    exact (_ ,, precomp_is_iso E).
  Defined.

End WeakEquivalenceInducesIsoOnUnivalentFunctorCategories.
