Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.Preservation.

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

Section WeakEquivalencePreservations.

  Definition weak_equiv_preserves_chosen_terminal
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → ∏ t : Terminal C, preserves_chosen_terminal t F.
  Proof.
    intros Fw [x x_is_t] y'.
    use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw y')).
    intros [y yi].
    apply (iscontrweqb' (x_is_t y)).
    refine (invweq (_ ,, ff_from_weak_equiv _ Fw y x) ∘ _)%weq.
    apply z_iso_comp_right_weq.
    exact yi.
  Qed.

  Definition weak_equiv_preserves_terminal
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F → preserves_terminal F.
  Proof.
    intros Fw ? x_is_t.
    apply (preserves_terminal_if_preserves_chosen (_,,x_is_t)).
    - apply weak_equiv_preserves_chosen_terminal.
      exact Fw.
    - exact x_is_t.
  Qed.

  Definition weak_equiv_preserves_chosen_terminal_eq
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → is_univalent D
      → ∏ t1 t2, preserves_chosen_terminal_eq F t1 t2.
  Proof.
    intros Fw Duniv t1 t2.
    apply hinhpr.
    apply Duniv.
    set (Ft1_t := weak_equiv_preserves_terminal _ Fw _ (pr2 t1)).
    exact (z_iso_Terminals (_ ,, Ft1_t) t2).
  Qed.

End WeakEquivalencePreservations.

Section WeakEquivalenceReflections.

  Lemma weak_equiv_reflects_terminal
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → ∏ c : C, isTerminal _ (F c) → isTerminal _ c.
  Proof.
    intros Fw c Fc_term c'.
    apply (iscontrweqb' (Fc_term (F c'))).
    apply ((_ ,, ff_from_weak_equiv _ Fw _ _))%weq.
  Qed.

End WeakEquivalenceReflections.
