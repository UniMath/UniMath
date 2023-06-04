Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.Preservation.

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

  (* TO BE MOVED IN THE SAME PLACE AS IDENTITY_functor_is_fully_faithful *)
  Lemma identity_functor_is_essentially_surjective (C : category)
    : essentially_surjective (functor_identity C).
  Proof.
    intro x.
    apply hinhpr.
    exists x.
    apply identity_z_iso.
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

  (* Definition two_out_of_three_CAT
    {∏ }

  Lemma two_out_of_three_weak_equivalence
    : two_out_of_three is_weak_equiv.
  Proof.
    split.
    - apply two_out_of_three_eso.
    - apply two_out_of_three_ff.
  Qed. *)

  Definition weak_equiv
    (C D : category) : UU
    := ∑ H : C ⟶ D, is_weak_equiv H.

End WeakEquivalences.

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

  (* This definition is the one provided by Niels in his PR on subbicats. *)
  Definition preserves_chosen_terminal_eq
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (T₁ : Terminal C₁)
           (T₂ : Terminal C₂)
  : UU
    := ∥ F T₁ = T₂ ∥.

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
