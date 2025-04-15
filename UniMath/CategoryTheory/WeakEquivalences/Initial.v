(**
In this file, we show that weak equivalences reflect and preserve initial objects.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Proposition weak_equiv_reflects_initial
  {C D : category} (F : C ⟶ D)
  : is_weak_equiv F
    → ∏ c : C, isInitial _ (F c) → isInitial _ c.
Proof.
  intros Fw c Fc_ini c'.
  apply (iscontrweqb' (Fc_ini (F c'))).
  apply ((_ ,, ff_from_weak_equiv _ Fw _ _))%weq.
Qed.

Section WeakEquivalencePreservationsInitial.

  Proposition weak_equiv_preserves_chosen_initial
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → ∏ I : Initial C, preserves_chosen_initial I F.
  Proof.
    intros Fw [x x_is_i] y'.
    use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw y')).
    intros [y yi].
    apply (iscontrweqb' (x_is_i y)).
    refine (invweq (_ ,, ff_from_weak_equiv _ Fw x y) ∘ _)%weq.
    apply z_iso_comp_left_weq.
    exact (z_iso_inv yi).
  Qed.

  Corollary weak_equiv_preserves_initial
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F → preserves_initial F.
  Proof.
    intros Fw ? x_is_i.
    apply (preserves_initial_if_preserves_chosen (_,,x_is_i)).
    - apply weak_equiv_preserves_chosen_initial.
      exact Fw.
    - exact x_is_i.
  Qed.

  Corollary weak_equiv_creates_initial
    {C D : category} {F : C ⟶ D} (F_weq : is_weak_equiv F) (T : Initial C)
    : Initial D.
  Proof.
    exact (make_Initial _ (weak_equiv_preserves_initial _ F_weq _ (pr2 T))).
  Defined.

  Corollary weak_equiv_preserves_chosen_initial_eq
    {C D : category} (F : C ⟶ D)
    : is_weak_equiv F
      → is_univalent D
      → ∏ I1 I2, preserves_chosen_initial_eq F I1 I2.
  Proof.
    intros Fw Duniv I1 I2.
    apply hinhpr.
    apply Duniv.
    set (FI1_i := weak_equiv_preserves_initial _ Fw _ (pr2 I1)).
    exact (ziso_Initials (_ ,, FI1_i) I2).
  Qed.

End WeakEquivalencePreservationsInitial.

Section WeakEquivalenceLiftsPreservesInitial.

  Lemma weak_equiv_lifts_preserves_initial
    {C1 C2 C3 : category}
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    (F_pI : preserves_initial F)
    : preserves_initial H.
  Proof.
    intros x2 x2_is_ini.
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x2)).
    { apply isaprop_isInitial. }
    intros [x1 i] y3.
    use (iscontrweqb' (Y :=  (C3⟦H(G x1), y3⟧))).
    - use (iscontrweqb' (Y := (C3⟦F x1, y3⟧))).
      + use F_pI.
        use (weak_equiv_reflects_initial _ Gw).
        exact (iso_to_Initial (_,, x2_is_ini) _ (z_iso_inv i)).
      + apply z_iso_comp_right_weq.
        exact (z_iso_inv (_ ,, pr2 α x1)).
    - apply z_iso_comp_right_weq.
      apply functor_on_z_iso.
      exact i.
  Qed.

End WeakEquivalenceLiftsPreservesInitial.
