Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.

Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.SubObjectClassifier.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.SubObjectClassifier.Reflection.

Local Open Scope cat.

Lemma weak_equiv_lifts_preserves_terminal
    {C1 C2 C3 : category}
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    (Fpterm : preserves_terminal F)
    : preserves_terminal H.
  Proof.
    intros x2 x2_is_term.
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x2)).
    { apply isaprop_isTerminal. }
    intros [x1 i] y3.
    use (iscontrweqb' (Y :=  (C3⟦y3, H(G x1)⟧))).
    + use (iscontrweqb' (Y := (C3⟦y3, F x1⟧))).
      * use (Fpterm _ _).
        use (weak_equiv_reflects_terminal _ Gw).
        exact (iso_to_Terminal (_,, x2_is_term) _ (z_iso_inv i)).
      * apply z_iso_comp_left_weq.
        exact (_ ,, pr2 α x1).
    + apply z_iso_comp_left_weq.
      apply functor_on_z_iso.
      exact (z_iso_inv i).
  Qed.

Section LiftAlongWeakEquivalencePreservesSubobjectClassifier.

  Context {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    (Fpt : preserves_terminal F)
    (T1 : Terminal C1)
    (T3 : Terminal C3)
    (Fps : preserves_subobject_classifier _ T1 T3 Fpt).

  Let T2 : Terminal C2 := _ ,, weak_equiv_preserves_terminal _ Gw (pr1 T1) (pr2 T1).

  Section Aux.

    Context {Ω₂ : C2}
      {tr₂ : C2⟦T2, Ω₂⟧}
      (Ω₂_issoc : is_subobject_classifier T2 Ω₂ tr₂)
      {Ω₁ : C1}
      (i₁ : z_iso (G Ω₁) Ω₂).

    Let Hpt := weak_equiv_lifts_preserves_terminal α Gw Fpt.
    Let T3' := preserves_terminal_to_terminal H Hpt T2.
    Let tr₃ := TerminalArrow T3' T3 · # H tr₂.

    Let t_12 := pr1 (pr2 T2 _) : C2⟦G T1, T2⟧.
    Let tr₁ := fully_faithful_inv_hom (pr2 Gw) T1 Ω₁ (t_12 · tr₂ · z_iso_inv i₁).

    Lemma Ω₁_issoc'
      : tr₂ · inv_from_z_iso i₁
        = # G tr₁.
    Proof.
      refine (_ @ ! functor_on_fully_faithful_inv_hom _ (pr2 Gw) _).
      apply maponpaths_2.
      refine (! id_left _ @ _).
      apply maponpaths_2.
      use proofirrelevancecontr.
      apply (weak_equiv_preserves_terminal _ Gw _ (pr2 T1)).
    Qed.

    Lemma Ω₁_issoc : is_subobject_classifier T1 Ω₁ tr₁.
    Proof.
      use (weak_equiv_reflects_is_subobject_classifier T1 Gw).
      use (SubobjectClassifierIso.z_iso_to_is_subobject_classifier (make_subobject_classifier _ _ Ω₂_issoc)).
      - exact (z_iso_inv i₁).
      - exact Ω₁_issoc'.
    Qed.

    Let Ω₃_H_issoc := Fps Ω₁ tr₁ Ω₁_issoc.
    Let Ω₃_H := make_subobject_classifier _ _ Ω₃_H_issoc.

    Lemma weak_equiv_lifts_preserves_subobject_classifier''
      : true' Ω₃_H · (inv_from_z_iso (nat_z_iso_pointwise_z_iso α Ω₁) · # H i₁) = tr₃.
    Proof.
      unfold Ω₃_H.
      cbn.
      etrans. {
        rewrite assoc.
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply (nat_trans_ax (nat_z_iso_inv α) _ _ _).
      }
      etrans. {
        apply maponpaths_2.
        do 2 apply maponpaths.
        simpl.
        apply maponpaths.
        apply functor_on_fully_faithful_inv_hom.
      }
      unfold tr₃.
      rewrite ! assoc.

      assert (tmp₀ : TerminalArrow (preserves_terminal_to_terminal F Fpt T1) T3 · nat_z_iso_inv α (pr1 T1) = TerminalArrow T3' T3).
      {
        use proofirrelevancecontr.
        apply Hpt, T2.
      }
      rewrite <- tmp₀.
      rewrite ! assoc'.
      do 2 apply maponpaths.
      refine (! functor_comp H _ _ @ _).
      apply maponpaths.
      rewrite ! assoc'.
      rewrite z_iso_after_z_iso_inv.
      rewrite id_right.
      refine (_ @ id_left _ ).
      apply maponpaths_2.
      use proofirrelevancecontr.
      apply (weak_equiv_preserves_terminal G Gw).
      apply T1.
    Qed.

    Lemma weak_equiv_lifts_preserves_subobject_classifier'
      : is_subobject_classifier T3 (H Ω₂) tr₃.
    Proof.
      use (SubobjectClassifierIso.z_iso_to_is_subobject_classifier Ω₃_H).
      - use (z_iso_comp (z_iso_inv (nat_z_iso_pointwise_z_iso α Ω₁))) ; simpl.
        apply (functor_on_z_iso H).
        exact i₁.
      - exact weak_equiv_lifts_preserves_subobject_classifier''.
    Qed.

  End Aux.

  Lemma weak_equiv_lifts_preserves_subobject_classifier
    : preserves_subobject_classifier H T2 T3 (weak_equiv_lifts_preserves_terminal α Gw Fpt).
  Proof.
    intros Ω₂ tr₂ Ω₂_issoc.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw Ω₂)).
    { apply isaprop_is_subobject_classifier. }
    intros [Ω₁ i₁].

    exact (weak_equiv_lifts_preserves_subobject_classifier' Ω₂_issoc i₁).
  Qed.

End LiftAlongWeakEquivalencePreservesSubobjectClassifier.
