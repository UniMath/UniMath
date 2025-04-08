(**
   In this file, we show that an arbitrary weak equivalence F : C -> D preserves binary coproducts.
   The main work is done in [weak_equiv_preserves_bincoproducts], where we show that the image (under F) of a binary coproduct in C is also a coproduct in D.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section WeakEquivalencePreservationsBinCoproducts₀.

  Context {C D : category}
    {F : C ⟶ D}
    (Fw : is_weak_equiv F)
    {x1 x2 : C} {y : D}
    (BC : BinCoproduct x1 x2)
    (g1 : D⟦F x1, y⟧)
    (g2 : D⟦F x2, y⟧)
    {x : C}
    (yi : z_iso (F x) y).

  Let f1 : C⟦x1, x⟧ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ (g1 · z_iso_inv yi).
  Let f2 : C⟦x2, x⟧ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ (g2 · z_iso_inv yi).

  Definition weak_equiv_preserves_bincoproducts_map
    : D⟦F BC, y⟧
    := #F (BinCoproductArrow BC f1 f2) · yi.

  Lemma weak_equiv_preserves_bincoproducts_in1
    : # F (BinCoproductIn1 BC) · weak_equiv_preserves_bincoproducts_map = g1.
  Proof.
    unfold weak_equiv_preserves_bincoproducts_map.
    rewrite assoc.
    rewrite <- functor_comp.
    rewrite BinCoproductIn1Commutes.
    unfold f1; rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc'.
    rewrite z_iso_inv_after_z_iso.
    apply id_right.
  Qed.

  Lemma weak_equiv_preserves_bincoproducts_in2
    : # F (BinCoproductIn2 BC) · weak_equiv_preserves_bincoproducts_map = g2.
  Proof.
    unfold weak_equiv_preserves_bincoproducts_map.
    rewrite assoc.
    rewrite <- functor_comp.
    rewrite BinCoproductIn2Commutes.
    unfold f2; rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc'.
    rewrite z_iso_inv_after_z_iso.
    apply id_right.
  Qed.

  Lemma weak_equiv_preserves_bincoproducts_unique
    : isaprop (∑ fg : D⟦F BC, y⟧, # F (BinCoproductIn1 BC) · fg = g1 × # F (BinCoproductIn2 BC) · fg = g2).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro. apply isapropdirprod ; apply homset_property. }

    use (cancel_z_iso _ _ (z_iso_inv yi)).

    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).

    apply maponpaths.
    use BinCoproductArrowsEq.
    - refine (! homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
      refine (_ @ homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
      apply maponpaths.
      simpl.
      rewrite ! functor_comp.
      etrans.
      {
        apply maponpaths.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      refine (! _).

      etrans. {
        apply maponpaths.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      rewrite ! assoc.
      apply maponpaths_2.
      exact (pr12 φ₂ @ ! pr12 φ₁).
    - refine (! homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
      refine (_ @ homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
      apply maponpaths.
      simpl.
      rewrite ! functor_comp.
      etrans.
      {
        apply maponpaths.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      refine (! _).

      etrans. {
        apply maponpaths.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      rewrite ! assoc.
      apply maponpaths_2.
      exact (pr22 φ₂ @ ! pr22 φ₁).
  Qed.

End WeakEquivalencePreservationsBinCoproducts₀.

Proposition weak_equiv_preserves_bincoproducts
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  : preserves_bincoproduct F.
Proof.
  intros x1 x2 px π₁ π₂ Hyp.
  pose (BP := make_BinCoproduct _ _ _ _ _ _ Hyp).
  intros y g1 g2.

  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw y)).
  intros [x yi].

  use iscontraprop1.
  - exact (weak_equiv_preserves_bincoproducts_unique Fw BP _ _ yi).
  - simple refine (_ ,, _ ,, _).
    + exact (weak_equiv_preserves_bincoproducts_map Fw BP g1 g2 yi).
    + apply (weak_equiv_preserves_bincoproducts_in1 Fw BP).
    + apply (weak_equiv_preserves_bincoproducts_in2 Fw BP).
Qed.

Corollary weak_equiv_preserves_chosen_bincoproducts
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (BP : BinCoproducts C)
  : preserves_chosen_bincoproduct BP F.
Proof.
  intros x1 x2.
  use (weak_equiv_preserves_bincoproducts Fw).
  apply isBinCoproduct_BinCoproduct.
Qed.
