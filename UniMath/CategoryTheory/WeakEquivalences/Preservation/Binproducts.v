(**
   In this file, we show that an arbitrary weak equivalence F : C -> D preserves binary products.
   The main work is done in [weak_equiv_preserves_binproducts], where we show that the image (under F) of a binary product in C is also a product in D.

   If both C and D have binary products and D is univalent, we conclude that the image of a pullback is the pullback of the images.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section WeakEquivalencePreservationsBinProducts₀.

  Context {C D : category}
    {F : C ⟶ D}
    (Fw : is_weak_equiv F)
    {x1 x2 : C} {y : D}
    (BP : BinProduct _ x1 x2)
    (g1 : D ⟦ y, F x1⟧)
    (g2 : D ⟦ y, F x2 ⟧)
    {x : C}
    (yi : z_iso (F x) y).

  Let f1 : C⟦x, x1⟧ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) x x1 (yi · g1).
  Let f2 : C⟦x, x2⟧ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) x x2 (yi · g2).

  Definition weak_equiv_preserves_binproducts_map
    : D⟦y, F BP⟧
    := inv_from_z_iso yi · #F (BinProductArrow _ BP f1 f2).

  Lemma weak_equiv_preserves_binproducts_pr1
    : weak_equiv_preserves_binproducts_map · # F (BinProductPr1 C BP)
      = g1.
  Proof.
    unfold weak_equiv_preserves_binproducts_map.
    rewrite assoc'.
    rewrite <- functor_comp.
    rewrite BinProductPr1Commutes.
    unfold f1; rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc.
    rewrite z_iso_after_z_iso_inv.
    apply id_left.
  Qed.

  Lemma weak_equiv_preserves_binproducts_pr2
    : weak_equiv_preserves_binproducts_map · # F (BinProductPr2 C BP)
      = g2.
  Proof.
    unfold weak_equiv_preserves_binproducts_map.
    rewrite assoc'.
    rewrite <- functor_comp.
    rewrite BinProductPr2Commutes.
    unfold f2; rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc.
    rewrite z_iso_after_z_iso_inv.
    apply id_left.
  Qed.

  Lemma weak_equiv_preserves_binproducts_unique
    : isaprop
        (∑ fg : D⟦y, F BP⟧,
            fg · # F (BinProductPr1 C BP) = g1 × fg · # F (BinProductPr2 C BP) = g2
        ).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro. apply isapropdirprod ; apply homset_property. }

    use (cancel_z_iso' yi).

    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).

    apply maponpaths.
    use BinProductArrowsEq.
    - refine (! homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
      refine (_ @ homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
      apply maponpaths.
      simpl.
      rewrite ! functor_comp.
      etrans.
      {
        apply maponpaths_2.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      refine (! _).

      etrans. {
        apply maponpaths_2.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      rewrite ! assoc'.
      apply maponpaths.
      exact (pr12 φ₂ @ ! pr12 φ₁).
    - refine (! homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
      refine (_ @ homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
      apply maponpaths.
      simpl.
      rewrite ! functor_comp.
      etrans.
      {
        apply maponpaths_2.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      refine (! _).

      etrans. {
        apply maponpaths_2.
        apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _)).
      }
      rewrite ! assoc'.
      apply maponpaths.
      exact (pr22 φ₂ @ ! pr22 φ₁).
  Qed.

End WeakEquivalencePreservationsBinProducts₀.

Proposition weak_equiv_preserves_binproducts
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  : preserves_binproduct F.
Proof.
  intros x1 x2 px π₁ π₂ Hyp.
  pose (BP := make_BinProduct _ _ _ _ _ _ Hyp).
  intros y g1 g2.

  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw y)).
  intros [x yi].

  use iscontraprop1.
  - exact (weak_equiv_preserves_binproducts_unique Fw BP _ _ yi).
  - simple refine (_ ,, _ ,, _).
    + exact (weak_equiv_preserves_binproducts_map Fw BP g1 g2 yi).
    + apply (weak_equiv_preserves_binproducts_pr1 Fw BP).
    + apply (weak_equiv_preserves_binproducts_pr2 Fw BP).
Defined.

Corollary weak_equiv_preserves_chosen_binproducts
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (BP : BinProducts C)
  : preserves_chosen_binproduct BP F.
Proof.
  intros x1 x2.
  use (weak_equiv_preserves_binproducts Fw).
  apply isBinProduct_BinProduct.
Defined.

Corollary weak_equiv_preserves_binproducts_eq
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (Duniv : is_univalent D)
  (BP₁ : BinProducts C) (BP₂ : BinProducts D)
  : preserves_chosen_binproducts_eq F BP₁ BP₂.
Proof.
  intros x y.
  apply hinhpr.
  apply Duniv.
  set (Fp := weak_equiv_preserves_binproducts Fw).
  set (p := make_BinProduct _ _ _ _ _ _ (Fp x y (BP₁ x y) _ _ (pr2 (BP₁ x y)))).
  exact (iso_between_BinProduct p (BP₂ (F x) (F y))).
Qed.
