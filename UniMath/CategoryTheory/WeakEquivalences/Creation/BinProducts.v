(**

In this file, we show how a weak equivalence F : C1 -> C2, with C2 univalent (i.e., the Rezk completion), creates binary products.
We consider two cases:
1. C1 (merely) has binary products;
2. C1 has chosen binary products.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.

Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.BinProducts.

Local Open Scope cat.

Definition weak_equiv_into_univ_creates_hasbinproducts
    {C1 C2 : category}
    (C2_univ : is_univalent C2)
    {F : C1 ⟶ C2}
    (Fw : is_weak_equiv F)
    (BP₁ : hasBinProducts C1)
  : hasBinProducts C2.
Proof.
  intros y1 y2.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y1)).
  { apply propproperty. }
  intros [x1 i1].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y2)).
  { apply propproperty. }
  intros [x2 i2].

  use (factor_through_squash _ _ (BP₁ x1 x2)).
  { apply propproperty. }
  intro p.
  apply hinhpr.
  simpl in BP₁.

  set (t := weak_equiv_preserves_binproducts Fw _ _ _ _ _ (pr2 p)).
  pose (PB := make_BinProduct _ _ _ _ _ _ t).
  exact (binproduct_of_isos PB i1 i2).
Defined.

Definition weak_equiv_into_univ_creates_binproducts
  {C1 C2 : category}
  (C2_univ : is_univalent C2)
  {F : C1 ⟶ C2}
  (Fw : is_weak_equiv F)
  (C1_prod : BinProducts C1)
  : BinProducts C2.
Proof.
  intros x2 y2.
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw x2)).
  { apply (isaprop_BinProduct C2_univ). }
  intros [x1 ix].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw y2)).
  { apply (isaprop_BinProduct C2_univ). }
  intros [y1 iy].

  use (binproduct_of_isos _ ix iy).

  set (t := weak_equiv_preserves_chosen_binproducts Fw C1_prod).
  exact (make_BinProduct _ _ _ _ _ _ (t x1 y1)).
Qed.
