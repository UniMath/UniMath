(**
   Lifting Of Binary Coproduct Preservation Along Weak Equivalences

   In this file, we show that the lifting of a "binary coproduct"-preserving functor along a weak equivalence is also binary coproduct preserving

   Contents
   1. Lift Preservation [weak_equiv_lifts_preserves_bincoproducts]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.BinCoproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Bincoproducts.

Local Open Scope cat.

(** * 1. Lifting Of Preservation *)
Lemma weak_equiv_lifts_preserves_bincoproducts
    {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
  : preserves_bincoproduct F → preserves_bincoproduct H.
Proof.
  intros Fprod y1 y2 py π₁p π₂p p_ispr.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y1)).
  { apply isaprop_isBinCoproduct. }
  intros [x1 i1].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y2)).
  { apply isaprop_isBinCoproduct. }
  intros [x2 i2].

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw py)).
  { apply isaprop_isBinCoproduct. }
  intros [px i].

  set (G_reflect := weak_equiv_reflects_coproducts (ff_from_weak_equiv _ Gw) x1 x2 px).
  set (π₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i1 · π₁p · z_iso_inv i)).
  set (π₂ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i2 · π₂p · z_iso_inv i)).

  set (is1 := z_iso_comp (functor_on_z_iso H (z_iso_inv i1)) ((_,, pr2 α x1))).
  set (is2 := z_iso_comp (functor_on_z_iso H (z_iso_inv i2)) ((_,, pr2 α x2))).

  assert (pf1 : i1 · π₁p = #G π₁ · i).
  {
    unfold π₁.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc'.
    rewrite z_iso_inv_after_z_iso.
    now rewrite id_right.
  }

  assert (pf2 :  i2 · π₂p = # G π₂ · i).
  {
    unfold π₂.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc'.
    rewrite z_iso_inv_after_z_iso.
    now rewrite id_right.
  }

  use (isbincoproduct_of_isos _ _ is1 is2).
  + use (make_BinCoproduct _ _ _ _ _ _ (Fprod _ _ _ _ _ (G_reflect π₁ π₂ _))).
    exact (isbincoproduct_of_isos (make_BinCoproduct _ _ _ _ _ _ p_ispr) _ i1 i2 i _ _ pf1 pf2).
  + exact (z_iso_comp (functor_on_z_iso H (z_iso_inv i)) (_ ,, pr2 α px)).
  + simpl.
    rewrite assoc'.
    etrans. {
      apply maponpaths.
      exact (! pr21 α _ _ π₁).
    }
    simpl.
    rewrite ! assoc.
    rewrite <- ! functor_comp.
    apply maponpaths_2, maponpaths.
    use z_iso_inv_on_left.
    rewrite assoc'.
    rewrite <- pf1.
    rewrite assoc.
    rewrite z_iso_after_z_iso_inv.
    now rewrite ! id_left.
    + simpl.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        exact (! pr21 α _ _ π₂).
      }
      simpl.
      rewrite ! assoc.
      rewrite <- ! functor_comp.
      apply maponpaths_2, maponpaths.
      use z_iso_inv_on_left.
      rewrite assoc'.
      rewrite <- pf2.
      rewrite assoc.
      rewrite z_iso_after_z_iso_inv.
      now rewrite ! id_left.
Qed.
