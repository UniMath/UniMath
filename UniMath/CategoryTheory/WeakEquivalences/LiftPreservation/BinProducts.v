(**
The universal property of the Rezk completion states, 1-dimensionally, that every functor F into a univalent category factors (uniquely) through the Rezk completion.
The unique functor out of the Rezk completion is referred to as ``the lift of F''.
The contents in this file conclude that if F preserves binary products, then so does its lift.

In [weak_equiv_lifts_preserves_binproducts], we show the following:
Assume F preserves all binary products in its domain.
Then, all binary products in the Rezk completion (of the domain) are also preserved.

In [weak_equiv_lifts_preserves_chosen_binproducts_eq], we show the following:
Assume all the involved categories have chosen binary products.
If F preserves the chosen binary products up to (propositional) equality, then so does it lift.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.

Local Open Scope cat.

Lemma weak_equiv_lifts_preserves_binproducts
    {C1 : category}
    (C2 C3 : univalent_category)
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    : preserves_binproduct F → preserves_binproduct H.
  Proof.
    intros Fprod y1 y2 py π₁p π₂p p_ispr.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y1)).
    { apply isaprop_isBinProduct. }
    intros [x1 i1].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y2)).
    { apply isaprop_isBinProduct. }
    intros [x2 i2].

    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw py)).
    { apply isaprop_isBinProduct. }
    intros [px i].

    set (G_reflect := weak_equiv_reflects_products (ff_from_weak_equiv _ Gw) x1 x2 px).
    set (π₁ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i · π₁p · z_iso_inv i1)).
    set (π₂ := (fully_faithful_inv_hom (ff_from_weak_equiv _ Gw)) _ _ (i · π₂p · z_iso_inv i2)).

    set (is1 := z_iso_comp (functor_on_z_iso H (z_iso_inv i1)) ((_,, pr2 α x1))).
    set (is2 := z_iso_comp (functor_on_z_iso H (z_iso_inv i2)) ((_,, pr2 α x2))).

    assert (pf1 :  i · π₁p = # G π₁ · i1).
    {
      unfold π₁.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      rewrite z_iso_inv_after_z_iso.
      now rewrite id_right.
    }

    assert (pf2 :  i · π₂p = # G π₂ · i2).
    {
      unfold π₂.
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite assoc'.
      rewrite z_iso_inv_after_z_iso.
      now rewrite id_right.
    }

    use (isbinproduct_of_isos _ is1 is2).
    + use (make_BinProduct _ _ _ _ _ _ (Fprod _ _ _ _ _ (G_reflect π₁ π₂ _))).
      exact (isbinproduct_of_isos (make_BinProduct _ _ _ _ _ _ p_ispr) i1 i2 i _ _ pf1 pf2).
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

  Lemma weak_equiv_lifts_preserves_chosen_binproducts_eq
  {C1 : category}
  (C2 C3 : univalent_category)
  {F : C1 ⟶ C3}
  {G : C1 ⟶ C2}
  {H : C2 ⟶ C3}
  (α : nat_z_iso (G ∙ H) F)
  (C1_prod : BinProducts C1)
  (C2_prod : BinProducts (pr1 C2))
  (C3_prod : BinProducts (pr1 C3))
  (Gw : is_weak_equiv G)
  : preserves_chosen_binproducts_eq F C1_prod C3_prod
    → preserves_chosen_binproducts_eq H C2_prod C3_prod.
Proof.
  intros Fprod y1 y2.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y1)).
  { apply isapropishinh. }
  intros [x1 i1].

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw y2)).
  { apply isapropishinh. }
  intros [x2 i2].

  unfold preserves_chosen_binproducts_eq in Fprod.

  use (factor_through_squash _ _ (Fprod x1 x2)).
  { apply isapropishinh. }
  intro p.

  pose (ϕ₁ := nat_z_iso_pointwise_z_iso α x1).
  pose (ϕ₂ := nat_z_iso_pointwise_z_iso α x2).
  pose (ϕ₃ := nat_z_iso_pointwise_z_iso α (C1_prod x1 x2)).

  pose (ψ₁ := isotoid _ (pr2 C3) ϕ₁).
  pose (ψ₂ := isotoid _ (pr2 C3) ϕ₂).
  pose (ψ₃ := isotoid _ (pr2 C3) ϕ₃).

  pose (j1 := isotoid _ (pr2 C2) i1).
  pose (j2 := isotoid _ (pr2 C2) i2).

  (*
    H (y1 × y2) = H (G x1 × G x2)
      = H (G (x1 × x2))
      = F (x1 × x2)
      = F x1 × F x2
      = H(G(x1)) × H(G(x2))
      = H y1 × H y2.

   *)

  set (Gprod := weak_equiv_preserves_binproducts_eq Gw (pr2 C2) C1_prod C2_prod).
  use (factor_through_squash _ _ (Gprod x1 x2)).
  { apply isapropishinh. }
  intro Gx1x2.
  clear Gprod.

  apply hinhpr.

  rewrite <- j1, <- j2.
  etrans. {
    apply maponpaths.
    exact (! Gx1x2).
  }

  refine (ψ₃ @ _).
  refine (p @ _).

  refine (maponpaths (fun z => BinProductObject _ (C3_prod z _)) _ @ _).
  { exact (! ψ₁). }
  refine (maponpaths (fun z => BinProductObject _ (C3_prod _ z)) _).
  exact (! ψ₂).
Qed.
