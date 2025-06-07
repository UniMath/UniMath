(**
   Interaction Regular Epimorphisms And Weak Equivalences

   In this file, we show that weak equivalences reflect and preserve regular epimorphisms.
   Furthermore, we show that the preservation of reg. epis is lifts along weak equivalences.

   Contents.
   1. Preservation [weak_equiv_preserves_regular_epi]
   2. Reflection [weak_equiv_reflects_regular_epi]
   3. Lift Preservation [weak_equiv_lifts_preserves_regular_epi]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Coequalizers.

Local Open Scope cat.

(** * 1. Preservation *)
Lemma weak_equiv_preserves_regular_epi
  {C D : category} {F : functor C D} (F_weq : is_weak_equiv F)
  : preserves_regular_epi F.
Proof.
  intros x y f f_e.
  use (factor_through_squash _ _ f_e).
  { apply isapropishinh. }
  intros [w [g₁ [g₂ [p pe]]]].

  apply hinhpr.
  exists (F w).
  exists (#F g₁).
  exists (#F g₂).

  assert (p' : # F g₁ · # F f = # F g₂ · #F f). {
    do 2 rewrite <- functor_comp.
    apply maponpaths.
    exact p.
  }
  exists p'.
  exact (weak_equiv_preserves_coequalizers F_weq _ _ _ _  _ _ _ p' pe).
Qed.

(** * 2. Reflection *)
Lemma weak_equiv_reflects_regular_epi
  {C D : category} {F : functor C D} (F_weq : is_weak_equiv F)
  : ∏ (x y : C) (f : C⟦x, y⟧), is_regular_epi (#F f) → is_regular_epi f.
Proof.
  intros x y f f_e.
  use (factor_through_squash _ _ f_e).
  { apply isapropishinh. }
  intros [w [g₁ [g₂ [p pe]]]].

  use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq w)).
  { intro ; apply isaprop_is_regular_epi. }
  intros [v i].

  set (f₁ := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ (i · g₁) : C⟦v, x⟧).
  set (f₂ := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ (i · g₂) : C⟦v, x⟧).

  apply hinhpr.
  exists v.
  exists f₁.
  exists f₂.

  assert (p' : f₁ · f = f₂ · f). {
    apply (faithful_reflects_morphism_equality _ (ff_from_weak_equiv _ F_weq)).
    do 2 rewrite functor_comp.
    unfold f₁, f₂.
    do 2 rewrite functor_on_fully_faithful_inv_hom.
    do 2 rewrite assoc'.
    apply maponpaths.
    exact p.
  }

  exists p'.
  use (weak_equiv_reflects_coequalizers F_weq).
  intros u h pf.
  apply (pe u h).

  unfold f₁, f₂ in pf.
  do 2 rewrite (functor_on_fully_faithful_inv_hom _ (ff_from_weak_equiv _ F_weq)) in pf.
  use (cancel_z_iso' i).
  do 2 rewrite assoc.
  exact pf.
Qed.

(** * 3. Lift Preservation *)
Lemma weak_equiv_lifts_preserves_regular_epi
  {C : category} (D E : univalent_category)
  {F : functor C E} {G : functor C D} {H : functor D E}
  (α : nat_z_iso (functor_composite G H) F)
  (G_weq : is_weak_equiv G)
  : preserves_regular_epi F → preserves_regular_epi H.
Proof.
  intro F_e.
  unfold preserves_regular_epi.
  intros d₁ d₂ f_D f_D_e.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ G_weq d₁)).
  { intro ; apply isaprop_is_regular_epi. }
  intros [c₁ i₁].
  use (factor_through_squash _ _ (eso_from_weak_equiv _ G_weq d₂)).
  { intro ; apply isaprop_is_regular_epi. }
  intros [c₂ i₂].

  set (p₁ := isotoid _ (pr2 D) i₁).
  set (p₂ := isotoid _ (pr2 D) i₂).
  induction p₁.
  induction p₂.

  set (f_C := fully_faithful_inv_hom (ff_from_weak_equiv _ G_weq) _ _ f_D).

  assert (f_C_e : is_regular_epi f_C).
  {
    use (weak_equiv_reflects_regular_epi G_weq).
    unfold f_C.
    rewrite functor_on_fully_faithful_inv_hom.
    exact f_D_e.
  }

  set (f_E_e := F_e c₁ c₂ f_C f_C_e).
  set (αi := nat_z_iso_inv α).
  use (is_regular_epi_arrow_z_iso_f _ _ _ _ _ f_E_e).
  - apply (nat_z_iso_pointwise_z_iso αi).
  - apply (nat_z_iso_pointwise_z_iso αi).
  - etrans. { apply (nat_trans_ax αi). }
    simpl ; do 2 apply maponpaths.
    unfold f_C.
    now rewrite functor_on_fully_faithful_inv_hom.
Qed.
