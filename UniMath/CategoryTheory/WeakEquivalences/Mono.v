(**
   In this file, we show that weak equivalences reflect and preserve monomorphisms.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

Section ReflectionOfMonomorphisms.

  Context {C D : category}
    {F : C ⟶ D}
    (Fw : fully_faithful F).

  Context {d₁ d₂ : D}
    {c₁ c₂ : C}
    (i₁ : z_iso (F c₁) d₁)
    (i₂ : z_iso (F c₂) d₂).

  Let reflection (f : D⟦d₁, d₂⟧)
    : C⟦c₁, c₂⟧
    := fully_faithful_inv_hom Fw c₁ c₂ (i₁ · f· z_iso_inv i₂).

  Lemma reflection_of_mono_is_mono
    (f : D⟦d₁, d₂⟧)
    : isMonic f → isMonic (reflection f).
  Proof.
    intro fm.
    unfold reflection.
    apply (faithful_reflects_mono _ Fw).
    rewrite functor_on_fully_faithful_inv_hom.
    repeat (use isMonic_comp).
    + apply is_iso_isMonic, z_iso_is_z_isomorphism.
    + apply fm.
    + apply is_iso_isMonic, z_iso_is_z_isomorphism.
  Qed.

  Definition reflection_of_mono
    (f : Monic D d₁ d₂)
    : Monic C c₁ c₂
    := make_Monic _ (reflection f) (reflection_of_mono_is_mono f (pr2 f)).

End ReflectionOfMonomorphisms.

Lemma weak_equiv_preserves_monic
  {C D : category}
  {F : functor C D}
  (Fw : is_weak_equiv F)
  {x y : C} (m : Monic _ x y)
  : isMonic (#F m).
Proof.
  intros d g₁ g₂ p.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ Fw d)).
  { apply homset_property. }
  intros [d₀ i].
  set (h₁ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ (i · g₁)).
  set (h₂ := fully_faithful_inv_hom (ff_from_weak_equiv _ Fw) _ _ (i · g₂)).

  assert (pf₀ : h₁ = h₂).
  {
    use (pr2 m d₀ h₁ h₂).
    use (faithful_reflects_morphism_equality _ (pr2 Fw)).
    unfold h₁, h₂.
    do 2 rewrite functor_comp.
    do 2 rewrite functor_on_fully_faithful_inv_hom.
    rewrite ! assoc'.
    apply maponpaths.
    exact p.
  }

  assert (spf₀ : g₁ = z_iso_inv i · #F h₁).
  {
    unfold h₁.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc.
    rewrite z_iso_inv_after_z_iso.
    apply pathsinv0, id_left.
  }
  assert (spf₁ : g₂ = z_iso_inv i · #F h₂).
  {
    unfold h₂.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc.
    rewrite z_iso_inv_after_z_iso.
    apply pathsinv0, id_left.
  }
  refine (spf₀ @ _ @ ! spf₁).
  apply maponpaths.

  unfold h₁, h₂.
  apply maponpaths.
  exact pf₀.
Qed.

Definition weak_equiv_preserves_mono
  {C D : category}
  {F : functor C D}
  (Fw : is_weak_equiv F)
  {x y : C} (m : Monic _ x y)
  : Monic _ (F x) (F y)
  := #F m ,, weak_equiv_preserves_monic Fw m.
