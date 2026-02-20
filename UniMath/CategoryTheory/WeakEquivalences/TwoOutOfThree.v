(*
  A (partial) 2-out-of-3 law for weak equivalences

  Let α : F ≅ G · H be a triangle of functors.
  If F and G are weak equivalences, then so is H.

  Contents.
  1. [two_out_of_three_weak_equiv] proves that H is a weak equivalence.

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Local Open Scope cat.

Section TwoOutOfThree.

  Context {C D E : category} (F : functor C E) (G : functor C D) (H : functor D E)
    (α : nat_z_iso F (functor_composite G H)).

  Lemma two_out_of_three_eso
    : essentially_surjective F → essentially_surjective G → essentially_surjective H.
  Proof.
    intros Fe Ge.
    intro e.
    use (factor_through_squash _ _ (Fe e)).
    { apply isapropishinh. }
    intros [c i].

    apply hinhpr.
    exists (G c).
    exact (z_iso_inv (z_iso_comp (z_iso_inv i) (nat_z_iso_pointwise_z_iso α c))).
  Defined.

  Lemma two_out_of_three_ff
    : fully_faithful F → is_weak_equiv G → fully_faithful H.
  Proof.
    intros Ff Gf.
    intros d₁ d₂.

    use (factor_through_squash _ _ (pr1 Gf d₁)).
    { apply isapropisweq. }
    intros [c₁ i₁].
    use (factor_through_squash _ _ (pr1 Gf d₂)).
    { apply isapropisweq. }
    intros [c₂ i₂].

    set (α₁ := (nat_z_iso_pointwise_z_iso α c₁)).
    set (α₂ := (nat_z_iso_pointwise_z_iso α c₂)).

    use isweq_iso.
    - intro f_E.
      set (f_C := fully_faithful_inv_hom Ff _ _ (α₁ · #H i₁ · f_E · #H (z_iso_inv i₂) · z_iso_inv α₂)).
      exact (z_iso_inv i₁ · #G f_C · i₂).
    - intro f_D.
      use z_iso_inv_to_right.
      use z_iso_inv_on_right.
      etrans.
      2: { apply (functor_on_fully_faithful_inv_hom _ (pr2 Gf)). }
      apply maponpaths.
      use (faithful_reflects_morphism_equality _ (Ff)).
      etrans. { apply functor_on_fully_faithful_inv_hom. }
      apply pathsinv0.
      use z_iso_inv_on_left.
      rewrite ! assoc'.
      apply pathsinv0.
      use z_iso_inv_to_left.
      etrans. {
        apply maponpaths, (nat_trans_ax α).
      }
      rewrite assoc.
      rewrite z_iso_after_z_iso_inv.
      rewrite id_left.
      simpl.
      rewrite functor_on_fully_faithful_inv_hom.
      now rewrite ! functor_comp.
    - intro f_E.
      simpl.
      rewrite ! functor_comp.

      use (z_iso_inv_to_right _ _ _ _ (functor_on_z_iso H i₂)).
      use (z_iso_inv_on_right _ _ _ (functor_on_z_iso H i₁)).
      cbn.

      use (cancel_z_iso' α₁).
      etrans. { apply pathsinv0, (nat_trans_ax α). }
      etrans. {
        apply maponpaths_2, functor_on_fully_faithful_inv_hom.
      }
      rewrite ! assoc'.
      rewrite z_iso_after_z_iso_inv.
      now rewrite id_right.
  Qed.

  Corollary two_out_of_three_weak_equiv
    : is_weak_equiv F → is_weak_equiv G → is_weak_equiv H.
  Proof.
    intros [Fe Ff] GG.
    split.
    - exact (two_out_of_three_eso Fe (pr1 GG)).
    - exact (two_out_of_three_ff Ff GG).
  Qed.

End TwoOutOfThree.
