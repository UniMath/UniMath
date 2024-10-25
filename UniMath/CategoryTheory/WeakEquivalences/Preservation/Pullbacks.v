(**
   In this file, we show that an arbitrary weak equivalence F : C -> D preserves pullbacks.
   The main work is done in weak_equiv_preserves_pullbacks, where we show that the image (under F) of a pullback in C, is also a pullback in D.

   If both C and D have pullbacks and D is univalent, we conclude that the image of a pullback is the pullback of the images.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section WeakEquivalencePreservationsPullbacks₀.

  Context {C D : category}
    {F : C ⟶ D}
    (Fw : is_weak_equiv F)
    {x y z p : C}
    {fₓ : C ⟦x, z⟧}
    {fy : C ⟦y, z⟧}
    {pₓ : C ⟦p, x⟧}
    {py : C ⟦p, y⟧}
    {r : pₓ · fₓ = py · fy}
    (iP : isPullback r).

  Let P := make_Pullback _ iP.

  Lemma weak_equiv_preserves_pullbacks_unique {q' : D}
    {qx' : D ⟦ q', F x ⟧}
    {qy' : D ⟦ q', F y ⟧}
    (r_q : qx' · # F fₓ = qy' · # F fy)
    {q : C}
    (i : z_iso (F q) q')
    : isaprop (∑ hk : D ⟦ q', F p ⟧, hk · # F pₓ = qx' × hk · # F py = qy').
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro ; apply isapropdirprod ; apply homset_property. }
    use (cancel_z_iso' i).

    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
    apply maponpaths.

    use (MorphismsIntoPullbackEqual (pr22 P)).
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
      exact (pr12 φ₂ @ ! (pr12 φ₁)).
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
      exact (pr22 φ₂ @ ! (pr22 φ₁)).
  Qed.

End WeakEquivalencePreservationsPullbacks₀.

Proposition weak_equiv_preserves_pullbacks
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  : preserves_pullback F.
Proof.
  intros x y z p fₓ fy pₓ py r_p Fr_p iP.
  pose (P := make_Pullback _ iP).
  intros q' qx' qy' r_q.

  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw q')).
  intros [q i].

  transparent assert (e : (D⟦q', F p⟧)). {
    use (z_iso_inv i · #F (pr11 (iP _ _ _ _))).
    + apply (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)).
      exact (i · qx').
    + apply (fully_faithful_inv_hom (ff_from_weak_equiv _ Fw)).
      exact (i · qy').
    + abstract (use (faithful_reflects_morphism_equality F (pr2 Fw)) ;
      do 2 rewrite functor_comp ;
      do 2 rewrite functor_on_fully_faithful_inv_hom ;
      do 2 rewrite assoc' ;
      apply maponpaths ;
      exact r_q).
  }

  assert (e₁ : e · # F pₓ = qx').
  {
    refine (assoc' _ _ _ @ _).
    rewrite <- (functor_comp F).
    etrans. {
      do 2 apply maponpaths.
      exact (pr121 (iP _ _ _ _)).
    }
    etrans. {
      apply maponpaths.
      apply functor_on_fully_faithful_inv_hom.
    }
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      apply z_iso_after_z_iso_inv.
    }
    apply id_left.
  }

  assert (e₂ :  e · # F py = qy'). {
    refine (assoc' _ _ _ @ _).
    rewrite <- (functor_comp F).
    etrans. {
      do 2 apply maponpaths.
      exact (pr221 (iP _ _ _ _)).
    }
    etrans. {
      apply maponpaths.
      apply functor_on_fully_faithful_inv_hom.
    }
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      apply z_iso_after_z_iso_inv.
    }
    apply id_left.
  }

  apply (iscontraprop1 (weak_equiv_preserves_pullbacks_unique Fw iP r_q i)).
  exact (e ,, (e₁ ,, e₂)).
Qed.

Corollary weak_equiv_preserves_chosen_pullbacks
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (PB : Pullbacks C)
  : preserves_chosen_pullback PB F.
Proof.
  intros x y f g p.
  use (weak_equiv_preserves_pullbacks Fw).
  - apply PullbackSqrCommutes.
  - apply isPullback_Pullback.
Qed.

Corollary weak_equiv_preserves_pullbacks_eq
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F) (Duniv : is_univalent D)
  (P₁ : Pullbacks C) (P₂ : Pullbacks D)
  : preserves_chosen_pullbacks_eq F P₁ P₂.
Proof.
  intros x y z f g.
  apply hinhpr.
  apply Duniv.
  set (Fp := weak_equiv_preserves_pullbacks Fw).

  use (z_iso_from_Pullback_to_Pullback
         (make_Pullback _ (Fp _ _ _ _ _ _ _ _ _ _ (pr22 (P₁ _ _ _ _ _))))
         (P₂ _ _ _ (#F f) (#F g))).
  do 2 rewrite <- functor_comp.
  apply maponpaths.
  apply P₁.
Qed.
