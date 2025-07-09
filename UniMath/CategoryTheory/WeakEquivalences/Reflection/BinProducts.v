(**
   In this file, we show that weak equivalences reflect binary products.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section WeakEquivalencesReflectBinproducts₀.

  Context
    {C D : category} {F : C ⟶ D} (Fw : fully_faithful F)
      (c1 c2 p : C) (π₁ : C⟦p, c1⟧) (π₂ : C⟦p, c2⟧)
      (Hp : isBinProduct _ (F c1) (F c2) (F p) (#F π₁) (#F π₂)).

  Context (x : C)
    (f1 : C⟦x, c1⟧)
    (f2 : C⟦x, c2⟧).

  Let fg : C ⟦x, p⟧
    := fully_faithful_inv_hom Fw _ _ (pr11 (Hp _ (#F f1) (#F f2))).

  Lemma weak_equiv_reflect_binproducts_first_projection_commute
    : fg · π₁ = f1.
  Proof.
    unfold fg.
    refine (! homotinvweqweq (weq_from_fully_faithful Fw _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful Fw _ _) _).
    apply maponpaths.
    simpl.
    rewrite functor_comp.
    etrans. {
      apply maponpaths_2.
      apply (homotweqinvweq (weq_from_fully_faithful Fw _ _)).
    }
    exact (pr121 (Hp _ (#F f1) (#F f2))).
  Qed.

  Lemma weak_equiv_reflect_binproducts_second_projection_commute
    : fg · π₂ = f2.
  Proof.
    unfold fg.
    refine (! homotinvweqweq (weq_from_fully_faithful Fw _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful Fw _ _) _).
    apply maponpaths.
    simpl.
    rewrite functor_comp.
    etrans. {
      apply maponpaths_2.
      apply (homotweqinvweq (weq_from_fully_faithful Fw _ _)).
    }
    exact (pr221 (Hp _ (#F f1) (#F f2))).
  Qed.

  Lemma weak_equiv_reflect_binproducts_uvp_uniqueness
    : isaprop (∑ fg0 : C ⟦ x, p ⟧, fg0 · π₁ = f1 × fg0 · π₂ = f2).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro. apply isapropdirprod ; apply homset_property. }

    refine (! homotinvweqweq (weq_from_fully_faithful Fw _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful Fw _ _) _).

    apply maponpaths.
    cbn.
    use (BinProductArrowsEq _ _ _ (make_BinProduct _ _ _ _ _ _ Hp)).
    - cbn.
      rewrite <- ! functor_comp.
      apply maponpaths.
      exact (pr12 φ₁ @ ! pr12 φ₂).
    - cbn.
      rewrite <- ! functor_comp.
      apply maponpaths.
      exact (pr22 φ₁ @ ! pr22 φ₂).
  Qed.

  Definition weak_equiv_reflect_binproducts_uvp_existence
    : ∑ fg : C ⟦ x, p ⟧, fg · π₁ = f1 × fg · π₂ = f2.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact fg.
    - apply weak_equiv_reflect_binproducts_first_projection_commute.
    - apply weak_equiv_reflect_binproducts_second_projection_commute.
  Defined.

End WeakEquivalencesReflectBinproducts₀.

Proposition weak_equiv_reflects_products
  {C D : category} {F : C ⟶ D} (Fw : fully_faithful F)
  : ∏ (c1 c2 p : C) (π₁ : C⟦p, c1⟧) (π₂ : C⟦p, c2⟧),
    isBinProduct _ (F c1) (F c2) (F p) (#F π₁) (#F π₂) → isBinProduct _ c1 c2 p π₁ π₂.
Proof.
  intros.
  intros x f1 f2.
  use iscontraprop1.
  - apply (weak_equiv_reflect_binproducts_uvp_uniqueness Fw _ _ _ _ _ X).
  - apply (weak_equiv_reflect_binproducts_uvp_existence Fw _ _ _ _ _ X).
Qed.
