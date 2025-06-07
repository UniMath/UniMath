(**
   Reflection Of Binary Coproducts Along Weak Equivalences

   In this file, we show that weak equivalences reflect binary coproducts.

   Contents
   1. Reflection of binary coproducts [weak_equiv_reflects_coproducts]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

(** 1. Reflection *)
Section WeakEquivalencesReflectBincoproducts₀.

  Context
    {C D : category} {F : C ⟶ D} (Fw : fully_faithful F)
      (c1 c2 p : C) (π₁ : C⟦c1, p⟧) (π₂ : C⟦c2, p⟧)
      (Hp : isBinCoproduct _ (F c1) (F c2) (F p) (#F π₁) (#F π₂)).

  Context (x : C) (f1 : C⟦c1, x⟧) (f2 : C⟦c2, x⟧).

  Let fg : C ⟦p, x⟧
    := fully_faithful_inv_hom Fw _ _ (pr11 (Hp _ (#F f1) (#F f2))).

  Lemma weak_equiv_reflect_bincoproducts_first_inclusion_commute
    : π₁ · fg = f1.
  Proof.
    unfold fg.
    refine (! homotinvweqweq (weq_from_fully_faithful Fw _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful Fw _ _) _).
    apply maponpaths.
    simpl.
    rewrite functor_comp.
    etrans. {
      apply maponpaths.
      apply (homotweqinvweq (weq_from_fully_faithful Fw _ _)).
    }
    exact (pr121 (Hp _ (#F f1) (#F f2))).
  Qed.

  Lemma weak_equiv_reflect_bincoproducts_second_inclusion_commute
    : π₂ · fg = f2.
  Proof.
    unfold fg.
    refine (! homotinvweqweq (weq_from_fully_faithful Fw _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful Fw _ _) _).
    apply maponpaths.
    simpl.
    rewrite functor_comp.
    etrans. {
      apply maponpaths.
      apply (homotweqinvweq (weq_from_fully_faithful Fw _ _)).
    }
    exact (pr221 (Hp _ (#F f1) (#F f2))).
  Qed.

  Lemma weak_equiv_reflect_bincoproducts_uvp_uniqueness
    : isaprop (∑ fg : C⟦p, x⟧, π₁ · fg = f1 × π₂ · fg = f2).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro. apply isapropdirprod ; apply homset_property. }

    refine (! homotinvweqweq (weq_from_fully_faithful Fw _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful Fw _ _) _).

    apply maponpaths.
    cbn.
    use (BinCoproductArrowsEq _ _ _ (make_BinCoproduct _ _ _ _ _ _ Hp)).
    - cbn.
      rewrite <- ! functor_comp.
      apply maponpaths.
      exact (pr12 φ₁ @ ! pr12 φ₂).
    - cbn.
      rewrite <- ! functor_comp.
      apply maponpaths.
      exact (pr22 φ₁ @ ! pr22 φ₂).
  Qed.

  Definition weak_equiv_reflect_bincoproducts_uvp_existence
    : ∑ fg : C⟦p, x⟧, π₁ · fg = f1 × π₂ · fg = f2.
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact fg.
    - apply weak_equiv_reflect_bincoproducts_first_inclusion_commute.
    - apply weak_equiv_reflect_bincoproducts_second_inclusion_commute.
  Defined.

End WeakEquivalencesReflectBincoproducts₀.

Proposition weak_equiv_reflects_coproducts
  {C D : category} {F : C ⟶ D} (Fw : fully_faithful F)
  : ∏ (c1 c2 p : C) (π₁ : C⟦c1, p⟧) (π₂ : C⟦c2, p⟧),
    isBinCoproduct _ (F c1) (F c2) (F p) (#F π₁) (#F π₂) → isBinCoproduct _ c1 c2 p π₁ π₂.
Proof.
  intros.
  intros x f1 f2.
  use iscontraprop1.
  - apply (weak_equiv_reflect_bincoproducts_uvp_uniqueness Fw _ _ _ _ _ X).
  - apply (weak_equiv_reflect_bincoproducts_uvp_existence Fw _ _ _ _ _ X).
Qed.
