(**
   In this file, we show how weak equivalences reflect subobject classifiers.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.

Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Mono.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.SubobjectClassifier.

Local Open Scope cat.

Section WeakEquivalencesReflectSubobjectClassifiersExistence.

  Context {C D : category} (T_C : Terminal C)
    {F : C ⟶ D} (Fw : is_weak_equiv F) (T_D : isTerminal D (F T_C)).

  Let image_of_terminal_is_terminal : Terminal D
    := F T_C ,, T_D.

  Context {Ω : ob C} (tr : C⟦T_C, Ω⟧)
    (is_cl : is_subobject_classifier (C := D) image_of_terminal_is_terminal _ (#F tr)).

  Let Ω₀ : subobject_classifier (_,,T_D)
     := make_subobject_classifier _ _ is_cl.

  Context {x y : C} (m : Monic C x y).
  Let classifying_map_reflection : C⟦y, Ω⟧.
  Proof.
    use (fully_faithful_inv_hom (pr2 Fw)).
    exact (characteristic_morphism Ω₀ (weak_equiv_preserves_mono Fw m)).
  Defined.

  Lemma classifying_map_square
    : m · classifying_map_reflection = TerminalArrow T_C x · tr.
  Proof.
    use (faithful_reflects_morphism_equality _ (pr2 Fw)).
    do 2 rewrite functor_comp.

    set (t_m := subobject_classifier_square_commutes Ω₀ (weak_equiv_preserves_mono Fw m)).
    refine (_ @ t_m @ _).
    2: {
      apply maponpaths_2.
      use proofirrelevancecontr.
      apply image_of_terminal_is_terminal.
    }
    apply maponpaths.
    apply functor_on_fully_faithful_inv_hom.
  Qed.

  Lemma classifying_map_square_isPullback
    : isPullback classifying_map_square.
  Proof.
    use (weak_equiv_reflects_pullbacks Fw).
    intros d' g k pf.

    assert (pf₀ :  g · pr11 (is_cl (F x) (F y) (weak_equiv_preserves_mono Fw m)) = k · # F tr).
    {
      refine (_ @ pf).
      apply maponpaths.
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
    }
    assert (pf₁ : TerminalArrow image_of_terminal_is_terminal (F x) = #F (TerminalArrow T_C x)).
    {
      use proofirrelevancecontr.
      apply image_of_terminal_is_terminal.
    }
    set (t := pr221 (is_cl _ _ (weak_equiv_preserves_mono Fw m)) d' g k pf₀).
    rewrite pf₁ in t.
    exact t.
  Qed.

  Lemma weak_equiv_reflects_subobject_classifier_existence
    : ∑ (χ : C ⟦ y, Ω ⟧) (H : m · χ = TerminalArrow T_C x · tr), isPullback H.
  Proof.
    simple refine (_ ,, _ ,, _).
    - apply classifying_map_reflection.
    - apply classifying_map_square.
    - apply classifying_map_square_isPullback.
  Defined.

End WeakEquivalencesReflectSubobjectClassifiersExistence.

Section WeakEquivalencesReflectSubobjectClassifiers₀.

   Context {C D : category} (T_C : Terminal C)
     {F : C ⟶ D} (Fw : is_weak_equiv F).

   Let T_D : Terminal D
      := make_Terminal _ (weak_equiv_preserves_terminal _ Fw T_C (pr2 T_C)).

  Context {Ω : ob C} (tr : C⟦T_C, Ω⟧)
    (is_cl : is_subobject_classifier (C := D) T_D _ (#F tr)).

  Let Ω₀ : subobject_classifier T_D
      := make_subobject_classifier _ _ is_cl.

  Let pb_square'
    {x y : ob C} {m : Monic C x y}
    (ϕ : ∑ (χ : C ⟦ y, Ω ⟧) (H : m · χ = TerminalArrow T_C x · tr), isPullback H)
    : # F m · # F (pr1 ϕ) = TerminalArrow T_D (F x) · true' Ω₀
      := (functor_on_square C D F (pr12 ϕ) @
           maponpaths_2 compose (functor_on_terminal_arrow T_C (weak_equiv_preserves_terminal F Fw) x) (true' Ω₀)).

  Let pb_square
    {x y : ob C} {m : Monic C x y}
    (ϕ : ∑ (χ : C ⟦ y, Ω ⟧) (H : m · χ = TerminalArrow T_C x · tr), isPullback H)
    : # F m · # F (pr1 ϕ) = #F (TerminalArrow T_C x) · true' Ω₀.
  Proof.
    refine (pb_square' ϕ @ _).
    apply maponpaths_2.
    apply pathsinv0, functor_on_terminal_arrow.
  Qed.

  Lemma weak_equiv_reflects_subobject_classifier_uvp_reflected_pullback'
    {x y : ob C} {m : Monic C x y}
    (ϕ : ∑ (χ : C ⟦ y, Ω ⟧) (H : m · χ = TerminalArrow T_C x · tr), isPullback H)
    :   isPullback (pb_square ϕ).
  Proof.
    use (weak_equiv_preserves_pullbacks Fw).
    - exact (pr12 ϕ).
    - exact (pr22 ϕ).
  Qed.

  Lemma weak_equiv_reflects_subobject_classifier_uvp_reflected_pullback
    {x y : ob C} {m : Monic C x y}
    (ϕ : ∑ (χ : C ⟦ y, Ω ⟧) (H : m · χ = TerminalArrow T_C x · tr), isPullback H)
    : isPullback (pb_square' ϕ).
  Proof.
    use (isPullback_mor_paths _ _ _ _ _ _ (weak_equiv_reflects_subobject_classifier_uvp_reflected_pullback' ϕ)) ; try (apply idpath).
    apply functor_on_terminal_arrow.
  Qed.

  Lemma weak_equiv_reflects_subobject_classifier_uvp_uniqueness
    {x y : ob C} (m : Monics.Monic C x y)
    : isaprop (∑ (χ : C ⟦ y, Ω ⟧)
                 (H : MonicArrow C m · χ = TerminalArrow T_C x · tr),
          isPullback H
        ).
  Proof.
    use invproofirrelevance.
    intros ϕ₁ ϕ₂.
    use subtypePath.
    { intro ; use isaproptotal2.
      { intro ; apply isaprop_isPullback. }
      intro ; intros.
      use proofirrelevance.
      apply homset_property.
    }

    refine (! homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 Fw) _ _) _).
    apply maponpaths.

    use (subobject_classifier_map_eq Ω₀ (weak_equiv_preserves_mono Fw m)).
    - apply pb_square'.
    - apply pb_square'.
    - apply weak_equiv_reflects_subobject_classifier_uvp_reflected_pullback.
    - apply weak_equiv_reflects_subobject_classifier_uvp_reflected_pullback.
  Qed.

  Lemma weak_equiv_reflects_is_subobject_classifier
    : is_subobject_classifier (C := C) T_C _ tr.
  Proof.
    unfold is_subobject_classifier.
    intros x y m. (* [m₀ m₁]. *)
    use iscontraprop1.
    - apply weak_equiv_reflects_subobject_classifier_uvp_uniqueness.
    - use (weak_equiv_reflects_subobject_classifier_existence T_C Fw (pr2 T_D)).
      assumption.
  Defined.

End WeakEquivalencesReflectSubobjectClassifiers₀.
