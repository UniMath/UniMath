(**
   In this file, we show that an arbitrary weak equivalence F : C -> D preserves subobject classifiers.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Mono.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.

Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.

Local Open Scope cat.

Section WeakEquivalencePreservationsSubobjectClassifier.

  Context {C D : category}
    {F : C ⟶ D}
    (Fw : is_weak_equiv F)
    {t_C : Terminal C}
    (t_D : Terminal D)
    (Ω : subobject_classifier t_C).

  Let t_F : preserves_terminal F.
  Proof.
    apply weak_equiv_preserves_terminal.
    exact Fw.
  Defined.

  Context {d₁ d₂ : D}
    {c₁ c₂ : C}
    (i₁ : z_iso (F c₁) d₁)
    (i₂ : z_iso (F c₂) d₂).

  Context (f : Monic D d₁ d₂).
  Let refl_f := reflection_of_mono (pr2 Fw) i₁ i₂ f.
  Let const_tr₂ := TerminalArrow t_D d₁ · (TerminalArrow (preserves_terminal_to_terminal F t_F t_C) t_D · # F (pr12 Ω)).

  Lemma square_of_reflection_subobject_classifier'
    (φ : ∑ (χ : D⟦d₂, F Ω⟧), ∑ (H : MonicArrow D f · χ = const_tr₂), isPullback H)
    : i₁ · const_tr₂ = # F (const_true c₁ Ω).
  Proof.
    unfold const_tr₂.
    rewrite ! assoc.

    etrans. {
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply TerminalArrowUnique.
    }

    assert (r₀ : TerminalArrow (preserves_terminal_to_terminal F t_F t_C) d₁
                 = z_iso_inv i₁ · #F (TerminalArrow _ _)).
    { apply pathsinv0, TerminalArrowUnique. }
    rewrite r₀.

    etrans. {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      now rewrite <- functor_comp.
    }
    rewrite assoc.
    rewrite z_iso_inv_after_z_iso.
    now rewrite id_left.
  Qed.

  Lemma square_of_reflection_subobject_classifier
    (φ : ∑ (χ : D⟦d₂, F Ω⟧), ∑ (H : MonicArrow D f · χ = const_tr₂), isPullback H)
    : refl_f · invmap (weq_from_fully_faithful (ff_from_weak_equiv F Fw) c₂ Ω) (i₂ · pr1 φ)
      = const_true c₁ Ω.
  Proof.
    apply (faithful_reflects_morphism_equality F (pr2 Fw)).
    etrans. {
      apply maponpaths, pathsinv0, fully_faithful_inv_comp.
    }
    etrans. {
      do 2 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_right.
    refine (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).

    (* i₁ · f · pr1 φ = # F (const_true c₁ Ω). *)
    etrans. {
      rewrite assoc'.
      apply maponpaths.
      exact (pr12 φ).
    }
    exact (square_of_reflection_subobject_classifier' φ).
  Qed.

  Definition ClassifyingPullbackOfImage {x₁ x₂ : ob C} (g : Monic _ x₁ x₂)
    : Pullback (# F (characteristic_morphism Ω g)) (# F (Monics.MonicArrow C Ω)).
  Proof.
    set (pb := (subobject_classifier_pullback Ω g)).
    use (make_Pullback _ (weak_equiv_preserves_pullbacks Fw _ _ _ _ _ _ _ _ _ _
                            (isPullback_Pullback pb))).
    apply functor_on_square, pb.
  Defined.

  Lemma pullback_square_of_reflection'
    (ϕ : ∑ (χ : D⟦d₂, F Ω⟧), ∑ (H : MonicArrow D f · χ = const_tr₂), isPullback H)
    : isPullback (Pullbacks.p_func (F := F) (square_of_reflection_subobject_classifier ϕ)).
  Proof.
    intros d' g k pfₛ.

    assert (spf : g · i₂ · pr1 ϕ =
       k · TerminalArrow t_D (F t_C)
         · (TerminalArrow (preserves_terminal_to_terminal F t_F t_C) t_D · # F (pr12 Ω))).
    {
      refine (_ @ pfₛ @ _).
      - rewrite ! assoc'.
        apply maponpaths.
        apply pathsinv0.
        apply (functor_on_fully_faithful_inv_hom _ (pr2 Fw)).
      - rewrite ! assoc'.
        apply maponpaths.
        refine (! id_left _ @ _).
        rewrite ! assoc.
        apply maponpaths_2.
        use proofirrelevancecontr.
        apply t_F, t_C.
    }

    set (R := pr22 ϕ d' _ _ spf).
    use (iscontrweqb' R).

    use weqtotal2.
    - use z_iso_comp_left_weq.
      exact i₁.
    - intro.
      use weqdirprodf ; simpl.
      + use weqimplimpl.
        * intro pq.
          use (cancel_z_iso _ _ (z_iso_inv i₂)).
          apply pathsinv0.
          etrans. {
            do 2 apply maponpaths_2.
            exact (! pq).
          }
          rewrite ! assoc'.
          apply maponpaths.
          rewrite z_iso_inv_after_z_iso.
          rewrite id_right.
          apply (functor_on_fully_faithful_inv_hom _ (pr2 Fw)).
          (* apply assoc'. *)
        * intro pq.
          etrans. {
            apply maponpaths.
            apply (functor_on_fully_faithful_inv_hom _ (pr2 Fw)).
          }
          rewrite ! assoc.
          rewrite pq.
          rewrite !assoc'.
          rewrite z_iso_inv_after_z_iso.
          apply id_right.
        * apply homset_property.
        * apply homset_property.
      + use weqcontrcontr ; apply isapropifcontr.
        * apply t_F, t_C.
        * apply t_D.
  Qed.

  Lemma pullback_square_of_reflection
    (ϕ : ∑ (χ : D⟦d₂, F Ω⟧), ∑ (H : MonicArrow D f · χ = const_tr₂), isPullback H)
    : isPullback (square_of_reflection_subobject_classifier ϕ).
  Proof.
    use (weak_equiv_reflects_pullbacks Fw).
    apply pullback_square_of_reflection'.
  Qed.

  Lemma weak_equiv_preserves_subobject_classifier_type_isaprop
    : isaprop (∑ (χ : D⟦d₂, F Ω⟧), ∑ (H : MonicArrow D f · χ = const_tr₂), isPullback H).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    simpl.
    use subtypePath.
    { intro ; apply isaprop_is_subobject_classifier_arr. }
    use (cancel_z_iso' i₂).

    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ Fw) _ _) _).
    apply maponpaths.

    set (χ₁ := invmap (weq_from_fully_faithful (ff_from_weak_equiv F Fw) c₂ Ω) (i₂ · pr1 φ₁)
                 : C⟦c₂, Ω⟧).
    set (χ₂ := invmap (weq_from_fully_faithful (ff_from_weak_equiv F Fw) c₂ Ω) (i₂ · pr1 φ₂)
           : C⟦c₂, Ω⟧).

    use (subobject_classifier_map_eq Ω (reflection_of_mono (pr2 Fw) i₁ i₂ f)).
    - apply square_of_reflection_subobject_classifier.
    - apply square_of_reflection_subobject_classifier.
    - apply pullback_square_of_reflection.
    - apply pullback_square_of_reflection.
  Qed.

  Lemma weak_equiv_preserves_subobject_classifier_square
    : f · (z_iso_inv i₂ · # F (characteristic_morphism Ω refl_f)) = const_tr₂.
  Proof.
    set (t := maponpaths (#F) (subobject_classifier_square_commutes Ω refl_f)).
    rewrite functor_comp in t.

    assert (pf : i₁ · pr1 f · z_iso_inv i₂ = #F refl_f).
    {
      apply pathsinv0, (functor_on_fully_faithful_inv_hom _ (pr2 Fw)).
    }

    use (cancel_z_iso' i₁).
    refine ( _ @ t @ _).
    - rewrite <- pf.
      now rewrite ! assoc'.
    - cbn.
      rewrite functor_comp.
      unfold const_tr₂.
      rewrite ! assoc.
      apply maponpaths_2.
      use proofirrelevancecontr.
      apply t_F, t_C.
  Qed.

  Lemma weak_equiv_preserves_subobject_classifier_square_is_a_pullback
    : isPullback weak_equiv_preserves_subobject_classifier_square.
  Proof.
    intros d g t pf.

    transparent assert (tfc : (D⟦d, F t_C⟧)). {
      apply t_F, t_C.
    }

    simpl in tfc.
    rewrite assoc in pf.
    assert (pf₀ : g · z_iso_inv i₂ · # F (characteristic_morphism Ω refl_f) = tfc · # F Ω).
    {
      refine (assoc' _ _ _ @ _ @ pf @ _).
      { apply assoc. }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      use proofirrelevancecontr.
      apply t_F, t_C.
    }

    use (iscontrweqf (X := ∑ hk : D ⟦ d, ClassifyingPullbackOfImage refl_f⟧,
       hk · PullbackPr1 (ClassifyingPullbackOfImage refl_f) = g · z_iso_inv i₂
                                                       × hk · PullbackPr2 (ClassifyingPullbackOfImage refl_f) = tfc)).
    2: {
      exact (isPullback_Pullback (ClassifyingPullbackOfImage refl_f) d (g · z_iso_inv i₂) tfc pf₀).
    }

    unfold ClassifyingPullbackOfImage.
    cbn.
    use weqtotal2.
    - use z_iso_comp_left_weq.
      exact i₁.
    - intro.
      use weqdirprodf ; simpl.
      + use weqimplimpl.
        * intro pq.
          use (cancel_z_iso _ _ (z_iso_inv i₂)).
          refine (_ @ pq).
          rewrite ! assoc'.
          apply maponpaths.
          apply pathsinv0, (functor_on_fully_faithful_inv_hom _ (pr2 Fw)).
        * intro pq.
          etrans. {
            apply maponpaths.
            apply (functor_on_fully_faithful_inv_hom _ (pr2 Fw)).
          }
          rewrite ! assoc.
          apply maponpaths_2.
          exact pq.
        * apply homset_property.
        * apply homset_property.
      + use weqcontrcontr ; apply isapropifcontr.
        * apply t_F, t_C.
        * apply t_D.
  Qed.

  Corollary weak_equiv_preserves_subobject_classifier_uvp
    : iscontr (∑ (χ : D⟦d₂, F Ω⟧), ∑ (H : MonicArrow D f · χ = const_tr₂), isPullback H).
  Proof.
    use iscontraprop1.
    { exact weak_equiv_preserves_subobject_classifier_type_isaprop. }
    simple refine (_ ,, _ ,, _).
    - exact (z_iso_inv i₂ · #F (characteristic_morphism Ω refl_f)).
    - apply weak_equiv_preserves_subobject_classifier_square.
    - apply weak_equiv_preserves_subobject_classifier_square_is_a_pullback.
  Qed.

  Corollary weak_equiv_preserves_subobject_classifier_uvp'
    :  ∃! (χ : D ⟦ d₂, F Ω ⟧)
         (H : f · χ = TerminalArrow t_D d₁ · (TerminalArrow (preserves_terminal_to_terminal F t_F t_C) t_D · # F (true Ω))),
      isPullback H.
  Proof.
    apply weak_equiv_preserves_subobject_classifier_uvp.
  Qed.

End WeakEquivalencePreservationsSubobjectClassifier.

Proposition weak_equiv_preserves_subobject_classifier
  {C D : category} {F : C ⟶ D} (Fw : is_weak_equiv F)
  (t_C : Terminal C) (t_D : Terminal D)
  : preserves_subobject_classifier F t_C t_D (weak_equiv_preserves_terminal _ Fw).
Proof.
  intros Ω τ τ_cl.
  set (S := make_subobject_classifier Ω τ τ_cl).
  intros d₁ d₂ f.

  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw d₁)).
  intros [c₁ i₁].
  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ Fw d₂)).
  intros [c₂ i₂].

  exact (weak_equiv_preserves_subobject_classifier_uvp Fw t_D  S i₁ i₂ f).
Qed.

Corollary weak_equiv_creates_subobject_classifier'
  {C1 C2 : category}
  {F : C1 ⟶ C2}
  (Fw : is_weak_equiv F)
  (T1 : Terminal C1)
  (T2 : Terminal C2)
  (P1 : subobject_classifier T1)
  : subobject_classifier T2.
Proof.
  set (P_2 := weak_equiv_preserves_subobject_classifier Fw T1 T2 P1 (pr12 P1) (pr22 P1)).
  exact (make_subobject_classifier _ _ P_2).
Defined.

Corollary weak_equiv_creates_subobject_classifier
  {C1 C2 : category}
  {F : C1 ⟶ C2}
  (Fw : is_weak_equiv F)
  (T1 : Terminal C1)
  (P1 : subobject_classifier T1)
  : subobject_classifier (make_Terminal _ (weak_equiv_preserves_terminal _ Fw _ (pr2 T1))).
Proof.
  exact (weak_equiv_creates_subobject_classifier' Fw T1 _ P1).
Defined.
