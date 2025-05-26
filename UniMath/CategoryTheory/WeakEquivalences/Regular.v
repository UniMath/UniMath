(**
   Rezk Completion For Regular Categories

   In this file, we show: if F : C → D is a weak equivalence with C regular and D univalent, then D is regular.

   Contents.
   1. Preservation [weak_equiv_preserves_regular_epi]
   2. Reflection [weak_equiv_reflects_regular_epi]
   3. Lift Preservation [weak_equiv_lifts_preserves_regular_epi]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Coequalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.RegularEpi.

Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.

Local Open Scope cat.

Proposition weak_equiv_preserves_pullback
  {C D : category} {F : C ⟶ D} (F_weq : is_weak_equiv F)
  {z x_l x_r : C} (f_l : C⟦x_l, z⟧) (f_r : C⟦x_r, z⟧) (c : Pullback f_l f_r)
  : Pullback (#F f_l) (#F f_r).
Proof.
  use (make_Pullback _ (weak_equiv_preserves_pullbacks F_weq _ _ _ _ f_l f_r _ _ _ _ (isPullback_Pullback c))).
  abstract (do 2 rewrite <- functor_comp ; apply maponpaths ; apply PullbackSqrCommutes).
Defined.

Proposition weak_equiv_preserves_coequalizer
  {C D : category} {F : C ⟶ D} (F_weq : is_weak_equiv F)
  {x y : C} (f g : C⟦x, y⟧) (c : Coequalizer f g)
  : Coequalizer (#F f) (#F g).
Proof.
  use (make_Coequalizer _ _ _ _
         (weak_equiv_preserves_coequalizers F_weq x y c f g _ _ _ (isCoequalizer_Coequalizer c))).
  abstract (do 2 rewrite <- functor_comp ; apply maponpaths ; apply CoequalizerEqAr).
Defined.

Proposition coequalizer_stable_under_iso
  {C : category} {x x' y y' : C} (f g : C⟦x, y⟧) (f' g' : C⟦x',y'⟧)
  (i : z_iso x' x) (j : z_iso y' y) (z : Coequalizer f g)
  (p : f' · j = i · f)
  (q : g' · j = i · g)
  : Coequalizer f' g'.
Proof.

  assert (pq :  f' · (j · CoequalizerArrow z) = g' · (j · CoequalizerArrow z)). {
    rewrite assoc, p ;
      rewrite assoc', CoequalizerEqAr ;
      rewrite assoc, <- q ;
      now rewrite assoc.
  }

  use make_Coequalizer.
  - exact z.
  - exact (j · CoequalizerArrow z).
  - exact pq.
  - intros w h pf.
    use (iscontrweqb' (isCoequalizer_Coequalizer z w (inv_from_z_iso j · h) _)).
    + do 2 rewrite assoc.
      use (cancel_z_iso' i).
      rewrite ! assoc.
      rewrite <- p, <- q.
      etrans. {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths, z_iso_inv_after_z_iso.
      }
      etrans.
      2: {
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths, pathsinv0, z_iso_inv_after_z_iso.
      }
      do 2 rewrite id_right.
      exact pf.
    + use weqfibtototal.
      intro k.
      simpl.
      use weqimplimpl.
      * intro pf'.
        apply pathsinv0, z_iso_inv_on_right.
        exact (! pf' @ assoc' _ _ _).
      * intro pf'.
        rewrite assoc'.
        apply pathsinv0.
        use z_iso_inv_to_left.
        exact (! pf').
      * apply homset_property.
      * apply homset_property.
Defined.

Proposition pullbacks_of_isos_to_iso'
  {C : category} {x x' y y' z z' : C}
  {f : C⟦x, z⟧} {g : C⟦y, z⟧}
  {f' : C⟦x', z'⟧} {g' : C⟦y', z'⟧}
  (p : Pullback f g) (q : Pullback f' g')
  (i : z_iso x x') (j : z_iso y y') (k : z_iso z z')
  (pf : i · f' = f · k)
  (pf' : j · g' = g · k)
  : C⟦p, q⟧.
Proof.
  use PullbackArrow.
  - exact (PullbackPr1 p · i).
  - exact (PullbackPr2 p · j).
  - abstract (rewrite assoc', pf;
              rewrite assoc', pf';
              do 2 rewrite assoc;
              now rewrite PullbackSqrCommutes).
Defined.

Proposition pullbacks_of_isos_to_iso
  {C : category} {x x' y y' z z' : C}
  {f : C⟦x, z⟧} {g : C⟦y, z⟧}
  {f' : C⟦x', z'⟧} {g' : C⟦y', z'⟧}
  (p : Pullback f g) (q : Pullback f' g')
  (i : z_iso x x') (j : z_iso y y') (k : z_iso z z')
  (pf : i · f' = f · k)
  (pf' : j · g' = g · k)
  : z_iso p q.
Proof.
  simple refine (_ ,, _ ,, (_ ,, _)).
  - exact (pullbacks_of_isos_to_iso' p q i j k pf pf').
  - apply (pullbacks_of_isos_to_iso' q p (z_iso_inv i) (z_iso_inv j) (z_iso_inv k)).
    + abstract (use z_iso_inv_on_right;
      rewrite assoc, pf;
      rewrite assoc';
      rewrite z_iso_inv_after_z_iso;
      now rewrite id_right).
    + abstract (use z_iso_inv_on_right;
      rewrite assoc, pf';
      rewrite assoc';
      rewrite z_iso_inv_after_z_iso;
      now rewrite id_right).
  - unfold pullbacks_of_isos_to_iso'.
    rewrite postCompWithPullbackArrow.
    apply pathsinv0, PullbackArrowUnique'.
    + rewrite id_left, assoc.
      rewrite PullbackArrow_PullbackPr1.
      rewrite assoc', z_iso_inv_after_z_iso.
      now rewrite id_right.
    + rewrite id_left, assoc.
      rewrite PullbackArrow_PullbackPr2.
      rewrite assoc', z_iso_inv_after_z_iso.
      now rewrite id_right.
  - cbn.
    unfold pullbacks_of_isos_to_iso'.
    rewrite postCompWithPullbackArrow.
    apply pathsinv0, PullbackArrowUnique'.
    + rewrite id_left, assoc.
      rewrite PullbackArrow_PullbackPr1.
      rewrite assoc', z_iso_inv_after_z_iso.
      now rewrite id_right.
    + rewrite id_left, assoc.
      rewrite PullbackArrow_PullbackPr2.
      rewrite assoc', z_iso_inv_after_z_iso.
      now rewrite id_right.
Defined.

Section CoequalizersOfKernelPairs.

  Context {C₀ C₁ : category} {F : functor C₀ C₁}
    (F_weq : is_weak_equiv F) (C₁_univ : is_univalent C₁)
    (P₀ : Pullbacks C₀) (C : coeqs_of_kernel_pair C₀).

  Definition Rezk_completion_has_coeqs_of_kernel_pair
    : coeqs_of_kernel_pair C₁.
  Proof.
    intros x₁ y₁ f₁ f₁₁.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq x₁)).
    { intro ; apply isaprop_Coequalizer, C₁_univ. }
    intros [x₀ i_x].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq y₁)).
    { intro ; apply isaprop_Coequalizer, C₁_univ. }
    intros [y₀ i_y].

    set (f₀ := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ (i_x · f₁ · inv_from_z_iso i_y)).
    set (coe := C x₀ y₀ f₀ (P₀ _ _ _ f₀ f₀)).
    set (F_coe := weak_equiv_preserves_coequalizer F_weq _ _ coe).

    set (F_pb := weak_equiv_preserves_pullback F_weq _ _ (P₀ _ _ _ f₀ f₀)).

    use (coequalizer_stable_under_iso _ _ _ _ _ _ F_coe).
    - use (pullbacks_of_isos_to_iso f₁₁ F_pb).
      + exact (z_iso_inv i_x).
      + exact (z_iso_inv i_x).
      + exact (z_iso_inv i_y).
      + abstract (unfold f₀;
        rewrite functor_on_fully_faithful_inv_hom;
        rewrite assoc;
        apply maponpaths_2;
        rewrite assoc;
        refine (_ @ id_left _);
        apply maponpaths_2;
        apply z_iso_after_z_iso_inv).
      + abstract (unfold f₀;
        rewrite functor_on_fully_faithful_inv_hom;
        rewrite assoc;
        apply maponpaths_2;
        rewrite assoc;
        refine (_ @ id_left _);
        apply maponpaths_2;
        apply z_iso_after_z_iso_inv).
    - exact (z_iso_inv i_x).
    - apply pathsinv0, (PullbackArrow_PullbackPr1 F_pb).
    - apply pathsinv0, (PullbackArrow_PullbackPr2 F_pb).
  Defined.

End CoequalizersOfKernelPairs.

Section RegularEpiPullbackStability.

  Context {C₀ C₁ : category} {F : functor C₀ C₁} (F_weq : is_weak_equiv F) (C₁_univ : is_univalent C₁)
    (T₀ : Terminal C₀) (P₀ : Pullbacks C₀) (C : regular_epi_pb_stable C₀).

  Definition Rezk_completion_regular_epi_pb_stable
    : regular_epi_pb_stable C₁.
  Proof.
    unfold regular_epi_pb_stable in *.
    intros pb x y z f g π₁ π₂ p pp re.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq pb)).
    { apply isaprop_is_regular_epi. }
    intros [pb₀ i_pb].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq x)).
    { apply isaprop_is_regular_epi. }
    intros [x₀ i_x].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq y)).
    { apply isaprop_is_regular_epi. }
    intros [y₀ i_y].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq z)).
    { apply isaprop_is_regular_epi. }
    intros [z₀ i_z].

    set (p_pb := isotoid _ C₁_univ i_pb).
    set (p_x := isotoid _ C₁_univ i_x).
    set (p_y := isotoid _ C₁_univ i_y).
    set (p_z := isotoid _ C₁_univ i_z).

    induction p_pb, p_x, p_y, p_z.

    set (f₀ := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ f).
    set (g₀ := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ g).
    set (π₁₀ := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ π₁).
    set (π₂₀ := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ π₂).

    assert (pf : π₂ = #F π₂₀). {
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
    }
    apply (transportf is_regular_epi (! pf)).
    apply (weak_equiv_preserves_regular_epi F_weq).

    assert (p₀ : π₁₀ · f₀ = π₂₀ · g₀). {
      use (faithful_reflects_morphism_equality _ (pr2 F_weq));
        do 2 rewrite functor_comp;
        unfold π₁₀, f₀, π₂₀, g₀;
        do 4 rewrite functor_on_fully_faithful_inv_hom;
        exact p.
    }

    use (C pb₀ x₀ y₀ z₀ f₀ g₀ π₁₀ π₂₀ p₀).
    - use (weak_equiv_reflects_pullbacks F_weq).
      use (isPullback_mor_paths _ _ _ _ _ _ pp)
      ; apply pathsinv0, functor_on_fully_faithful_inv_hom.
    - use (weak_equiv_reflects_regular_epi F_weq).
      use (transportf is_regular_epi _ re).
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
  Qed.

End RegularEpiPullbackStability.

Definition Rezk_completion_is_regular
  {C₀ C₁ : category} {F : functor C₀ C₁} (F_weq : is_weak_equiv F) (C₁_univ : is_univalent C₁)
  (R₀ : is_regular_category C₀)
  : is_regular_category C₁.
Proof.
  induction R₀ as [T₀ [P₀ [A₀ B₀]]].
  repeat split.
  - exact (weak_equiv_creates_terminal F_weq T₀).
  - exact (weak_equiv_into_univ_creates_pullbacks C₁_univ F_weq P₀).
  - exact (Rezk_completion_has_coeqs_of_kernel_pair F_weq C₁_univ P₀ A₀).
  - exact (Rezk_completion_regular_epi_pb_stable F_weq C₁_univ B₀).
Defined.
