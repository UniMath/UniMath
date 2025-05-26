(**
   Rezk Completion For Exact Categories

   Let F : C → D be a weak equivalence.
   In this file, we show that if C is exact and D univalent, then D is exact.

   Contents.
   1. Reflection Of Equivalence Relations [weak_equiv_reflect_eqrel]
   2. Preservation Of Effectivity [weak_equiv_effective_internal_eqrel]
   3. Preservation Of Exactness [weak_equiv_preserves_is_exact]
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
Require Import UniMath.CategoryTheory.RegularAndExact.ExactCategory.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Coequalizers.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.RegularEpi.
Require Import UniMath.CategoryTheory.WeakEquivalences.Regular.

Local Open Scope cat.

Definition internal_relation_op
  {C : category} {x : C} (R : internal_relation x)
  : internal_relation x.
Proof.
  use make_internal_relation.
  - exact R.
  - exact (internal_relation_tar R).
  - exact (internal_relation_src R).
  - intros w f g p q.
    exact (internal_relation_monic R q p).
Defined.

Definition internal_eqrel_op
  {C : category} {x : C} (R : internal_eqrel x)
  : internal_eqrel x.
Proof.
  use (make_internal_eqrel _ (internal_relation_op R)).
  repeat split ; intro w.
  - intro f.
    set (t := isrefl_internal_eqrel R w f).
    exact (pr1 t ,, pr22 t ,, pr12 t).
  - intros f g [r [p q]].
    set (t := issymm_internal_eqrel R w g f (r ,, (q ,, p))).
    exact (pr1 t ,, pr22 t ,, pr12 t).
  - intros f g h [r [p q]] [r' [p' q']].
    set (t := istrans_internal_eqrel R w h g f (r' ,, (q' ,, p')) (r ,, (q ,, p))).
    exact (pr1 t ,, pr22 t ,, pr12 t).
Defined.

(** * 1. Reflection Of Equivalence Relations *)
Section ReflectionOfRelations.

  Context {C₀ C₁ : category} {F : functor C₀ C₁}
    (F_weq : fully_faithful F).

  Context {x₀ R₀ : C₀} {x₁ : C₁} (i_x : z_iso (F x₀) x₁).

  Definition weak_equiv_reflect_rel_src
    (R₁ : internal_relation x₁)
    (i_R : z_iso (F R₀) R₁)
      := fully_faithful_inv_hom F_weq _ _ (i_R · internal_relation_src R₁ · inv_from_z_iso i_x).

  Definition weak_equiv_reflect_rel_tgt
    (R₁ : internal_relation x₁)
    (i_R : z_iso (F R₀) R₁)
    := fully_faithful_inv_hom F_weq _ _ (i_R · internal_relation_tar R₁ · inv_from_z_iso i_x).

  Lemma weak_equiv_preserves_rel_mono_src
    (R₁ : internal_relation x₁)
    (i_R : z_iso (F R₀) R₁)
    {w : C₀}
    {f g : C₀⟦w, R₀⟧}
    (pf_s : f · weak_equiv_reflect_rel_src R₁ i_R = g · weak_equiv_reflect_rel_src R₁ i_R)
    : # F f · i_R · internal_relation_src R₁ = # F g · i_R · internal_relation_src R₁.
  Proof.
    use (cancel_z_iso _ _ (z_iso_inv i_x)).
    set (s := maponpaths #F pf_s).
    do 2 rewrite functor_comp in s.
    unfold weak_equiv_reflect_rel_src in s.
    rewrite functor_on_fully_faithful_inv_hom in s.
    do 4 rewrite assoc in s.
    exact s.
  Qed.

  Definition weak_equiv_reflect_rel
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    : internal_relation x₀.
  Proof.
    use (make_internal_relation x₀ R₀ (weak_equiv_reflect_rel_src R₁ i_R) (weak_equiv_reflect_rel_tgt R₁ i_R)).
    intros w f g pf_s pf_t.
    use (faithful_reflects_morphism_equality _ F_weq).
    use (cancel_z_iso _ _ i_R).
    use (internal_relation_monic R₁).
    - exact (weak_equiv_preserves_rel_mono_src _ _ pf_s).
    - exact (weak_equiv_preserves_rel_mono_src (internal_relation_op R₁) _ pf_t).
  Defined.

  Lemma weak_equiv_reflect_src_comm
    {w : C₀}
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    (h' : C₀⟦w, x₀⟧)
    {s₀ : C₁ ⟦ F w, R₁ ⟧}
    (p₀ : s₀ · internal_relation_src R₁ = # F h' · i_x)
    : fully_faithful_inv_hom F_weq w R₀ (s₀ · z_iso_inv i_R)
        · internal_relation_src (weak_equiv_reflect_rel R₁ i_R) = h'.
  Proof.
    use (faithful_reflects_morphism_equality _ F_weq).
    rewrite functor_comp.
    rewrite functor_on_fully_faithful_inv_hom.
    etrans. { apply maponpaths, functor_on_fully_faithful_inv_hom. }
    use (cancel_z_iso _ _ i_x).
    refine (_ @ p₀).
    rewrite ! assoc'.
    rewrite z_iso_after_z_iso_inv.
    rewrite id_right.
    apply maponpaths.
    rewrite assoc.
    simpl ; rewrite z_iso_after_z_iso_inv.
    apply id_left.
  Qed.

  Lemma weak_equiv_reflect_rel_refl_com
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    (w : C₀)
    (h : C₀⟦w, x₀⟧)
    : fully_faithful_inv_hom F_weq w (weak_equiv_reflect_rel R₁ i_R)
        (pr1 (isrefl_internal_eqrel R₁ (F w) (#F h · i_x)) · inv_from_z_iso i_R)
        · internal_relation_src (weak_equiv_reflect_rel R₁ i_R)
      = h.
  Proof.
    apply weak_equiv_reflect_src_comm.
    exact (pr12 (isrefl_internal_eqrel R₁ (F w) (#F h · i_x))).
  Qed.

  Lemma weak_equiv_reflect_isrefl
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    (w : C₀)
    : isrefl (internal_relation_to_arr_hrel (weak_equiv_reflect_rel R₁ i_R) w).
  Proof.
    intro h.
    set (h_refl := isrefl_internal_eqrel R₁ (F w) (#F h · i_x)).
    simple refine (_ ,, _ ,, _).
    - use (fully_faithful_inv_hom F_weq).
      exact (pr1 h_refl · inv_from_z_iso i_R).
    - apply weak_equiv_reflect_rel_refl_com.
    - exact (weak_equiv_reflect_rel_refl_com (internal_eqrel_op R₁) i_R w h).
  Defined.

  Lemma weak_equiv_preserves_arr_rel_src
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    {w : C₀}
    (h h' : C₀⟦w, x₀⟧)
    (r : internal_relation_to_arr_hrel (weak_equiv_reflect_rel R₁ i_R) w h h')
    : (#F (pr1 r) · i_R) · internal_relation_src R₁ = # F h · i_x.
  Proof.
    rewrite <- (maponpaths #F (pr12 r)).
    rewrite functor_comp.
    do 2 rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { apply maponpaths_2, pathsinv0, functor_on_fully_faithful_inv_hom. }
    rewrite assoc', z_iso_after_z_iso_inv.
    now rewrite id_right.
  Qed.

  Definition weak_equiv_preserves_arr_rel
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    {w : C₀}
    (h h' : C₀⟦w, x₀⟧)
    (r : internal_relation_to_arr_hrel (weak_equiv_reflect_rel R₁ i_R) w h h')
    : internal_relation_to_arr_relation R₁ (# F h · i_x) (# F h' · i_x).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact (#F (pr1 r) · i_R).
    - apply weak_equiv_preserves_arr_rel_src.
    - exact (weak_equiv_preserves_arr_rel_src (internal_eqrel_op R₁) i_R _ _ (pr1 r ,, (pr22 r ,, pr12 r))).
  Defined.

  Lemma weak_equiv_reflect_issym (w : C₀)
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    : issymm (internal_relation_to_arr_hrel (weak_equiv_reflect_rel R₁ i_R) w).
  Proof.
    intros h h' r.
    set (pf := weak_equiv_preserves_arr_rel R₁ i_R h h' r).
    set (σ := issymm_internal_eqrel R₁ (F w) (#F h · i_x) (#F h' · i_x) pf).
    induction σ as [s₀ [p₀ q₀]].
    simple refine (_ ,, _ ,, _).
    - exact (fully_faithful_inv_hom F_weq _ _ (s₀ · z_iso_inv i_R)).
    - exact (weak_equiv_reflect_src_comm R₁ i_R _ p₀).
    - exact (weak_equiv_reflect_src_comm (internal_eqrel_op R₁) i_R _ q₀).
  Defined.

  Lemma weak_equiv_reflect_istrans (w : C₀)
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    : istrans (internal_relation_to_arr_hrel (weak_equiv_reflect_rel R₁ i_R) w).
  Proof.
    intros h h' h'' r r'.
    set (pf := weak_equiv_preserves_arr_rel R₁ i_R h h' r).
    set (pf' := weak_equiv_preserves_arr_rel R₁ i_R h' h'' r').
    set (σ := istrans_internal_eqrel R₁ (F w) (#F h · i_x) (#F h' · i_x) (#F h'' · i_x) pf pf').
    induction σ as [s₀ [p₀ q₀]].
    simple refine (_ ,, _ ,, _).
    - exact (fully_faithful_inv_hom F_weq _ _ (s₀ · z_iso_inv i_R)).
    - exact (weak_equiv_reflect_src_comm R₁ i_R _ p₀).
    - exact (weak_equiv_reflect_src_comm (internal_eqrel_op R₁) i_R _ q₀).
  Defined.

  Definition weak_equiv_reflect_eqrel
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    : internal_eqrel x₀.
  Proof.
    apply (make_internal_eqrel _ (weak_equiv_reflect_rel R₁ i_R)).
    repeat split; intro w.
    - apply weak_equiv_reflect_isrefl.
    - apply weak_equiv_reflect_issym.
    - apply weak_equiv_reflect_istrans.
  Defined.

  Lemma weak_equiv_preserves_eqrel_source
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀) R₁)
    : internal_relation_src R₁ · z_iso_inv i_x
      = z_iso_inv i_R · # F (internal_relation_src (weak_equiv_reflect_rel R₁ i_R)).
  Proof.
    etrans.
    2: { apply maponpaths, pathsinv0, functor_on_fully_faithful_inv_hom. }
    rewrite assoc.
    apply maponpaths_2.
    rewrite assoc.
    simpl ; rewrite z_iso_after_z_iso_inv.
    now rewrite id_left.
  Qed.

End ReflectionOfRelations.

(** * 2. Preservation Of Effectivity *)
Section PreservationOfEffectivity.

  Context {C₀ C₁ : category} {F : functor C₀ C₁}
    (F_weq : is_weak_equiv F) (C₁_univ : is_univalent C₁)
    (P₀ : Pullbacks C₀) (E₀ : all_internal_eqrel_effective C₀).

  Context {x₀ : C₀} {x₁ : C₁}
    (i_x : z_iso (F x₀) x₁)
    {R₀₀ : C₀}
    (R₁ : internal_eqrel x₁)
    (i_R : z_iso (F R₀₀) R₁).

  Let R₀ := weak_equiv_reflect_eqrel (pr2 F_weq) i_x R₁ i_R.
  Let oR₀ := weak_equiv_reflect_eqrel (pr2 F_weq) i_x (internal_eqrel_op R₁) i_R.

  Let R₀_eff := E₀ x₀ R₀.
  Let coE := weak_equiv_preserves_coequalizer F_weq _ _ (pr1 R₀_eff).

  Let pB_pf
      : # F (internal_relation_src R₀) · # F (CoequalizerArrow (pr1 R₀_eff))
        = # F (internal_relation_tar R₀) · # F (CoequalizerArrow (pr1 R₀_eff)).
  Proof.
    do 2 rewrite <- functor_comp.
    apply maponpaths.
    exact (CoequalizerEqAr (pr1 R₀_eff)).
    Qed.
  Let pB := weak_equiv_preserves_pullbacks F_weq _ _ _ _ _ _ _ _ _ pB_pf (pr2 R₀_eff).

  Lemma weak_equiv_preserves_effectivity_coeq
    : Coequalizer (internal_relation_src R₁) (internal_relation_tar R₁).
  Proof.
    use (coequalizer_stable_under_iso _ _ _ _ _ _ coE).
      - exact (z_iso_inv i_R).
      - exact (z_iso_inv i_x).
      - apply weak_equiv_preserves_eqrel_source.
      - apply (weak_equiv_preserves_eqrel_source _ _ (internal_eqrel_op R₁)).
  Defined.

  Lemma weak_equiv_preserves_effectivity_pb
    : isPullback (CoequalizerEqAr weak_equiv_preserves_effectivity_coeq).
  Proof.
    use (Pullback_iso_squares _ pB).
    - exact (z_iso_inv i_x).
    - exact (z_iso_inv i_x).
    - apply identity_z_iso.
    - exact (z_iso_inv i_R).
    - apply pathsinv0, id_right.
    - apply pathsinv0, id_right.
    - apply pathsinv0, weak_equiv_preserves_eqrel_source.
    - apply (weak_equiv_preserves_eqrel_source _ _ (internal_eqrel_op R₁)).
  Qed.

  Lemma weak_equiv_preserves_effectivity
    : is_effective R₁.
  Proof.
    exists weak_equiv_preserves_effectivity_coeq.
    exact weak_equiv_preserves_effectivity_pb.
  Defined.

End PreservationOfEffectivity.

Definition weak_equiv_effective_internal_eqrel
  {C₀ C₁ : category} {F : functor C₀ C₁}
  (F_weq : is_weak_equiv F) (C₁_univ : is_univalent C₁)
  (P₀ : Pullbacks C₀) (E₀ : all_internal_eqrel_effective C₀)
  : all_internal_eqrel_effective C₁.
Proof.
  intros x₁ R₁.

  use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq x₁)).
  { apply (isaprop_is_effective (C := C₁ ,, C₁_univ)). }
  intros [x₀ i_x].

  use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq R₁)).
  { apply (isaprop_is_effective (C := C₁ ,, C₁_univ)). }
  intros [R₀ i_R].

  exact (weak_equiv_preserves_effectivity F_weq E₀ i_x R₁ i_R).
Defined.

(** * 3. Preservation Of Exactness *)
Definition weak_equiv_preserves_is_exact
  {C₀ C₁ : category} {F : functor C₀ C₁}
  (F_weq : is_weak_equiv F) (C₁_univ : is_univalent C₁)
  (E₀ : is_exact C₀)
  : is_exact C₁.
Proof.
  set (R₀ := is_exact_to_is_regular E₀).
  set (P₀ := is_regular_category_pullbacks R₀).
  set (T₀ := is_regular_category_terminal R₀).

  use tpair.
  - exact (Rezk_completion_is_regular F_weq C₁_univ (pr1 E₀)).
  - exact (weak_equiv_effective_internal_eqrel F_weq C₁_univ P₀ (pr2 E₀)).
Defined.
