(**
   Preservation Of Exponentials Is Transported Along Weak Equivalences

  The universal property of the Rezk completion states that for every functor F : C₁ → C₂, with C₂ univalent, extends along the (unit of the) Rezk completion to a functor F' : RC(C₁) → C₂.
  In this file, we prove that if F preserves exponentials, then so does F'.

  1. Preservation Of Exponentials Transports Along Weak Equivalences [weak_equiv_lifts_preserves_exponentials']
 *)

Require Import UniMath.Foundations.All.

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.Exponentials.

Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.BinProducts.

Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Exponentials.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Exponentials.

Local Open Scope cat.

Section Prelim.

  Context {C D : category} {F G : functor C D}
    (F_pP : preserves_binproduct F)
    (G_pP : preserves_binproduct G)
    (α : nat_trans F G).

  Lemma nat_trans_commute_with_binproduct_preservation
    {x y : C}
    (p : BinProduct _ x y)
    (q₁ : BinProduct _ (F x) (F y))
    (q₂ : BinProduct _ (G x) (G y))
    : BinProductOfArrows _ q₂ q₁ (α x) (α y) · z_iso_inv (preserves_binproduct_to_z_iso _ G_pP p _)
      = z_iso_inv (preserves_binproduct_to_z_iso _ F_pP _ _) · α p.
  Proof.
    refine (precompWithBinProductArrow _  (preserves_binproduct_to_binproduct G G_pP p) _ _ _ @ _).
    rewrite BinProductOfArrowsPr1.
    rewrite BinProductOfArrowsPr2.
    apply pathsinv0.
    apply (z_iso_inv_on_right _ _ _ (preserves_binproduct_to_z_iso _ F_pP p q₁)).
    apply pathsinv0.
    refine (precompWithBinProductArrow _  (preserves_binproduct_to_binproduct G G_pP p) _ _ _ @ _).
    do 2 rewrite assoc.
    cbn.
    rewrite BinProductPr1Commutes, BinProductPr2Commutes.
    do 2 rewrite nat_trans_ax.
    apply pathsinv0.
    apply (BinProductArrowUnique _ _ _ (preserves_binproduct_to_binproduct G G_pP p)) ; apply idpath.
  Qed.

End Prelim.

(** * 1. Preservation Of Exponentials Transports Along Weak Equivalences *)
Section WeakEquivLiftsExponentialPreservation.

  Context {C₁ : category}
    (C₂ C₃ : univalent_category)
    {F : C₁ ⟶ C₃}
    {G : C₁ ⟶ C₂}
    {H : C₂ ⟶ C₃}
    (α : nat_z_iso (G ∙ H) F)
    (P₁ : BinProducts C₁)
    {P₂ : BinProducts C₂} (E₂ : Exponentials P₂)
    {P₃ : BinProducts C₃} (E₃ : Exponentials P₃)
    (G_weq : is_weak_equiv G)
    {F_pP : preserves_binproduct F}
    (F_pE : preserves_exponential_objects P₁ P₃ F_pP).

  Let H_pP : preserves_binproduct H
      := weak_equiv_lifts_preserves_binproducts α G_weq F_pP.
  Let G_pP : preserves_binproduct G
      := weak_equiv_preserves_binproducts G_weq.

  Section LiftPreservationPointwise.

    Context {x₁ y₁ e₁ : C₁} {ev₂ : C₂⟦P₂ (G x₁) (G e₁), G y₁⟧}
      (ev₂_uvp : is_exponent_uvp P₂ ev₂).

    Let ev₂' : C₂⟦G (P₁ x₁ e₁), G y₁⟧.
    Proof.
      refine (_ · ev₂).
      apply (z_iso_inv (preserves_binproduct_to_z_iso _ G_pP (P₁ x₁ e₁) (P₂ (G x₁) (G e₁)))).
    Defined.

    Let ev₁ := fully_faithful_inv_hom (pr2 G_weq) _ _ ev₂' : (C₁⟦P₁ x₁ e₁, y₁⟧).

    Local Lemma ev₂_is_img_of_ev₁
      : ev₂ = z_iso_inv (preserves_binproduct_to_z_iso G G_pP
                           (P₁ x₁ e₁) (P₂ (G x₁) (G e₁))) · # G ev₁.
    Proof.
      unfold ev₁.
      rewrite functor_on_fully_faithful_inv_hom.
      refine (_ @ assoc' _ _ _).
      refine (! id_left _ @ _).
      apply maponpaths_2.
      apply pathsinv0.
      apply z_iso_inv_after_z_iso.
    Qed.

    Local Lemma ev₁_uvp : is_exponent_uvp P₁ ev₁.
    Proof.
      apply (weak_equiv_reflects_exponential_objects P₁ P₂ G_weq x₁ y₁ e₁ ev₁).
      use (is_universal_arrow_from_after_path_induction _ _ _ _ _ _ ev₂_uvp).
      apply ev₂_is_img_of_ev₁.
    Qed.

    Let αinv := nat_z_iso_inv α.
    Let α_iso (a : C₁) := nat_z_iso_pointwise_z_iso α a.
    Let αinv_iso (a : C₁) := nat_z_iso_pointwise_z_iso (nat_z_iso_inv α) a.

    Let HG_pP := composition_preserves_binproduct G_pP H_pP.

    Local Lemma img_of_unique_binprodarrow
      : # H (z_iso_inv (preserves_binproduct_to_z_iso G G_pP (P₁ x₁ e₁) (P₂ (G x₁) (G e₁))))
        = z_iso_inv
            (preserves_binproduct_to_z_iso (G ∙ H) HG_pP (P₁ x₁ e₁)
               (preserves_binproduct_to_binproduct H H_pP (P₂ (G x₁) (G e₁)))).
    Proof.
      use (BinProductArrowUnique _ _ _ (preserves_binproduct_to_binproduct _ HG_pP _)).
      - cbn.
        rewrite <- functor_comp.
        apply maponpaths.
        set (q := preserves_binproduct_to_preserves_pr1 _ G_pP (P₁ x₁ e₁) (preserves_binproduct_to_binproduct _ G_pP (P₁ _ _))).

        use cancel_z_iso'.
        2: {
          apply (preserves_binproduct_to_z_iso _ G_pP (P₁ _ _) (P₂ _ _)).
        }
        rewrite assoc.
        refine (_ @ q @ _).
        * etrans. {
            apply maponpaths_2.
            apply (precompWithBinProductArrow _ (preserves_binproduct_to_binproduct _ _ _)).
          }
          cbn.
          rewrite BinProductPr1Commutes.
          rewrite BinProductPr2Commutes.
          refine (_ @ id_left _).
          apply maponpaths_2.
          refine (_ @ ! BinProductArrowEta _ _ _ (preserves_binproduct_to_binproduct _ G_pP (P₁ _ _)) _ (identity _)).
            now do 2 rewrite id_left.
          * etrans. {
              apply (BinProductPr1Commutes _ _ _ (preserves_binproduct_to_binproduct _ G_pP (P₁ _ _))).
            }
            apply pathsinv0.
            apply BinProductPr1Commutes.
      - cbn.
        rewrite <- functor_comp.
        apply maponpaths.
        set (q := preserves_binproduct_to_preserves_pr2 _ G_pP (P₁ x₁ e₁) (preserves_binproduct_to_binproduct _ G_pP (P₁ _ _))).

        use cancel_z_iso'.
        2: {
          apply (preserves_binproduct_to_z_iso _ G_pP (P₁ _ _) (P₂ _ _)).
        }
          rewrite assoc.
        refine (_ @ q @ _).
        * etrans. {
            apply maponpaths_2.
            apply (precompWithBinProductArrow _ (preserves_binproduct_to_binproduct _ _ _)).
          }
          cbn.
          rewrite BinProductPr1Commutes.
          rewrite BinProductPr2Commutes.
          refine (_ @ id_left _).
          apply maponpaths_2.
          refine (_ @ ! BinProductArrowEta _ _ _ (preserves_binproduct_to_binproduct _ G_pP (P₁ _ _)) _ (identity _)).
          now do 2 rewrite id_left.
        * etrans. {
            apply (BinProductPr2Commutes _ _ _ (preserves_binproduct_to_binproduct _ G_pP (P₁ _ _))).
          }
          apply pathsinv0.
          apply BinProductPr2Commutes.
    Qed.

    Local Lemma equiv_of_binprodarrows_nat_eval_lr
      {d₃ : C₃}
      (g₃ : C₃⟦d₃, F e₁⟧)
      : BinProductOfArrows C₃ (P₃ (F x₁) (F e₁)) (P₃ (F x₁) d₃) (identity (F x₁)) g₃
           · (BinProductArrow C₃ (preserves_binproduct_to_binproduct F F_pP (P₁ x₁ e₁))
                (BinProductPr1 C₃ (P₃ (F x₁) (F e₁))) (BinProductPr2 C₃ (P₃ (F x₁) (F e₁)))
                · # F ev₁)
         = BinProductOfArrows C₃ (P₃ (H (G x₁)) d₃) (P₃ (F x₁) d₃) (αinv x₁) (identity d₃)
             · (BinProductOfArrows C₃ (P₃ (H (G x₁)) (H (G e₁))) (P₃ (H (G x₁)) d₃) (identity (H (G x₁))) (g₃ · αinv e₁)
                  · (BinProductArrow C₃ (preserves_binproduct_to_binproduct H H_pP (P₂ (G x₁) (G e₁)))
                       (BinProductPr1 C₃ (P₃ (H (G x₁)) (H (G e₁)))) (BinProductPr2 C₃ (P₃ (H (G x₁)) (H (G e₁))))
                       · # H ev₂) · α y₁).
    Proof.
      apply pathsinv0.
      rewrite ev₂_is_img_of_ev₁.
      rewrite functor_comp.
      rewrite ! assoc'.
      etrans. {
        do 4 apply maponpaths.
        apply (nat_trans_ax α _ _ ev₁).
      }
      rewrite ! assoc.
      apply maponpaths_2.

      rewrite BinProductOfArrows_comp.
      rewrite id_left, id_right.

      etrans. {
        rewrite assoc'.
        apply maponpaths.
        set (p_HG := composition_preserves_binproduct G_pP H_pP).
        set (t := nat_trans_commute_with_binproduct_preservation p_HG F_pP α
                 (P₁ x₁ e₁) (preserves_binproduct_to_binproduct _ H_pP (P₂ _ _))
                 (P₃ _ _)).
        refine (_ @ ! t).
        apply maponpaths_2.
        apply img_of_unique_binprodarrow.
      }
      cbn.
      rewrite assoc.
      apply maponpaths_2.
      unfold BinProductOfArrows.

      rewrite (precompWithBinProductArrow).
      use maponpaths_12.
      - etrans. {
          apply maponpaths_2.
          apply (precompWithBinProductArrow _ (preserves_binproduct_to_binproduct _ _ _)).
        }
        rewrite BinProductPr1Commutes, BinProductPr2Commutes.
        rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite assoc'.
        apply maponpaths.
        apply (z_iso_after_z_iso_inv (α_iso _)).
      - etrans. {
          apply maponpaths_2.
          apply (precompWithBinProductArrow _ (preserves_binproduct_to_binproduct _ _ _)).
        }
        rewrite BinProductPr1Commutes, BinProductPr2Commutes.
        rewrite assoc.
        rewrite BinProductPr2Commutes.
        rewrite assoc'.
        apply maponpaths.
        refine (_ @ id_right _).
        rewrite assoc'.
        apply maponpaths.
        apply (z_iso_after_z_iso_inv (α_iso _)).
    Qed.

    Local Lemma equiv_of_binprodarrows_nat_eval
      {d₃ : C₃}
      (f₃ : C₃⟦P₃ (H (G x₁)) d₃, H (G y₁)⟧)
      (g₃ : C₃⟦d₃, F e₁⟧)
      : (BinProductOfArrows C₃ (P₃ _ _) (P₃ _ _) (αinv x₁) (identity d₃) · f₃ · α y₁
         = BinProductOfArrows C₃ (P₃ _ _) (P₃ _ _) (identity (F x₁)) g₃
             · (BinProductArrow C₃ (preserves_binproduct_to_binproduct F F_pP (P₁ x₁ e₁))
                  (BinProductPr1 C₃ (P₃ (F x₁) (F e₁))) (BinProductPr2 C₃ (P₃ (F x₁) (F e₁)))
                  · # F ev₁))
          ≃
          (f₃ = BinProductOfArrows C₃ (P₃ (H (G x₁)) (H (G e₁))) (P₃ (H (G x₁)) d₃)
                  (identity (H (G x₁))) (g₃ · αinv e₁)
                  · (BinProductArrow C₃
                       (preserves_binproduct_to_binproduct H H_pP (P₂ (G x₁) (G e₁)))
                       (BinProductPr1 C₃ (P₃ (H (G x₁)) (H (G e₁))))
                       (BinProductPr2 C₃ (P₃ (H (G x₁)) (H (G e₁))))
                       · # H ev₂)).
    Proof.
      use weqimplimpl.
      - intro pf.
        use (cancel_z_iso _ _ (nat_z_iso_pointwise_z_iso α _)).
        use (cancel_z_iso' (binproduct_of_z_iso (P₃ _ _) (P₃ _ _) (αinv_iso _) (_ ,, identity_is_z_iso _))).
        refine (assoc _ _ _ @ pf @ _).
        clear pf.
        apply (equiv_of_binprodarrows_nat_eval_lr g₃).

      - intro pf.
        rewrite pf.
        clear pf.
        rewrite ! assoc.
        rewrite BinProductOfArrows_comp.
        rewrite id_right, id_left.
        use (z_iso_inv_to_right _ _ _ _ (α_iso _)).
        apply pathsinv0.
        etrans. {
          do 2 apply maponpaths_2.
          apply (precompWithBinProductArrow _  (preserves_binproduct_to_binproduct _ F_pP (P₁ _ _))).
        }
        rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
        do 2 rewrite assoc'.
        etrans. {
          apply maponpaths, (nat_trans_ax αinv).
        }
        etrans. {
          do 2 apply maponpaths.
          simpl ; apply maponpaths.
          apply functor_on_fully_faithful_inv_hom.
        }
        unfold ev₂'.
        rewrite functor_comp.
        rewrite ! assoc.
        apply maponpaths_2.
        simpl.
        etrans. {
          apply maponpaths.
          apply (preserves_binproduct_to_preserves_arrow _ H_pP (P₂ _ _) (P₃ _ _)).
        }
        cbn.
        rewrite assoc.
        apply maponpaths_2.
        rewrite assoc'.
        etrans. { apply maponpaths, precompWithBinProductArrow. }
        etrans. { apply precompWithBinProductArrow. }
        unfold BinProductOfArrows.
        etrans. {
          apply maponpaths_12 ; apply maponpaths, pathsinv0, (nat_trans_ax αinv).
        }
        rewrite id_right.
        apply maponpaths_12 ; rewrite ! assoc ; apply maponpaths_2.
        + apply (BinProductPr1Commutes _ _ _ (preserves_binproduct_to_binproduct _ F_pP (P₁ _ _))).
        + apply (BinProductPr2Commutes _ _ _ (preserves_binproduct_to_binproduct _ F_pP (P₁ _ _))).
      - apply homset_property.
      - apply homset_property.
    Qed.

    Lemma weak_equiv_lifts_preserves_exponential_objects₀
      : is_exponent_uvp P₃
          (z_iso_inv (preserves_binproduct_to_z_iso H H_pP (P₂ (G x₁) (G e₁)) (P₃ (H (G x₁)) (H (G e₁)))) · # H ev₂).
    Proof.
      set (Fev_uvp := F_pE x₁ y₁ e₁ ev₁ ev₁_uvp).
      intros [d₃ f₃].
      set (t := Fev_uvp (d₃ ,, BinProductOfArrows _ (P₃ _ _) _ (nat_z_iso_inv α _) (identity _) ·  f₃ · α _)).
      use (iscontrweqf _ t).
      use weqtotal2.
      - apply z_iso_comp_left_weq.
        exact (nat_z_iso_pointwise_z_iso (nat_z_iso_inv α) e₁).
      - intro g₃.
        apply equiv_of_binprodarrows_nat_eval.
    Qed.

  End LiftPreservationPointwise.

  Lemma weak_equiv_lifts_preserves_exponential_objects
    : preserves_exponential_objects P₂ P₃ H_pP.
  Proof.
    intros x₂ y₂.
    use (factor_through_squash _ _ (eso_from_weak_equiv _ G_weq x₂)).
    { repeat (apply impred_isaprop ; intro) ; apply isapropiscontr. }
    intros [x₁ ix].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ G_weq y₂)).
    { repeat (apply impred_isaprop ; intro) ; apply isapropiscontr. }
    intros [y₁ iy].

    intros e₂ ev₂ ev₂_uvp.

    use (factor_through_squash _ _ (eso_from_weak_equiv _ G_weq e₂)).
    { apply impred_isaprop ; intro ; apply isapropiscontr. }
    intros [e₁ ie].

    set (px := isotoid _ (pr2 C₂) ix).
    induction px.
    set (py := isotoid _ (pr2 C₂) iy).
    induction py.
    set (pe := isotoid _ (pr2 C₂) ie).
    induction pe.

    apply weak_equiv_lifts_preserves_exponential_objects₀.
    exact ev₂_uvp.
  Qed.

  Lemma weak_equiv_lifts_preserves_exponentials
    : preserves_exponentials E₂ E₃ H_pP.
  Proof.
    apply preserves_exponential_objects_to_preserves_exponentials.
    unfold preserves_exponential_objects'.
    intros x₂ y₂.
    apply (weak_equiv_lifts_preserves_exponential_objects x₂ y₂ (exp (E₂ x₂) y₂) (exp_eval (E₂ x₂) y₂)).
    apply is_exponentiable_to_uvp.
  Qed.

End WeakEquivLiftsExponentialPreservation.

Lemma weak_equiv_lifts_preserves_exponentials'
  {C₁ : category}
  (C₂ C₃ : univalent_category)
  {F : C₁ ⟶ C₃}
  {G : C₁ ⟶ C₂}
  {H : C₂ ⟶ C₃}
  (α : nat_z_iso (G ∙ H) F)
  {P₁ : BinProducts C₁} (E₁ : Exponentials P₁)
  {P₂ : BinProducts C₂} (E₂ : Exponentials P₂)
  {P₃ : BinProducts C₃} (E₃ : Exponentials P₃)
  (G_weq : is_weak_equiv G)
  {F_pP : preserves_binproduct F}
  (F_pE : preserves_exponentials E₁ E₃ F_pP)
  : preserves_exponentials E₂ E₃ (weak_equiv_lifts_preserves_binproducts α G_weq F_pP).
Proof.
  use weak_equiv_lifts_preserves_exponentials.
  { exact P₁. }

  set (t := preserves_exponentials_to_preserves_exponential_objects P₁ P₃ F_pP E₁ E₃ F_pE).
  exact (preserves_exponential_objects'_to_preserves_exponential_objects P₁ P₃ F_pP t).
Qed.
