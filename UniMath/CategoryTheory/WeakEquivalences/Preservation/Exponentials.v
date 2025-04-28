(**
   In this file, we show that an arbitrary weak equivalence F : C -> D preserves exponential objects.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.BinProducts.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Exponentials.

Local Open Scope cat.

Section WeakEquivalencesPreserveExponentialObjects.

  Context {C₀ C₁ : category}
    {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
    (C₁_univ : is_univalent C₁)
    {P₀ : BinProducts C₀}
    (E₀ : Exponentials P₀).

  Context (P₁ : BinProducts C₁).

  Context {x₀ y₀ : C₀}
    {a₁ : C₁}
    (f₁ : C₁⟦P₁ (F x₀) a₁, F y₀⟧)
    {a₀ : C₀}
    (i₀ : z_iso (F a₀) a₁).

  Let e₀ := exp (E₀ x₀) y₀.
  Let ev₀ := exp_eval (E₀ x₀) y₀.

  Let i_p : z_iso (F (P₀ x₀ a₀)) (P₁ (F x₀) a₁).
  Proof.
    refine (z_iso_comp _ (BinProductOfIsos P₁ (pr2 (identity_z_iso (F x₀))) (pr2 i₀))).
    use preserves_binproduct_to_z_iso.
    exact (weak_equiv_preserves_binproducts F_weq).
  Defined.

  Let f₀ : C₀⟦P₀ x₀ a₀, y₀⟧ := fully_faithful_inv_hom (pr2 F_weq) _ _ (i_p · f₁).
  Local Lemma Ff₀ : #F f₀ = i_p · f₁.
  Proof.
    apply functor_on_fully_faithful_inv_hom.
  Qed.
  Local Lemma Ff₀' : z_iso_inv i_p · #F f₀ = f₁.
  Proof.
    rewrite Ff₀.
    rewrite assoc.
    rewrite z_iso_inv_after_z_iso.
    apply id_left.
  Qed.

  Definition weak_equiv_preserves_exponentiable_objects_map
    : C₁ ⟦a₁, F e₀⟧ := z_iso_inv i₀ · #F (exp_lam _ f₀).

  Local Lemma commutation_of_binproductarrows
    : z_iso_inv i_p · # F (BinProductOfArrows C₀ (P₀ _ _) (P₀ x₀ a₀) (identity x₀) (exp_lam (E₀ x₀) f₀))
      = BinProductArrow C₁
          (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))
          (BinProductPr1 C₁ (P₁ (F x₀) a₁) · identity (F x₀))
          (BinProductPr2 C₁ (P₁ (F x₀) a₁) · weak_equiv_preserves_exponentiable_objects_map).
  Proof.
    etrans. {
      unfold i_p.
      cbn.
      rewrite assoc'.
      apply maponpaths.
      apply (preserves_binproduct_of_arrows (weak_equiv_preserves_binproducts F_weq)).
    }
    rewrite assoc.
    rewrite BinProductOfArrows_comp.
    etrans. {
      apply (precompWithBinProductArrow _  (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ (exp (E₀ x₀) y₀)))).
    }
    apply maponpaths_12.
    - etrans. { apply BinProductOfArrowsPr1. }
      rewrite functor_id.
      now rewrite id_right.
    - apply BinProductOfArrowsPr2.
   Qed.

  Lemma weak_equiv_preserves_exponentiable_objects_eq
    : f₁ =
        BinProductOfArrows C₁ (P₁ (F x₀) (F e₀)) (P₁ (F x₀) a₁)
          (identity (F x₀))
          weak_equiv_preserves_exponentiable_objects_map
          · (BinProductArrow C₁
               (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))
               (BinProductPr1 C₁ (P₁ (F x₀) (F e₀)))
               (BinProductPr2 C₁ (P₁ (F x₀) (F e₀)))
               · # F ev₀).
  Proof.
    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0.
      apply precompWithBinProductArrow.
    }

    rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.

    set (t := exp_beta (E₀ x₀) f₀).
    unfold weak_equiv_preserves_exponentiable_objects_map.
    rewrite assoc.

    refine (! Ff₀' @ _).

    etrans. {
      do 2 apply maponpaths.
      exact (! exp_beta (E₀ x₀) f₀).
    }
    rewrite functor_comp.
    rewrite ! assoc.
    apply maponpaths_2.
    rewrite assoc'.
    apply commutation_of_binproductarrows.
  Qed.

  Lemma weak_equiv_preserves_exponentiable_objects_uniqueness
    : isaprop
    (∑ f' : C₁ ⟦ a₁, F e₀ ⟧,
     f₁ =
     BinProductOfArrows C₁ (P₁ (F x₀) (F e₀)) (P₁ (F x₀) a₁) (identity (F x₀)) f'
     · (BinProductArrow C₁
          (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))
          (BinProductPr1 C₁ (P₁ (F x₀) (F e₀))) (BinProductPr2 C₁ (P₁ (F x₀) (F e₀))) ·
          # F (ev₀))).
  Proof.
    use invproofirrelevance.
    intros ϕ₁ ϕ₂.

    use subtypePath.
    { intro ; apply homset_property. }
    use (cancel_z_iso' i₀).

    (* F a₀ → F e₀ *)
    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _).

    (* a₀ → e₀ *)
    apply maponpaths.
    set (ψ₁ :=  invmap (weq_from_fully_faithful (ff_from_weak_equiv F F_weq) a₀ e₀) (i₀ · pr1 ϕ₁)).
    set (ψ₂ :=  invmap (weq_from_fully_faithful (ff_from_weak_equiv F F_weq) a₀ e₀) (i₀ · pr1 ϕ₂)).

    set (t := is_exponentiable_to_uvp P₀ (E₀ x₀) y₀ a₀ (exp_app (E₀ _) ψ₁)).
    use (base_paths _ _ (proofirrelevancecontr t (ψ₁ ,, _) (ψ₂ ,, _))).
    {
      refine (pr21 t @ _).
      apply maponpaths_2, maponpaths.
      apply exp_lam_app.
    }

    (* P₀ x₀ a₀ → y₀ *)
    apply (faithful_reflects_morphism_equality _ (pr2 F_weq)).
    rewrite functor_comp.
    cbn ; unfold BinProduct_of_functors_mor ; cbn.
    (* F (P₀ x₀ a₀) → F y₀ *)

    use cancel_z_iso'. (* P₁ (F x₀) a₁ ≅ F (P₀ x₀ a₀) *)
    { exact (P₁ (F x₀) a₁). }
    {
      refine (z_iso_comp (BinProductOfIsos P₁ (pr2 (identity_z_iso _)) (pr2 (z_iso_inv i₀))) _).
      use z_iso_inv.
      apply (preserves_binproduct_to_z_iso _ (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ a₀) (P₁ _ _)).
    }
    set (p := ! pr2 ϕ₁ @ pr2 ϕ₂).
    rewrite ! assoc in p.
    refine (_ @ p @ _) ; cbn.
    - etrans. {
        apply maponpaths_2.
        apply (precompWithBinProductArrow _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ _ _))).
      }
      rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
      etrans.
      2: {
        apply maponpaths_2.
        apply pathsinv0.
        apply (precompWithBinProductArrow _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))).
      }
      rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
      cbn.

      etrans. {
        apply maponpaths.
        exact (maponpaths #F (pr21 t)).
      }
      rewrite functor_comp.
      rewrite ! assoc.
      apply maponpaths_2.
      assert (pf : pr11 t = ψ₁).
      {
        apply pathsinv0.
        use (base_paths _ _ (proofirrelevancecontr t (ψ₁ ,, _) _)).
        simpl.
        refine (pr21 t @ _).
        apply maponpaths_2, maponpaths.
        apply exp_lam_app.
      }

      rewrite pf.

      set (t' := preserves_binproduct_of_arrows (weak_equiv_preserves_binproducts F_weq)
                   (BC₁ := P₀) (BC₂ := P₁) (identity x₀) ψ₁).
      set (t'' := z_iso_inv_to_left _ _ _ _ _ _ t').
      etrans. {
        apply maponpaths.
        exact t''.
      }
      cbn.

      rewrite ! assoc.
      rewrite (precompWithBinProductArrow _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))).
      rewrite ! assoc'.
      rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
      rewrite ! assoc.

      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply BinProductPr2Commutes.
      }
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        apply (BinProductOfArrowsPr2 _  (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ a₀))).
      }
      etrans. {
        apply maponpaths_2.
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply BinProductPr1Commutes.
      }
      unfold BinProductOfArrows ; apply maponpaths_12.
      + rewrite functor_id.
        apply maponpaths_2.
        etrans. {
          apply (BinProductPr1Commutes _ _ _ (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ _ _))).
        }
        apply id_right.
      + rewrite assoc'.
        apply maponpaths.
        etrans. {
          apply maponpaths.
          apply functor_on_fully_faithful_inv_hom.
        }
        rewrite assoc.
        rewrite z_iso_after_z_iso_inv.
        apply id_left.
    - rewrite ! assoc.
      apply maponpaths_2.
      set (t' := preserves_binproduct_of_arrows (weak_equiv_preserves_binproducts F_weq)
                   (BC₁ := P₀) (BC₂ := P₁) (identity x₀) ψ₂).
      set (t'' := z_iso_inv_to_left _ _ _ _ _ _ t').
      etrans.
      2: {
        apply maponpaths.
        exact (! t'').
      }
      cbn.
      etrans. {
        apply (precompWithBinProductArrow _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))).
      }
      rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
      apply pathsinv0.
      rewrite ! assoc.
      etrans. {
        apply (precompWithBinProductArrow _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))).
      }
      rewrite ! assoc'.
      rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
      apply maponpaths_12.
      + rewrite functor_id.
        rewrite ! assoc.
        etrans. {
          do 3 apply maponpaths_2.
        apply (precompWithBinProductArrow _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ _ _))).
        }
        rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
        rewrite precompWithBinProductArrow.
        apply maponpaths_2.
        etrans. { apply BinProductPr1Commutes. }

        etrans. {
          apply (BinProductPr1Commutes _ _ _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ a₀))).
        }
        apply id_right.
      + rewrite ! assoc.
        etrans. {
          do 3 apply maponpaths_2.
        apply (precompWithBinProductArrow _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ _ _))).
        }
        rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2.
        rewrite precompWithBinProductArrow.
        etrans. {
          apply maponpaths.
          apply functor_on_fully_faithful_inv_hom.
        }
        rewrite assoc.
        apply maponpaths_2.
        etrans. {
          apply maponpaths_2.
          apply BinProductPr2Commutes.
        }

        etrans. {
          apply maponpaths_2.
          apply (BinProductPr2Commutes _ _ _   (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ a₀))).
        }
        rewrite assoc'.
        rewrite z_iso_after_z_iso_inv.
        apply id_right.
  Qed.

  Lemma weak_equiv_preserves_exponentiable_objects_uvp
    : ∃! f' : C₁ ⟦ a₁, F e₀ ⟧,
        f₁ =
          BinProductOfArrows C₁ (P₁ (F x₀) (F e₀)) (P₁ (F x₀) a₁)
            (identity (F x₀)) f'
            · (BinProductArrow C₁
       (preserves_binproduct_to_binproduct F (weak_equiv_preserves_binproducts F_weq) (P₀ x₀ e₀))
       (BinProductPr1 C₁ (P₁ (F x₀) (F e₀)))
       (BinProductPr2 C₁ (P₁ (F x₀) (F e₀)))
       · # F ev₀).
  Proof.
    use iscontraprop1.
    { exact weak_equiv_preserves_exponentiable_objects_uniqueness. }
    exists weak_equiv_preserves_exponentiable_objects_map.
    exact weak_equiv_preserves_exponentiable_objects_eq.
  Defined.

End WeakEquivalencesPreserveExponentialObjects.

Proposition weak_equiv_preserves_exponential_objects
  {C₀ C₁ : category}
  {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
  (C₁_univ : is_univalent C₁)
  {P₀ : BinProducts C₀}
  (E₀ : Exponentials P₀)
  (P₁ : BinProducts C₁)
  : preserves_exponential_objects'
      P₀ P₁
      (weak_equiv_preserves_binproducts F_weq) E₀.
Proof.
  intros x₀ y₀.
  intros a₁ f₁.
  use (factor_through_squash _ _ (pr1 F_weq a₁)).
  { intro ; apply isapropiscontr. }
  intros [a₀ i₀].
  exact (weak_equiv_preserves_exponentiable_objects_uvp _ _ _ _ i₀).
Defined.

Section WeakEquivalencesIntoUnivalentCatsCreatesExponentials.

  Context {C₀ C₁ : category}
    {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
    (C₁_univ : is_univalent C₁)
    {P₀ : BinProducts C₀}
    (E₀ : Exponentials P₀)
    (P₁ : BinProducts C₁).

  Lemma weak_equiv_into_univ_creates_exponentials
    : Exponentials P₁.
  Proof.
    intro x₁.
    use is_exponentiable_alt_to_is_exponentiable.
    use (factor_through_squash _ _ (pr1 F_weq x₁)).
    {
      apply impred_isaprop ; intro.
      apply isaprop_Exponent.
      exact C₁_univ.
    }
    intros [x₀ ix].
    apply (is_exponentiable_alt_closed_under_iso _ ix).
    intro y₁.
    use (factor_through_squash _ _ (pr1 F_weq y₁)).
    {
      apply isaprop_Exponent.
      exact C₁_univ.
    }
    intros [y₀ iy].
    apply (Exponent_transport_along_iso' P₁ (identity_z_iso _) iy).
    apply (preserves_exponential_objects_to_exponent' P₀ P₁ (weak_equiv_preserves_binproducts F_weq) (E₀ := E₀)).
    apply (weak_equiv_preserves_exponential_objects F_weq C₁_univ).
  Defined.

End WeakEquivalencesIntoUnivalentCatsCreatesExponentials.

Section WeakEquivalencesIntoUnivalentCatsPreservesExponentials.

  Context {C₀ C₁ : category}
    {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
    (C₁_univ : is_univalent C₁)
    {P₀ : BinProducts C₀}
    (E₀ : Exponentials P₀).

  Lemma weak_equiv_preserves_exponentials
    : preserves_exponentials E₀
        (weak_equiv_into_univ_creates_exponentials F_weq C₁_univ E₀
        (weak_equiv_into_univ_creates_binproducts C₁_univ F_weq P₀))
        (weak_equiv_preserves_binproducts F_weq).
  Proof.
    use preserves_exponential_objects_to_preserves_exponentials.
    apply weak_equiv_preserves_exponential_objects.
    exact C₁_univ.
  Defined.

  Corollary weak_equiv_preserves_exponentials'
    {P₁ : BinProducts C₁} (E₁ : Exponentials P₁)
    : preserves_exponentials E₀ E₁ (weak_equiv_preserves_binproducts F_weq).
  Proof.
    use preserves_exponential_objects_to_preserves_exponentials.
    apply weak_equiv_preserves_exponential_objects.
    exact C₁_univ.
  Defined.

End WeakEquivalencesIntoUnivalentCatsPreservesExponentials.
