(**
   In this file, we show how weak equivalences reflect exponential objects.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.

Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Exponentials.

Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Binproducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.BinProducts.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Exponentials.

Local Open Scope cat.

Section WeakEquivReflectsExponentialObjects.

  Context {C₀ C₁ : category}
    (P₀ : BinProducts C₀) (P₁ : BinProducts C₁)
    {F : C₀ ⟶ C₁} (F_weq : is_weak_equiv F).

  Definition weak_equiv_z_iso_binprod (x y : C₀)
    : z_iso (P₁ (F x) (F y)) (F (P₀ x y)).
  Proof.
    exact (z_iso_inv (preserves_binproduct_to_z_iso F (weak_equiv_preserves_binproducts F_weq)
                        (P₀  _ _) (P₁ (F _) (F _)))).
  Defined.

  Context {x₀ y₀ e₀ : C₀}
    (ev₀ : C₀⟦P₀ x₀ e₀, y₀⟧)
    (ev_uvp : is_exponentiable_alt_uvp P₁ (weak_equiv_z_iso_binprod _ _ · # F ev₀))
    {a₀ : C₀}
    (f₀ : C₀⟦P₀ x₀ a₀, y₀⟧).

  Let f₁ : C₁⟦P₁ (F x₀) (F a₀), F y₀⟧ := weak_equiv_z_iso_binprod _ _ · #F f₀.

  Definition weak_equiv_reflect_exp_lam : C₀⟦a₀, e₀⟧
    := fully_faithful_inv_hom (pr2 F_weq) _ _
      (pr11 (ev_uvp (make_coreflection_data (F := constprod_functor1 _ _) _ f₁))).

  Lemma weak_equiv_reflect_exp_lam_helper (ψ : C₀⟦a₀, e₀⟧)
    :  BinProductOfArrows C₁ (P₁ _ _) (P₁ _ _)
         (identity (F x₀)) (#F ψ)
         · inv_from_z_iso
         (preserves_binproduct_to_z_iso F (weak_equiv_preserves_binproducts F_weq)
            (P₀ x₀ e₀) (P₁ (F x₀) (F e₀)))
       = weak_equiv_z_iso_binprod x₀ a₀
           · # F (BinProductOfArrows C₀ (P₀ x₀ e₀) (P₀ x₀ a₀)
                    (identity x₀) ψ).
  Proof.
    set (t' := preserves_binproduct_of_arrows (BC₁ := P₀) (BC₂ := P₁)
                 (weak_equiv_preserves_binproducts F_weq) (identity x₀) ψ).
    refine (_ @ ! t').
    do 2 apply maponpaths_2.
    apply pathsinv0, functor_id.
  Qed.

  Lemma weak_equiv_reflect_exp_lam_app
    : f₀ =
        BinProductOfArrows C₀ (P₀ x₀ e₀) (P₀ x₀ a₀) (identity x₀) weak_equiv_reflect_exp_lam · ev₀.
  Proof.
    set(t := pr21 (ev_uvp (make_coreflection_data (F := constprod_functor1 _ _) _ f₁))).
    simpl in t ; unfold BinProduct_of_functors_mor in t ; simpl in t.

    use (faithful_reflects_morphism_equality _ (pr2 F_weq)).
    use (cancel_z_iso' (weak_equiv_z_iso_binprod _ _)).

    refine (t @ _).
    rewrite functor_comp.
    rewrite ! assoc.
    apply maponpaths_2.
    refine (_ @ weak_equiv_reflect_exp_lam_helper weak_equiv_reflect_exp_lam).
    apply maponpaths_2, maponpaths.
    apply pathsinv0, functor_on_fully_faithful_inv_hom.
  Qed.

  Section WeakEquivReflectsExponentialsObjectsUniqueness.

    Let A := (∑ f' : C₀ ⟦ a₀, e₀ ⟧, f₀ = # (constprod_functor1 P₀ x₀) f' · ev₀).

    Lemma bla (ϕ : A)
      : f₁ =  BinProductOfArrows C₁ (P₁ (F x₀) (F e₀)) (P₁ (F x₀) (F a₀))
                (identity (F x₀)) (# F (pr1 ϕ))
                · (weak_equiv_z_iso_binprod x₀ e₀ · # F ev₀).
    Proof.
      use (cancel_z_iso' (z_iso_inv (weak_equiv_z_iso_binprod _ _))).
      refine (_ @ maponpaths #F (pr2 ϕ) @ _).
      - refine (assoc _ _ _ @ _).
        refine (_ @ id_left _).
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      - rewrite functor_comp.
        rewrite ! assoc.
        apply maponpaths_2.
        rewrite assoc'.
        use z_iso_inv_to_left.
        exact (! weak_equiv_reflect_exp_lam_helper (pr1 ϕ)).
    Qed.

    Lemma weak_equiv_reflects_exponential_objects_uniqueness
      : isaprop A.
    Proof.
      use invproofirrelevance.
      intros ϕ₁ ϕ₂.
      use subtypePath.
      { intro ; apply homset_property. }

      use (faithful_reflects_morphism_equality _ (pr2 F_weq)).
      set (t₁ := ! pr2 (ev_uvp (make_coreflection_data (F := constprod_functor1 _ _) (F a₀) f₁)) (#F (pr1 ϕ₁) ,, bla ϕ₁)).
      set (t₂ := ! pr2 (ev_uvp (make_coreflection_data (F := constprod_functor1 _ _) (F a₀) f₁)) (#F (pr1 ϕ₂) ,, bla ϕ₂)).
      exact (! base_paths _ _ t₁ @ base_paths _ _ t₂).
    Qed.

  End WeakEquivReflectsExponentialsObjectsUniqueness.

  Proposition weak_equiv_reflects_exponential_objects_uvp
    : ∃! f' : C₀ ⟦ a₀, e₀ ⟧, f₀ = # (constprod_functor1 P₀ x₀) f' · ev₀.
  Proof.
    use iscontraprop1.
    { exact weak_equiv_reflects_exponential_objects_uniqueness. }
    use tpair.
    - exact weak_equiv_reflect_exp_lam.
    - exact weak_equiv_reflect_exp_lam_app.
  Defined.

End WeakEquivReflectsExponentialObjects.

Proposition weak_equiv_reflects_exponential_objects
  {C₀ C₁ : category} (P₀ : BinProducts C₀) (P₁ : BinProducts C₁)
  {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
  : reflects_exponential_objects P₀ P₁ (weak_equiv_preserves_binproducts F_weq).
Proof.
  intros x₀ y₀ e₀ ev₀ ev_uvp f₀.
  apply (weak_equiv_reflects_exponential_objects_uvp P₀ P₁ F_weq).
  assumption.
Defined.
