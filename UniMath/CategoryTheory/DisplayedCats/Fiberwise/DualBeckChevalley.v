(***************************************************************************************

 The Dual Beck-Chevalley condition

 In the setting of categorical logic, quantifiers are interpreted as certain adjoints.
 More concretely, existential quantifiers and sigma types are interpreted as left adjoints
 of weakening, whereas universal quantifiers and pi types are interpreted as right adjoints
 of weakening. These quantifiers must also satisfy a condition that expresses stability
 under substitution: more concretely, if we perform a substitution on a universal
 quantifier, then we again get a universally quantified formula. In the semantics, these
 stability axioms are expressed as Beck-Chevalley conditions.

 If we are interested in first-order logic with quantifiers (semantically, a hyperdoctrine)
 or in dependent type theory with sigma types and pi types (semantically, a comprehension
 category), then we need the Beck-Chevalley condition for both the universal and the
 existential quantifier. However, it suffices to verify only one of those. More specifically,
 if the existential quantifier is stable under substitution, then so is the universal
 quantifier. For this reason, only one Beck-Chevalley condition is usually required in
 the definition of hyperdoctrines (see, e.g., "Hyperdoctrines, natural deduction and the
 Beck condition" by Seely).

 In this file, we prove this statement. More specifically, suppose that we have a fibration
 `D` over `C` and a commuting square `k · f = h · g` where `f : x --> w`, `g : y --> w`,
 `h : z --> y`, and `k : z --> x`, and suppose that pulling back along `f` and h` has a
 right adjoint, and pulling back along `g` and `k` has a left adjoint. If we can verify
 the Beck-Chevalley condition for the left adjoints of `g` and `k`, then the Beck-Chevalley
 condition also holds for the right adjoints of `f` and `g`.

 References
 - "Hyperdoctrines, natural deduction and the Beck condition" by Seely

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.

Local Open Scope cat.

Section DualBeckChevalley.
  Context {C : category}
          {D : disp_cat C}
          (HD : cleaving D)
          {w x y z : C}
          {f : x --> w}
          {g : y --> w}
          {h : z --> y}
          {k : z --> x}
          {p : k · f = h · g}
          {P₁ : dependent_product HD f}
          {P₂ : dependent_product HD h}
          {S₁ : dependent_sum HD g}
          {S₂ : dependent_sum HD k}
          (HB : left_beck_chevalley HD g f k h (!p) S₁ S₂).

  Let F : D[{w}] ⟶ D[{x}] := fiber_functor_from_cleaving D HD f.
  Let R₁ : D[{x}] ⟶ D[{w}] := right_adjoint P₁.
  Let η₁ : functor_identity _ ⟹ F ∙ R₁
    := unit_from_left_adjoint P₁.
  Let ε₁ : R₁ ∙ F ⟹ functor_identity _
    := counit_from_left_adjoint P₁.

  Let H : D[{y}] ⟶ D[{z}] := fiber_functor_from_cleaving D HD h.
  Let R₂ : D[{z}] ⟶ D[{y}] := right_adjoint P₂.
  Let η₂ : functor_identity _ ⟹ H ∙ R₂
    := unit_from_left_adjoint P₂.
  Let ε₂ : R₂ ∙ H ⟹ functor_identity _
    := counit_from_left_adjoint P₂.

  Let G : D[{w}] ⟶ D[{y}] := fiber_functor_from_cleaving D HD g.
  Let L₁ : D[{y}] ⟶ D[{w}]
    := left_adjoint S₁.
  Let φ₁ : functor_identity _ ⟹ L₁ ∙ G
    := unit_from_right_adjoint S₁.
  Let ψ₁ : G ∙ L₁ ⟹ functor_identity _
    := counit_from_right_adjoint S₁.

  Let K : D[{x}] ⟶ D[{z}] := fiber_functor_from_cleaving D HD k.
  Let L₂ : D[{z}] ⟶ D[{x}]
    := left_adjoint S₂.
  Let φ₂ : functor_identity _ ⟹ L₂ ∙ K
    := unit_from_right_adjoint S₂.
  Let ψ₂ : K ∙ L₂ ⟹ functor_identity _
    := counit_from_right_adjoint S₂.

  Let τ : nat_z_iso (G ∙ H) (F ∙ K)
    := comm_nat_z_iso HD g f k h (!p).
  Let ℓ_iso : nat_z_iso (H ∙ L₂) (L₁ ∙ F)
    := make_nat_z_iso
         _ _
         (left_beck_chevalley_nat_trans S₁ S₂ τ)
         HB.
  Let ℓ : H ∙ L₂ ⟹ L₁ ∙ F
    := left_beck_chevalley_nat_trans S₁ S₂ τ.
  Let ℓi : L₁ ∙ F ⟹ H ∙ L₂
    := nat_z_iso_inv ℓ_iso.

  Let θ : nat_z_iso (G ∙ H) (F ∙ K)
    := comm_nat_z_iso_inv HD f g h k p.
  Let ρ : R₁ ∙ G ⟹ K ∙ R₂
    := right_beck_chevalley_nat_trans P₁ P₂ θ.

  #[local] Opaque fiber_category.

  Proposition inv_of_comm_nat_z_iso
              (xx : D[{x}])
    : nat_z_iso_inv (comm_nat_z_iso HD f g h k p) (right_adjoint P₁ xx)
      =
      τ (R₁ xx).
  Proof.
    unfold τ.
    cbn -[fiber_functor_from_cleaving_comp_nat_z_iso fiber_functor_on_eq_nat_z_iso].
    rewrite !assoc'.
    apply maponpaths.
    apply maponpaths_2.
    refine (!(id_right _) @ _).
    use z_iso_inv_on_right.
    cbn.
    refine (_ @ pr1_idtoiso_concat _ _).
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (λ q, pr1 (HD w z q (R₁ xx))) _ _) @ _).
      rewrite pathsinv0r.
      apply idpath.
    }
    apply idpath.
  Qed.

  Lemma dual_right_beck_chevalley_nat_trans_ob
        (xx : D[{x}])
    : ρ xx
      =
      η₂(G(R₁ xx))
      · #R₂(τ(R₁ xx))
      · #R₂(#K(ε₁ xx)).
  Proof.
    unfold ρ.
    etrans.
    {
      apply right_beck_chevalley_nat_trans_ob.
    }
    apply maponpaths_2.
    do 2 apply maponpaths.
    apply inv_of_comm_nat_z_iso.
  Qed.

  Lemma dual_left_beck_chevalley_nat_trans_ob
        (xx : D[{x}])
    : ℓ (G(R₁ xx))
      =
      #L₂(#H(φ₁(G(R₁ xx))))
      · #L₂(τ(L₁(G(R₁ xx))))
      · ψ₂(F(L₁(G(R₁ xx)))).
  Proof.
    apply left_beck_chevalley_nat_trans_ob.
  Qed.

  Lemma dual_left_beck_chevalley_nat_trans_ob'
        (xx : D[{x}])
    : ℓ (R₂(K xx))
      =
      #L₂(#H(φ₁(R₂(K xx))))
      · #L₂(τ(L₁(R₂(K xx))))
      · ψ₂(F(L₁(R₂(K xx)))).
  Proof.
    apply left_beck_chevalley_nat_trans_ob.
  Qed.

  #[local] Opaque F G H K η₁ η₂ ε₁ ε₂ φ₁ φ₂ ψ₁ ψ₂ R₁ R₂ L₁ L₂ ℓi ℓ ρ τ.

  Lemma dual_left_beck_chevalley_nat_trans_ob_alt
        (xx : D[{x}])
    : ℓ (G(R₁ xx)) · #F(ψ₁ _) · ε₁ xx
      =
      # L₂ (τ (R₁ xx)) · (ψ₂ (F (R₁ xx)) · ε₁ xx).
  Proof.
    rewrite dual_left_beck_chevalley_nat_trans_ob.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply (nat_trans_ax ψ₂ _ _ (# F (ψ₁ (R₁ xx)))).
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !functor_comp.
    refine (!(functor_comp _ _ _) @ _).
    apply maponpaths.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (nat_trans_ax τ).
    }
    refine (_ @ id_left _).
    rewrite !assoc.
    apply maponpaths_2.
    refine (!(functor_comp _ _ _) @ _ @ functor_id _ _).
    apply maponpaths.
    apply (pr222 S₁).
  Qed.

  Lemma dual_left_beck_chevalley_nat_trans_ob_alt'
        (xx : D[{x}])
    : #H(φ₁(R₂(K xx))) · τ(L₁(R₂(K xx)))
      =
      φ₂ _ · #K(ℓ(R₂(K xx))).
  Proof.
    rewrite dual_left_beck_chevalley_nat_trans_ob'.
    refine (!_).
    rewrite !functor_comp.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax φ₂).
    }
    cbn.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax φ₂).
    }
    cbn.
    refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    apply (pr222 S₂).
  Qed.

  Definition right_from_left_beck_chevalley_inv
             (xx : D[{x}])
    : R₂(K xx) --> G(R₁ xx)
    := φ₁ _ · #G(η₁ _ · #R₁(ℓi _ · #L₂(ε₂ _) · ψ₂ _)).

  Proposition right_from_left_beck_chevalley_inverses
              (xx : D[{x}])
    : is_inverse_in_precat
        (ρ xx)
        (right_from_left_beck_chevalley_inv xx).
  Proof.
    unfold right_from_left_beck_chevalley_inv.
    split.
    - rewrite !functor_comp.
      rewrite !assoc'.
      etrans.
      {
        rewrite !assoc.
        do 4 apply maponpaths_2.
        apply (nat_trans_ax φ₁ _ _ (ρ xx)).
      }
      cbn.
      rewrite !assoc'.
      refine (_ @ pr222 S₁ _).
      apply maponpaths.
      rewrite <- !functor_comp.
      apply maponpaths.
      cbn.
      assert ((pr212 S₁) (R₁ xx) = ψ₁ (R₁ xx)) as q.
      {
        apply idpath.
      }
      refine (_ @ !q) ; clear q.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (nat_trans_ax η₁ _ _ (#L₁ (ρ xx))).
      }
      cbn.
      rewrite !assoc'.
      rewrite <- functor_comp.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply (nat_trans_ax ℓi _ _ (ρ xx)).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- functor_comp.
        apply maponpaths.
        rewrite dual_right_beck_chevalley_nat_trans_ob.
        rewrite !functor_comp.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite <- !functor_comp.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            refine (!_).
            apply (functor_comp R₂).
          }
          apply (nat_trans_ax ε₂ _ _).
        }
        cbn.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply (pr122 P₂).
      }
      cbn.
      rewrite id_left.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite functor_comp.
        rewrite !assoc'.
        apply maponpaths.
        apply (nat_trans_ax ψ₂).
      }
      cbn.
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        apply dual_left_beck_chevalley_nat_trans_ob_alt.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        exact (z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso ℓ_iso (G(R₁ xx)))).
      }
      rewrite id_left.
      rewrite functor_comp.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (nat_trans_ax η₁).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (pr222 P₁).
      }
      apply id_right.
    - cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply functor_comp.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply (nat_trans_ax ρ).
      }
      cbn.
      rewrite dual_right_beck_chevalley_nat_trans_ob.
      etrans.
      {
        rewrite !assoc.
        do 3 apply maponpaths_2.
        apply (nat_trans_ax η₂ _ _ (_ · #G(η₁(L₁(R₂(K xx)))))).
      }
      cbn.
      refine (_ @ pr222 P₂ _).
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !functor_comp.
      apply maponpaths.
      cbn.
      assert ((pr212 P₂) (K xx) = ε₂(K xx)) as q.
      {
        apply idpath.
      }
      refine (_ @ !q) ; clear q.
      etrans.
      {
        apply maponpaths_2.
        apply functor_comp.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (nat_trans_ax τ).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite <- functor_comp.
        apply maponpaths.
        rewrite !assoc.
        do 3 apply maponpaths_2.
        apply (pr122 P₁).
      }
      rewrite id_left.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply dual_left_beck_chevalley_nat_trans_ob_alt'.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (!(functor_comp K _ _) @ _).
        apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso ℓ_iso (R₂(K xx)))).
      }
      rewrite id_left.
      rewrite functor_comp.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (nat_trans_ax φ₂).
      }
      cbn.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (pr222 S₂).
  Qed.

  Definition right_from_left_beck_chevalley
    : right_beck_chevalley HD f g h k p P₁ P₂.
  Proof.
    intros xx.
    use make_is_z_isomorphism.
    - exact (right_from_left_beck_chevalley_inv xx).
    - exact (right_from_left_beck_chevalley_inverses xx).
  Defined.
End DualBeckChevalley.
