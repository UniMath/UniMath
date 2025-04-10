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

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.exponentials.

Local Open Scope cat.

Section PrelimProducts.
  (* This section has to be moved to Limits.BinProducts.v *)

  Definition BinProductOfIsos'
    {C : category}
    {x x' y y' : C}
    (P' : BinProduct _ x' y')
    (P : BinProduct _ x y)
    {fx : C⟦x, x'⟧} {fy : C⟦y, y'⟧}
    (i_fx : is_z_isomorphism fx) (i_fy : is_z_isomorphism fy)
    : is_z_isomorphism (BinProductOfArrows _ P' P fx fy).
  Proof.
    set (f_x_i := make_z_iso' _ i_fx).
    set (f_y_i := make_z_iso' _ i_fy).

    use make_is_z_isomorphism.
    { exact (BinProductOfArrows _ _ _ (z_iso_inv f_x_i) (z_iso_inv f_y_i)). }
    exact (binproduct_of_z_iso_inv P P' f_x_i f_y_i).
  Defined.

  Definition BinProductOfIsos
    {C : category} (P : BinProducts C)
    {x x' y y' : C} {fx : C⟦x, x'⟧} {fy : C⟦y, y'⟧}
    (i_fx : is_z_isomorphism fx) (i_fy : is_z_isomorphism fy)
    : is_z_isomorphism (BinProductOfArrows _ (P x' y') (P x y) fx fy).
  Proof.
    set (f_x_i := make_z_iso' _ i_fx).
    set (f_y_i := make_z_iso' _ i_fy).

    use make_is_z_isomorphism.
    { exact (BinProductOfArrows _ _ _ (z_iso_inv f_x_i) (z_iso_inv f_y_i)). }
    exact (binproduct_of_z_iso_inv (P x y) (P x' y') f_x_i f_y_i).
  Defined.

End PrelimProducts.

Section IsExponentiableCharacterization.
  (* This section has to be moved to CategoryTheory.exponentials.v *)
  (* Some renaming is also appropriate *)

  Context (C : category) (P : BinProducts C).

  (* (e,ev) satisfies the universal property of the exponential [x, y] *)
  Definition is_exponentiable_alt_uvp
    (x y e : C) (ev : C⟦P x e, y⟧)
    : UU
    := ∏ (a : C) (f : C⟦P x a, y⟧),
      ∃! f' : C⟦a, e⟧,
        f = BinProductOfArrows C (P _ _) (P _ _)
              (identity x) f' · ev.

  (* Evaluation map + universal property *)
  Definition is_exponentiable_alt_mor
    (x y e : C) : UU
    := ∑ (ev : C⟦P x e, y⟧), is_exponentiable_alt_uvp x y e ev.

  (* The existence of the exponential [x,y] *)
  Definition is_exponentiable_alt_struct (x y : C) : UU
    := ∑ e : C, is_exponentiable_alt_mor x y e.

  (* The existence of exponentials [x, -] *)
  Definition is_exponentiable_alt (x : C) : UU
    := ∏ (y : C), is_exponentiable_alt_struct x y.

  (* Rename: proof that the unique maps (associated to the evaluation) compose to the identity *)
  Lemma bl
    {x y e e' : C}
    {ev : C ⟦ P x e, y ⟧}
    {ev' : C ⟦ P x e', y ⟧}
    (ev_uvp : is_exponentiable_alt_uvp x y e ev)
    (ev'_uvp : is_exponentiable_alt_uvp x y e' ev')
    : pr1 (iscontrpr1 (ev'_uvp e ev)) · pr1 (iscontrpr1 (ev_uvp e' ev')) = identity e.
  Proof.
    refine (_ @ idpath (pr1 (iscontrpr1 (ev_uvp e ev))) @ _).
    - use (base_paths _ _ (pr2 (ev_uvp e ev) (_ ,, _))).
      simpl.
      etrans.
      2: {
        apply maponpaths_2.
        apply BinProductOfArrows_idxcomp.
      }
      rewrite assoc'.
      etrans.
      2: {
        apply maponpaths.
        apply (pr21 (ev_uvp _ _)).
      }
      apply (pr21 (ev'_uvp _ _)).
    - use (! base_paths _ _ (pr2 (ev_uvp e ev) (_ ,, _))).
      refine (! id_left _ @ _).
      apply maponpaths_2.
      apply pathsinv0, BinProductOfArrows_id.
  Qed.

  Lemma exponentials_unique_up_to_iso
    {x y : C} {e e' : C}
    {ev : C⟦P x e, y⟧} {ev' : C⟦P x e', y⟧}
    (ev_uvp : is_exponentiable_alt_uvp x y e ev)
    (ev'_uvp : is_exponentiable_alt_uvp x y e' ev')
    : z_iso e e'.
  Proof.
    use make_z_iso.
      - exact (pr1 (iscontrpr1 (ev'_uvp e ev))).
      - exact (pr1 (iscontrpr1 (ev_uvp e' ev'))).
      - split ; apply bl.
  Defined.

  Lemma isaprop_is_exponentiable_alt_mor (x y e: C)
    : isaprop (is_exponentiable_alt_mor x y e).
  Proof.
    use isaproptotal2.
    {
      intro ev ; do 2 (apply impred_isaprop ; intro) ; apply isapropiscontr.
    }
    intros ev ev' ev_uvp ev'_uvp.
    unfold is_exponentiable_alt_uvp in ev_uvp.
  Admitted.

  Lemma isaprop_is_exponentiable_alt_struct (C_univ : is_univalent C) (x y : C)
      : isaprop (is_exponentiable_alt_struct x y).
    Proof.
      use isaproptotal2.
      { intro ; apply isaprop_is_exponentiable_alt_mor. }
      intros e e' [ev ev_uvp] [ev' ev'_uvp].
      use isotoid.
      { exact C_univ. }
      exact (exponentials_unique_up_to_iso ev_uvp ev'_uvp).
    Qed.

    Lemma is_exponentiable_alt_to_is_exponentiable (x : C)
      : is_exponentiable_alt x → is_exponentiable P x.
    Proof.
      intro e.
      use left_adjoint_from_partial.
      - exact (λ y, pr1 (e y)).
      - exact (λ y, pr12 (e y)).
      - intro ; intro ; intros ; apply (pr22 (e _)).
    Defined.

    Lemma is_exponentiable_to_is_exponentiable_alt (x : C)
      : is_exponentiable P x → is_exponentiable_alt x.
    Proof.
      intros e y.
      simple refine (_ ,, _ ,, _).
      - exact (exp e y).
      - exact (exp_eval e y).
      - set (l := left_adjoint_to_adjunction e).
        set (ll := make_are_adjoints _ _ _ _ (pr2 l)).
        set (lw := nathomweq_from_adj ll).
        intros a f.
        set (lww := pr2 (invweq (hom_weq lw)) f).
        use (iscontrweqb' lww).
        use weqfibtototal.
        intro g.
        apply weqpathsinv0.
    Defined.

    (* We have maps back and forth, not yet shown that they are inverses of eachother *)

End IsExponentiableCharacterization.

Section PreservationExponentialObjects.

  Definition preserves_exponential_objects
    {C₀ C₁ : category} (F : functor C₀ C₁)
    (P₀ : BinProducts C₀) (P₁ : BinProducts C₁)
    : UU
    := ∏ x : C₀, is_exponentiable P₀ x → is_exponentiable P₁ (F x).

  Lemma preserves_exponential_objects_to_preserves_exponentials
    {C₀ C₁ : category} (F : functor C₀ C₁)
    (P₀ : BinProducts C₀) (P₁ : BinProducts C₁)
    (E₀ : Exponentials P₀) (E₁ : Exponentials P₁) (F_pP : preserves_binproduct F)
    : preserves_exponential_objects F P₀ P₁ → preserves_exponentials E₀ E₁ F_pP.
  Proof.
    intro F_pE.
    intros x y.
    set (ex := F_pE _ (E₀ x)).
    (* follows since both the domain and codomain witness exponentiability *)
  Admitted.

End PreservationExponentialObjects.

Section WeakEquivalencesPreserveExponentialObjects.

  Context {C₀ C₁ : category}
    {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
    (C₁_univ : is_univalent C₁)
    (P₀ : BinProducts C₀).

  Let P₁ := weak_equiv_into_univ_creates_binproducts C₁_univ F_weq P₀.

  Section ImageOfExponentialIsExponent.

    Context {x₀ : C₀}
      (ex₀ : is_exponentiable P₀ x₀)
      {y₁ : C₁} {y₀ : C₀}
      (iy : z_iso (F y₀) y₁).

    Let p : BinProduct C₁ (F x₀) (F (exp ex₀ y₀))
        := make_BinProduct _ _ _ _ _ _
             (weak_equiv_preserves_binproducts F_weq _ _ _ _ _ (pr2 (P₀ x₀ (exp ex₀ y₀)))).

    Let ev_ : C₁ ⟦P₁ (F x₀) (F (exp ex₀ y₀)), y₁⟧
        := iso_between_BinProduct (P₁ _ _) p · #F (exp_eval ex₀ y₀) · iy.

    Section ImageOfExponentiableIsExponentUVP.

      Context {a₁ : C₁}
        {a₀ : C₀}
        (ia : z_iso (F a₀) a₁)
        (f₁ : C₁⟦P₁ (F x₀) a₁, y₁⟧).

      Let P_Fx_Fa := (make_BinProduct _ _ _ _ _ _
                        (weak_equiv_preserves_binproducts F_weq _ _ _ _ _ (pr2 (P₀ x₀ a₀)))).

      Let i_FPxa_PFxA : z_iso (F (P₀ x₀ a₀)) (P₁ (F x₀) a₁).
      Proof.
        exists (BinProductOfArrows _ (P₁ (F x₀) a₁) P_Fx_Fa (identity _) ia).
        exact (BinProductOfIsos' (P₁ _ _) P_Fx_Fa (identity_is_z_iso (F x₀)) (pr2 ia)).
      Defined.

      Local Lemma is_z_iso_BPA
        : is_z_isomorphism (BinProductOfArrows C₁ (P₁ (F x₀) (F a₀)) (P₁ (F x₀) a₁) (identity (F x₀)) (z_iso_inv ia)).
      Proof.
        use BinProductOfIsos.
        - apply identity_is_z_iso.
        - apply z_iso_inv.
      Defined.
      Definition i_PFxA_PFxFa : z_iso (P₁ (F x₀) a₁) (P₁ (F x₀) (F a₀))
        := make_z_iso _ _ (is_z_iso_BPA).

      Let f₁_mod_iso : C₁⟦F (P₀ x₀ a₀), F y₀⟧
          := i_FPxa_PFxA · f₁ · z_iso_inv iy.

      Let f₀ : C₀⟦P₀ x₀ a₀, y₀⟧
          := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ f₁_mod_iso.

      Local Lemma Ff₀ : #F f₀ = f₁_mod_iso.
      Proof.
        apply functor_on_fully_faithful_inv_hom.
      Qed.

      Let f₁_curry : C₁⟦a₁, F (exp ex₀ y₀)⟧.
      Proof.
        refine (z_iso_inv ia · #F _).
        use exp_lam.
        exact f₀.
      Defined.

      Lemma image_of_exp_uvp_existence_commutation
        : f₁ = BinProductOfArrows C₁ (P₁ (F x₀) (F (exp ex₀ y₀))) (P₁ (F x₀) a₁)
                 (identity (F x₀)) f₁_curry · ev_.
      Proof.
        unfold f₁_curry, ev_.
        set (pf := maponpaths #F (exp_app_lam ex₀ f₀)).
        rewrite Ff₀ in pf.
        unfold f₁_mod_iso in pf.
        rewrite <- BinProductOfArrows_idxcomp.
        rewrite assoc'.
        use (z_iso_inv_to_left _ _ _ (_ ,, is_z_iso_BPA)).
        rewrite ! assoc.
        apply pathsinv0.
        use z_iso_inv_to_right.
        cbn.

        (* We want to start from (F (P₀ x₀ a₀)) *)
        use (cancel_z_iso' i_PFxA_PFxFa).
        use (cancel_z_iso' i_FPxa_PFxA).
        refine (_ @ pf @ _).
        (* (* P₁ and F(P₀) are not definitionally equal.. *) *)
        -
      Admitted.

      Lemma image_of_exp_uvp_uniqueness
        : isaprop (∑ f' : C₁ ⟦ a₁, F (exp ex₀ y₀) ⟧,
                f₁ = BinProductOfArrows C₁ (P₁ (F x₀) (F (exp ex₀ y₀))) (P₁ (F x₀) a₁) (identity (F x₀)) f' · ev_).
      Proof.
      Admitted.

      Lemma image_of_exp_uvp
        : ∃! f' : C₁ ⟦ a₁, F (exp ex₀ y₀) ⟧,
            f₁ = BinProductOfArrows C₁ (P₁ (F x₀) (F (exp ex₀ y₀))) (P₁ (F x₀) a₁)
                   (identity (F x₀)) f' · ev_.
      Proof.
        use iscontraprop1.
        { exact image_of_exp_uvp_uniqueness. }
        exists f₁_curry.
        exact image_of_exp_uvp_existence_commutation.
      Defined.

    End ImageOfExponentiableIsExponentUVP.

    Lemma image_of_chosen_exp_is_exponentiable
      : is_exponentiable_alt_mor C₁ P₁ (F x₀) y₁ (F (exp ex₀ y₀)).
    Proof.
      use tpair.
      - exact ev_.
      - intros a₁.
        use (factor_through_squash _ _ (pr1 F_weq a₁)).
        { intro ; apply impred_isaprop ; intro ; apply isapropiscontr. }
        intros [a₀ ia].
        intro f₁.
        exact (image_of_exp_uvp ia f₁).
    Defined.

  End ImageOfExponentialIsExponent.

  Proposition weak_equiv_preserves_exponential_objects
    : preserves_exponential_objects F P₀ P₁.
  Proof.
    intros x₀ ex₀.
    use is_exponentiable_alt_to_is_exponentiable.
    intro y₁.
    use (factor_through_squash _ _ (pr1 F_weq y₁)).
    { intro ; apply isaprop_is_exponentiable_alt_struct.
      exact C₁_univ. }
    intros [y₀ iy].

    exists (F (exp ex₀ y₀)).
    apply image_of_chosen_exp_is_exponentiable.
    exact iy.
  Defined.

End WeakEquivalencesPreserveExponentialObjects.

Section IsExponentiableAltTransportAlongIso.

  Context {C : category} (P : BinProducts C)
    {x x' : C} (i : z_iso x x').

  Context (e : is_exponentiable_alt _ P x).

  Let ev (y : C) : C⟦P x' (pr1 (e y)), y⟧
      :=  BinProductOfArrows C (P x (pr1 (e y))) (P x' (pr1 (e y)))
            (z_iso_inv i) (identity (pr1 (e y)))
            · pr12 (e y).

  Local Lemma equiv_of_mor
    {y a : C}
    (f : C⟦P x' a, y⟧)
    (g : C⟦a, pr1 (e y)⟧)
    : (f = BinProductOfArrows C (P x' (pr1 (e y))) (P x' a) (identity x') g · ev y)
        ≃ (BinProductOfArrows C (P x' a) (P x a) i (identity a) · f
           = BinProductOfArrows C (P x (pr1 (e y))) (P x a) (identity x) g · pr12 (e y)).
  Proof.
    use weqimplimpl.
    - intro pf.
      simpl in pf.
      etrans. {
        apply maponpaths.
        exact pf.
      }
      unfold ev.
      rewrite ! assoc.
      etrans. {
        do 2 apply maponpaths_2.
        apply BinProductOfArrows_comp.
      }
      etrans. {
        apply maponpaths_2.
        apply BinProductOfArrows_comp.
      }
      apply maponpaths_2.
      rewrite ! id_left.
      rewrite ! id_right.
      now rewrite z_iso_inv_after_z_iso.
    - (* This could be cleaned up by having a lemma about the bin product of isomorphisms, and then apply cancel_z_iso *)
      intro pf.
      unfold ev.
      rewrite assoc.
      rewrite BinProductOfArrows_comp.
      apply pathsinv0.
      etrans. {
        apply maponpaths_2, maponpaths.
        refine (id_right _ @ _).
        exact (! id_left _).
      }
      etrans. {
        do 2 apply maponpaths_2.
        refine (id_left _ @ _).
        exact (! id_right _).
      }
      rewrite <- BinProductOfArrows_comp.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        exact (! pf).
      }
      rewrite assoc.
      rewrite BinProductOfArrows_comp.
      rewrite id_right.
      rewrite z_iso_inv_after_z_iso.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply BinProductOfArrows_id.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Lemma is_exponentiable_alt_closed_under_iso
    : is_exponentiable_alt _ P x'.
  Proof.
    intro y.
    exists (pr1 (e y)).
    exists (ev y).
    intros a f.
    use (iscontrweqb' (pr22 (e y) a (_ · f))).
    - apply BinProductOfArrows.
      + exact i.
      + apply identity.
    - use weqfibtototal ; intro ; apply equiv_of_mor.
  Defined.

End IsExponentiableAltTransportAlongIso.

Section WeakEquivalencesIntoUnivalentCatsCreatesExponentials.

  Context {C₀ C₁ : category}
    {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
    (C₁_univ : is_univalent C₁)
    (P₀ : BinProducts C₀)
    (E₀ : Exponentials P₀).

  Let P₁ := weak_equiv_into_univ_creates_binproducts C₁_univ F_weq P₀.

  Lemma weak_equiv_into_univ_creates_exponentials
    : Exponentials P₁.
  Proof.
    intro x₁.
    use is_exponentiable_alt_to_is_exponentiable.
    use (factor_through_squash _ _ (pr1 F_weq x₁)).
    {
      apply impred_isaprop ; intro.
      use isaprop_is_exponentiable_alt_struct.
      exact C₁_univ.
    }
    intros [x₀ ix].
    apply (is_exponentiable_alt_closed_under_iso _ ix).
    use is_exponentiable_to_is_exponentiable_alt.
    use (weak_equiv_preserves_exponential_objects F_weq C₁_univ P₀).
    apply E₀.
  Defined.

  Lemma weak_equiv_into_univ_creates_exponentials'
    (Q₁ : BinProducts C₁)
    : Exponentials Q₁.
  Proof.
    exact (exponentials_independent P₁ Q₁ weak_equiv_into_univ_creates_exponentials).
  Defined.

End WeakEquivalencesIntoUnivalentCatsCreatesExponentials.

Section WeakEquivalencesReflectExponentials.
  (* TODO *)
End WeakEquivalencesReflectExponentials.

Section WeakEquivalencesLiftPreserveExponentials.
  (* TODO *)
End WeakEquivalencesLiftPreserveExponentials.
