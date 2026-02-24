
(*
  Constructing a CwF from a Comprehension Category with a Universe

  In this file, we construct a CwF from a comprehension category with a universe (U,el) which is closed under sigma and unit types.
  Briefly, this construction is as follows:
  - The contexts of the target CwF are terms of type U in the empty context of the comp cat.
  - The morphisms from context Γ to context Δ in the CwF are context morphisms of the form [].el(Γ) ➜ [].el(Δ) in the comp cat making
    the usual triangle commute.
  - The terminal context is given by the unit code of the universe in the comp cat.
  - The types in the target CwF are terms of type U in the context [].(el Γ) of the comp cat.
  - Context extension is given by the sigma code of the universe in the comp cat.

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Core.Setcategories.


Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.

Require Import UniMath.CategoryTheory.ComprehensionCats.CompCats.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatTypeFormers.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatUniverse.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFams.


Local Open Scope cat.
Local Open Scope comp_cat.

Section Construction.

  Context (C : comp_cat_with_universe) (Sigma : comp_cat_sigma C) (SigmaU : comp_cat_universe_closed_sigma C Sigma)
    (Unit : comp_cat_unit C) (UnitU : comp_cat_universe_closed_unit C Unit).

  (* the object are terms of type U *)
  Definition context_from_comp_cat_with_u : UU :=
    (comp_cat_tm [] (weakened_from_empty (comp_cat_U C) _)).

  Definition substitution_from_comp_cat_with_u :
    context_from_comp_cat_with_u -> context_from_comp_cat_with_u -> UU.
  Proof.
    (* the morphisms from Γ to Δ are context morphisms s : [].el(Γ) to [].el(Δ)
          in the comprehension category such that s ; π_Δ  = π_Γ *)
    intros Γ Δ.
    set (el := comp_cat_El C).
    set (U := comp_cat_morphisms _ ([] & (comp_cat_El _ _ Γ)) ([] & (comp_cat_El _ _ Δ))).
    exact (∑ s : U , s · (π (el _ Δ)) = (π (el _ Γ))).
  Defined.

  Coercion morphism_from_substitution_from_comp_cat_with_u {Γ Δ : context_from_comp_cat_with_u}
    {s : substitution_from_comp_cat_with_u Γ Δ}
    : ([] & (comp_cat_El _  _ Γ)) --> ([] & (comp_cat_El _  _ Δ))
    := pr1 s.

  Definition ob_mor_from_comp_cat_with_u :=
    make_precategory_ob_mor context_from_comp_cat_with_u substitution_from_comp_cat_with_u.

  Coercion ob_from_ob_mor_from_comp_cat_with_u {C : ob_mor_from_comp_cat_with_u} := pr1 C.

  Definition precategory_data_context_from_comp_cat_with_u : precategory_data.
  Proof.
    use make_precategory_data.
    - exact ob_mor_from_comp_cat_with_u.
    - (* identity *)
      intro Γ.
      use tpair.
      + exact (identity ([] & (comp_cat_El _ _ Γ))).
      + abstract (apply id_left).
    - (* composition *)
      intros Γ Δ Θ f g.
      use tpair.
      + exact (pr1 f · pr1 g).
      + abstract (
            eapply pathscomp0;
            [apply assoc'
            | eapply pathscomp0;
              [ apply cancel_precomposition;
                apply (pr2 g)
              | apply (pr2 f) ] ] ).
  Defined.

  Definition is_precategory_context_from_comp_cat_with_u : is_precategory precategory_data_context_from_comp_cat_with_u.
  Proof.
    do 2 split ; intros ; use subtypePath.
    1 , 3 , 5, 7:  unfold isPredicate; intros; apply (homset_property (pr1 C)).
    - apply (id_left (pr1 f)).
    - apply id_right.
    - apply (assoc (pr1 f) (pr1 g) (pr1 h)).
    - apply (assoc' (pr1 f) (pr1 g) (pr1 h)).
  Qed.

  Definition cwf_context_precategory_from_comp_cat_with_u : precategory :=
    (precategory_data_context_from_comp_cat_with_u ,, is_precategory_context_from_comp_cat_with_u).

  Definition is_category_context_from_comp_cat_with_u : has_homsets cwf_context_precategory_from_comp_cat_with_u.
  Proof.
    Admitted.

  Definition cwf_context_from_comp_cat_with_u : category :=
    (cwf_context_precategory_from_comp_cat_with_u ,, is_category_context_from_comp_cat_with_u).

  Definition cwf_terminal_from_comp_cat_with_u : Terminal (cwf_context_from_comp_cat_with_u).
  Proof.
    (* The terminal context is given by the code of the unit in the universe *)
    set (unit_code := pr1 UnitU []).
    set (U := comp_cat_U C).
    set (el := comp_cat_El C).
    set (unit_el_iso := pr12 UnitU).
    set (unit_iso := pr122 (pr222 Unit)).
    set (unit := (pr1 Unit)).
    set (tt := (pr12 Unit)).

    use tpair.
    - exact (unit_code).
    - intro Γ.
      set (tm_unit_code := term_unit_code C Unit UnitU []).
      use tpair.
      + (* The terminal map is given by precomposing pi with the unique term of the unit code *)
        use tpair.
        *  exact (π (el _ Γ) · tm_unit_code).
        * (* proof that it is a section *)
          abstract (
              cbn;
              rewrite <- (assoc4 _ _ _ _ _ _ (π (el [] Γ)) _ _ (π (comp_cat_El C [] unit_code)));
              repeat rewrite <- assoc;
              rewrite comp_cat_comp_mor_law;
              rewrite <- id_right;
              apply cancel_precomposition;
              exact (pr2 ((pr12 Unit) []))
                    ).
      + (* Uniqueness using the universal property of the pullback that is given by pulling back
            π (el unit_code) along π (el Γ) precomposed with an isomorphism
           and uniqueness of tt *)
        cbn; intro s;
          use subtypePath; [unfold isPredicate; intros; apply (homset_property C) |cbn ].
        set (u := π (el [] Γ) · ((pr12 Unit) [] · comp_cat_comp_mor (⌈ (pr12 UnitU) [] ⌉⁻¹))).
        assert (i' : @z_iso
                      (fiber_category _ _ )
                      (unit ([] & (el _ Γ))) ((el _ unit_code) [[ π (el _ Γ) ]] )).
        {
          refine (z_iso_comp _ (z_iso_inv (comp_cat_reindex_iso _ (unit_el_iso _)))).
          exact (z_iso_inv (unit_iso _ _ _)).
        }
        assert (p : ∏ {Γ Δ : C} (A : comp_cat_ty Δ) (s : Γ --> Δ),
                   PullbackObject (comp_cat_pullback A s)
                   = Γ & (A [[ s ]]) ) by (intros; apply idpath).
        set (i := transportf _ (p _ _ _ _) (comp_cat_comp_iso i')).
        set (PB := comp_cat_pullback_compose_iso (π (el [] Γ)) i).
        assert (p_u : identity ([] & el [] Γ) · u · π (el [] unit_code) = π (el [] Γ)).
        {
          rewrite <- assoc; rewrite id_left.
          unfold u.
          rewrite <- assoc4.
          repeat rewrite <- assoc.
          rewrite comp_cat_comp_mor_law.
          rewrite <- id_right.
          apply cancel_precomposition.
          exact (pr2 (tt [])).
        }
        assert (p_s :  identity ([] & el [] Γ) · s · π (el [] unit_code) = π (el [] Γ))
          by (rewrite <- assoc; rewrite id_left; exact (pr2 s)).
        set (univ_u := comp_cat_univ_pullback_compose_iso (π (el [] Γ)) i' (identity _) u p_u).
        set (univ_s := comp_cat_univ_pullback_compose_iso (π (el [] Γ)) i' (identity _) s p_s).
        assert (unit_code_term_eq' : (univ_s) = (univ_u)).
        {
          set (unique := pr12 (pr222 Unit)).
          etrans.
          exact (unique _ univ_s).
          exact (!(unique _ univ_u)).
        }
        set (H := maponpaths pr1 unit_code_term_eq').
        cbn in H.
        unfold isPullback_z_iso_mor in H.
        apply (post_comp_with_z_iso_is_inj (z_iso_inv (comp_cat_comp_iso i'))) in H.
        set (PB0 := make_Pullback
                      (PullbackSqrCommutes (comp_cat_pullback (el [] unit_code) (π (el [] Γ))))
                      (comp_cat_is_pullback (el [] unit_code) (π (el [] Γ)))).
        set (pr1eq := maponpaths (fun t => t · PullbackPr1 PB0) H).
        cbn in pr1eq.
        repeat rewrite (PullbackArrow_PullbackPr1 PB0) in pr1eq.
        repeat rewrite id_left in pr1eq.
        exact pr1eq.
Defined.

  Definition cwf_ty_from_comp_cat_with_u :  cwf_context_from_comp_cat_with_u → hSet.
  Proof.
    (* types in Γ are tm empty.(el Γ) U*)
    intro Γ.
    use tpair.
    - set (ext := comp_cat_ext (empty_context C) (comp_cat_El C (empty_context C) Γ)).
      set (is_hset := is_category_context_from_comp_cat_with_u).
      exact (comp_cat_tm (ext) (weakened_from_empty (comp_cat_U _) _)).
    - abstract (apply comp_cat_tm_isaset).
  Defined.

  Definition cwf_tm_from_comp_cat_with_u : ∏ Γ : cwf_context_from_comp_cat_with_u,
        cwf_ty_from_comp_cat_with_u Γ → hSet.
  Proof.
    (* tm Γ A is tm (⋄ & el Γ) (el A)*)
    intros Γ A.
    use tpair.
    - set (ext := comp_cat_ext (empty_context C) (comp_cat_El C (empty_context C) Γ)).
      exact (comp_cat_tm (ext) (comp_cat_El _  _ A)).
    - abstract (apply comp_cat_tm_isaset).
  Defined.

  Definition cwf_subst_ty_from_comp_cat_with_u :
    ∏ Γ Δ : cwf_context_from_comp_cat_with_u,
        cwf_context_from_comp_cat_with_u ⟦ Δ, Γ ⟧ → cwf_ty_from_comp_cat_with_u Γ → cwf_ty_from_comp_cat_with_u Δ.
  Proof.
    intros Γ Δ s A.
    (* A is a term of type U in the context ([] & El Γ).
     Substitute it along σ : ([] & El Δ) → ([] & El Γ),
     then coerce along the canonical iso showing U is stable under weakening-from-empty. *)
    exact ( (A [[ (pr1 s) ]]tm) ↑ ⌈sub_comp_cat_univ_iso (comp_cat_U C) (pr1 s)⌉).
  Defined.

  Definition cwf_subst_tm_from_comp_cat_with_u :
    ∏ (Γ Δ : cwf_context_from_comp_cat_with_u)
      (f : cwf_context_from_comp_cat_with_u ⟦ Δ, Γ ⟧)
      (A : cwf_ty_from_comp_cat_with_u Γ),
      cwf_tm_from_comp_cat_with_u Γ A →
      cwf_tm_from_comp_cat_with_u Δ (cwf_subst_ty_from_comp_cat_with_u Γ Δ f A).
  Proof.
  intros Γ Δ f A t.
  refine ( (t [[ (pr1 f) ]]tm) ↑ _ ).
  (* now we need a coercion along the universe substitution iso:
     (El A)[f]  ≃  El(A[f])  *)
  exact (pr2 (pr212 C) ([] & comp_cat_El C [] Δ)
             ([] & comp_cat_El C [] Γ) (pr1 f) A : _ --> _).
  Defined.


  Definition cwf_id_ty_from_comp_cat_with_u :   ∏ (Γ : cwf_context_from_comp_cat_with_u) (A : cwf_ty_from_comp_cat_with_u Γ),
      cwf_subst_ty_from_comp_cat_with_u Γ Γ (identity Γ) A = A.
  Proof.
    Admitted.

  Definition cwf_comp_ty_from_comp_cat_with_u :
  ∏ (Γ Δ Θ : cwf_context_from_comp_cat_with_u) (g : cwf_context_from_comp_cat_with_u ⟦ Θ, Δ ⟧)
  (f : cwf_context_from_comp_cat_with_u ⟦ Δ, Γ ⟧) (A : cwf_ty_from_comp_cat_with_u Γ),
      cwf_subst_ty_from_comp_cat_with_u Γ Θ (g · f) A = cwf_subst_ty_from_comp_cat_with_u Δ Θ g (cwf_subst_ty_from_comp_cat_with_u Γ Δ f A).
  Proof.
  Admitted.

  Definition cwf_id_tm_from_comp_cat_with_u :
  ∏ (Γ : cwf_context_from_comp_cat_with_u) (A : cwf_ty_from_comp_cat_with_u Γ) (t : cwf_tm_from_comp_cat_with_u Γ A),
  transportf (λ A0 : cwf_ty_from_comp_cat_with_u Γ, cwf_tm_from_comp_cat_with_u Γ A0) (cwf_id_ty_from_comp_cat_with_u Γ A)
    (cwf_subst_tm_from_comp_cat_with_u Γ Γ (identity Γ) A t) =
    t.
  Proof.
  Admitted.

  Definition cwf_comp_tm_from_comp_cat_with_u :
    ∏ (Γ Δ Θ : cwf_context_from_comp_cat_with_u)
      (g : cwf_context_from_comp_cat_with_u ⟦ Θ, Δ ⟧)
      (f : cwf_context_from_comp_cat_with_u ⟦ Δ, Γ ⟧)
      (A : cwf_ty_from_comp_cat_with_u Γ) (t : cwf_tm_from_comp_cat_with_u Γ A),
      transportf (λ A0 : cwf_ty_from_comp_cat_with_u Θ, cwf_tm_from_comp_cat_with_u Θ A0)
        (cwf_comp_ty_from_comp_cat_with_u Γ Δ Θ g f A)
        (cwf_subst_tm_from_comp_cat_with_u Γ Θ (g · f) A t) =
        cwf_subst_tm_from_comp_cat_with_u Δ Θ g
          (cwf_subst_ty_from_comp_cat_with_u Γ Δ f A)
          (cwf_subst_tm_from_comp_cat_with_u Γ Δ f A t).
Proof.
Admitted.

  Definition  cwf_ctx_ext_from_comp_cat_with_u : cwf_ctx_ext
    (make_cwf_ty_term_subst cwf_ty_from_comp_cat_with_u cwf_tm_from_comp_cat_with_u cwf_subst_ty_from_comp_cat_with_u cwf_subst_tm_from_comp_cat_with_u
       cwf_id_ty_from_comp_cat_with_u cwf_comp_ty_from_comp_cat_with_u cwf_id_tm_from_comp_cat_with_u cwf_comp_tm_from_comp_cat_with_u).
  Proof.
    (* This one requires having sigma types and the universe being closed by them. *)
    intros Γ A.
    use tpair.
    - (* the extended context Γ.A is the sigma type Σ(Γ,A) in the comprehension category  *)
      exact (pr1 SigmaU _ Γ A).
    - set (iso := (pr1 (pr2 SigmaU) _ Γ A)).
      set (el := comp_cat_El C).
      set (ctxextproj := (comp_cat_comp_mor (⌈ iso ⌉)) · (comp_cat_sigma_proj_1 _ Sigma (el _ Γ) (el _ A))).
      use tpair.
      + (* the projection Γ.A -> Γ is the composition of χ_0(i_Σ(Γ,A)) with χ_0(π_1)
            where π_1 is the first projection in the comprehension category *)
        use tpair.
        * exact ctxextproj.
        * cbn.
          unfold ctxextproj.
          eapply pathscomp0; [ apply assoc' | ].
          rewrite comp_cat_sigma_proj_1_law.
          rewrite comp_cat_comp_mor_law.
          apply idpath.
      + (* The term q  *)
        set (sigmaproj := pr1 (pr222 Sigma)).
        set (i := comp_cat_El_iso C ([] & comp_cat_El C [] (pr1 SigmaU [] Γ A))
                    ([] & el [] Γ) ctxextproj A).
        refine ((comp_cat_univ_pullback ctxextproj (comp_cat_comp_mor (⌈ iso ⌉))
                       (sigmaproj [] (el [] Γ) (el ([] & comp_cat_El C [] Γ) A)) _) ↑ ⌈ i ⌉).
        rewrite assoc'.
        apply maponpaths.
        apply idpath.
  Defined.

  Definition cwf_data_from_comp_cat_with_u : cwf_data.
  Proof.
    use make_cwf_data.
    - exact cwf_context_from_comp_cat_with_u.
    - exact cwf_terminal_from_comp_cat_with_u.
    - use make_cwf_ty_term_subst.
      + exact cwf_ty_from_comp_cat_with_u.
      + exact cwf_tm_from_comp_cat_with_u.
      + exact cwf_subst_ty_from_comp_cat_with_u.
      + exact cwf_subst_tm_from_comp_cat_with_u.
      + exact cwf_id_ty_from_comp_cat_with_u.
      + exact cwf_comp_ty_from_comp_cat_with_u.
      + exact cwf_id_tm_from_comp_cat_with_u.
      + exact cwf_comp_tm_from_comp_cat_with_u.
    - exact cwf_ctx_ext_from_comp_cat_with_u.
  Defined.

  (* Helper lemma for the universal property proof *)
  Lemma qA_subst_helper_lemma
    {Γ Δ : cwf_data_from_comp_cat_with_u}
    (A : cwf_ty (cwf_t cwf_data_from_comp_cat_with_u) Γ)
    (s : cwf_data_from_comp_cat_with_u ⟦ Δ, Γ ⟧)
    (t : cwf_tm (cwf_t cwf_data_from_comp_cat_with_u)
           (cwf_subst_ty (cwf_t cwf_data_from_comp_cat_with_u) s A))
    : let El := comp_cat_El C in
      let Δ' := [] & El [] Δ in
      let Γ' := [] & El [] Γ in
    pr1 t
      · comp_cat_comp_mor (⌈ comp_cat_El_iso C Δ' Γ' (pr1 s) A ⌉⁻¹)
      · comp_cat_ext_subst Γ' Δ' (pr1 s) (El Γ' A)
      · (pr12 Sigma) [] (El [] Γ) (El Γ' A)
      · comp_cat_sigma_proj_1 C Sigma (El [] Γ) (El Γ' A)
      = (pr1 s).
  Proof.
    intros.
    unfold comp_cat_sigma_proj_1.
    set (sig_beta := pr1 (pr222 (pr2 Sigma))).
    rewrite (assoc _ ((pr122 (pr2 Sigma)) [] (comp_cat_El C [] Γ) (comp_cat_El C ([] & comp_cat_El C [] Γ) A)) _).
    rewrite assoc4.
    eapply pathscomp0.
    - apply cancel_postcomposition.
      apply cancel_precomposition.
      apply sig_beta.
    - rewrite id_right.
      rewrite <- (assoc _ _ (π (comp_cat_El C ([] & comp_cat_El C [] Γ) A))).
      rewrite comp_cat_ext_subst_commute.
      rewrite assoc.
      unfold "π".
      rewrite assoc4.
      set (h := comprehension_functor_mor_comm (comp_cat_comprehension C)
                  (identity Δ') (⌈ comp_cat_El_iso C Δ' Γ' (pr1 s) A ⌉⁻¹)).
      eapply pathscomp0.
      ++ apply cancel_postcomposition.
         apply cancel_precomposition.
         exact h.
      ++ rewrite id_right.
         eapply pathscomp0.
         ** apply cancel_postcomposition.
            exact (pr2 t).
         ** apply id_left.
  Qed.

  Definition cwf_universal_property_from_comp_cat_with_u : cwf_universal_property cwf_data_from_comp_cat_with_u.
  Proof.
    intros Γ Δ A s t.
    set (El := comp_cat_El C).
    set (Δ' := ([] & El [] Δ)).
    set (Γ' := ([] & El [] Γ)).
    use tpair.
    - use tpair.
      +
        cbn in t.
        use tpair.
        * refine (t · _).
          refine (comp_cat_comp_mor (⌈ comp_cat_El_iso C Δ' Γ' (pr1 s) A ⌉⁻¹) · _).
          refine (comp_cat_ext_subst (C:=C) Γ' Δ' (pr1 s) (El Γ' A) · _).
          refine (pr12 Sigma [] (El [] Γ) (El Γ' A) · _).
          exact (comp_cat_comp_mor (⌈ pr12 SigmaU [] Γ A ⌉⁻¹)).
        * admit.
      + cbn.
        use tpair.
        * (* u · p_A = s *)
          (* TODO: this ones needs to be abstracted but it failts before homset_property *)
              use subtypePath; unfold isPredicate; intros.
              apply (homset_property (pr1 C)).
              cbn;
              set (j := (pr12 SigmaU) [] Γ A);
              rewrite !assoc;
              rewrite (assoc _ (comp_cat_comp_mor (⌈ j ⌉))
                         (comp_cat_sigma_proj_1 C Sigma (comp_cat_El C [] Γ) (comp_cat_El C ([] & comp_cat_El C [] Γ) A)));
              rewrite assoc4;
              eapply pathscomp0;
              [ apply cancel_postcomposition;
                apply cancel_precomposition;
                apply comp_cat_comp_mor_z_iso_after_z_iso_inv |
                rewrite (id_right _);
                apply qA_subst_helper_lemma].
        * (* t = q_A[u] *)
          set (j := pr12 SigmaU [] Γ A).
          set (u := pr1 t
                      · (comp_cat_comp_mor (⌈ comp_cat_El_iso C Δ' Γ' (pr1 s) A ⌉⁻¹)
                           · (comp_cat_ext_subst Γ' Δ' (pr1 s) (El Γ' A)
                                · ((pr12 Sigma) [] (El [] Γ) (El Γ' A)
                                     · comp_cat_comp_mor (⌈ j ⌉⁻¹))))).
          set (pA := comp_cat_comp_mor (⌈ j ⌉)
                       · comp_cat_sigma_proj_1 C Sigma (El [] Γ) (El Γ' A)).
          assert (p : u · pA = pr1 s). {
              unfold u, pA.
              rewrite !assoc.
              rewrite assoc4.
              eapply pathscomp0.
              - apply cancel_postcomposition.
                apply cancel_precomposition.
                apply (comp_cat_comp_mor_z_iso_after_z_iso_inv j).
              - rewrite id_right.
                exact (qA_subst_helper_lemma A s t).
              }
              cbn.
          use subtypePath; [intro; apply homset_property |].
          admit.
    - (* uniqueness *)
      admit.
    Admitted.

  Definition cwf_from_comp_cat_with_u : cwf.
  Proof.
    use make_cwf.
    - exact cwf_data_from_comp_cat_with_u.
    - exact cwf_universal_property_from_comp_cat_with_u.
  Defined.

End Construction.
