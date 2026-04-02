
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

  Contents:
  1. Type and Terms of the CWF
  2. Terminal Context
  3. Substitutions
  4. Functorialities
  5. Context Extension
  6. Universal Property
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
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

  Context (C : comp_cat_with_universe)
    (Sigma : comp_cat_sigma C)
    (SigmaU : comp_cat_universe_closed_sigma C Sigma)
    (Unit : comp_cat_unit C)
    (UnitU : comp_cat_universe_closed_unit C Unit).

  (** * Type and Terms of the CWF  *)

  (* the object are terms of type U *)
  Definition context_from_comp_cat_with_u : UU :=
    (comp_cat_tm (comp_cat_U ([] : C))).

  (* the morphisms from Γ to Δ are context morphisms s : [].el(Γ) to [].el(Δ) *)
  Definition substitution_from_comp_cat_with_u :
    context_from_comp_cat_with_u -> context_from_comp_cat_with_u -> UU.
  Proof.
    intros Γ Δ.
    exact (comp_cat_morphisms _ ([] & (comp_cat_el Γ)) ([] & (comp_cat_el Δ))).
  Defined.

  Definition ob_mor_from_comp_cat_with_u :=
    make_precategory_ob_mor context_from_comp_cat_with_u substitution_from_comp_cat_with_u.

  Coercion ob_from_ob_mor_from_comp_cat_with_u {C : ob_mor_from_comp_cat_with_u} := pr1 C.

  Definition precategory_data_context_from_comp_cat_with_u : precategory_data.
  Proof.
    use make_precategory_data.
    - exact ob_mor_from_comp_cat_with_u.
    - (* identity *)
      intro Γ.
      exact (identity ([] & (comp_cat_el Γ))).
    - (* composition *)
      intros Γ Δ Θ f g.
      exact (f · g).
  Defined.

  Definition is_precategory_context_from_comp_cat_with_u : is_precategory precategory_data_context_from_comp_cat_with_u.
  Proof.
    do 2 split ; intros.
    - apply id_left.
    - apply id_right.
    - apply assoc.
    - apply assoc'.
  Qed.

  Definition cwf_context_precategory_from_comp_cat_with_u : precategory :=
    (precategory_data_context_from_comp_cat_with_u ,, is_precategory_context_from_comp_cat_with_u).

  Definition is_category_context_from_comp_cat_with_u : has_homsets cwf_context_precategory_from_comp_cat_with_u.
  Proof.
    intros Γ Γ'.
    apply homset_property.
  Qed.

  Definition cwf_context_from_comp_cat_with_u : category :=
    (cwf_context_precategory_from_comp_cat_with_u ,, is_category_context_from_comp_cat_with_u).

  (** *  Terminal Context  *)

  Section Terminal_from_comp_cat_with_u.

    (* The terminal context is the code of unit in the comprehension category. *)

    Let unit_code := comp_cat_unit_code _ _ UnitU.
    Let unit_code_w := (comp_cat_unit_code_weakened C Unit UnitU []).
    Let tm_unit_code := term_unit_code C Unit UnitU [].

  Definition terminal_context : context_from_comp_cat_with_u := unit_code_w.

  Definition terminal_morphism (Γ : context_from_comp_cat_with_u)
    : ([] & (comp_cat_el Γ)) --> ([] & comp_cat_el unit_code_w )
    := π (comp_cat_el Γ) · tm_unit_code.

  Lemma terminal_morphism_is_section (Γ : context_from_comp_cat_with_u)
    : terminal_morphism Γ · (π (comp_cat_el unit_code_w)) = (π (comp_cat_el Γ)).
  Proof.
    cbn.
    unfold terminal_morphism.
    rewrite <- assoc.
    etrans.
    {
      apply maponpaths.
      apply (pr2 tm_unit_code).
    }
    apply id_right.
  Qed.

  (* The iso witnessing that the unit fiber is isomorphic to the reindexed El of unit_code *)
  Definition terminal_fiber_iso (Γ : context_from_comp_cat_with_u)
    : @z_iso (fiber_category _ _)
        ((pr1 Unit) ([] & (comp_cat_el Γ)))
        ((comp_cat_el unit_code_w) [[ π (comp_cat_el Γ) ]]).
  Proof.
    exact (z_iso_comp (z_iso_inv (comp_cat_unit_sub_iso _ ))
             (z_iso_inv (comp_cat_reindex_iso _ (comp_cat_unit_el_iso_w _ _ _ _)))).
  Defined.

  (*
      We prove uniqueness of the terminal maps  using the universal property of the pullback
      that is given by pulling back π (el unit_code) along π (el Γ) precomposed with an isomorphism
      and uniqueness of tt.
   *)

  Lemma terminal_uniqueness (Γ : context_from_comp_cat_with_u)
    (s : substitution_from_comp_cat_with_u Γ unit_code_w)
    : s = terminal_morphism Γ.
  Proof.
    unfold terminal_morphism.
    set (i' := terminal_fiber_iso Γ).
    assert (p_u : π (comp_cat_el Γ) · tm_unit_code · π (_) = π (comp_cat_el Γ)) by apply TerminalArrowEq.
    assert (p_s : identity ([] & comp_cat_el Γ) · s · π (comp_cat_el unit_code_w) = π (comp_cat_el Γ))
      by apply TerminalArrowEq.
    set (univ_u := comp_cat_univ_pullback_compose_iso i' p_u).
    set (univ_s := @comp_cat_univ_pullback_compose_iso _ _ _ _ _ (π (comp_cat_el Γ)) _ i' (identity _) s p_s).
    assert (unit_code_term_eq: univ_s = univ_u).
    {
      etrans.
      - exact (comp_cat_unit_unique univ_s).
      - exact (!(comp_cat_unit_unique univ_u)).
    }
    refine (_ @ maponpaths (λ z, pr1 z · PullbackPr1 (comp_cat_pullback_compose_iso (π (comp_cat_el Γ)) _) ) unit_code_term_eq @ _).
    - refine (!_).
      refine (PullbackArrow_PullbackPr1 _ _ _ _ _ @ _).
      apply id_left.
    - apply PullbackArrow_PullbackPr1.
  Qed.

End Terminal_from_comp_cat_with_u.

Definition cwf_terminal_from_comp_cat_with_u : Terminal cwf_context_from_comp_cat_with_u.
Proof.
  use tpair.
  - exact terminal_context.
  - intro Γ.
    exact (terminal_morphism Γ ,, terminal_uniqueness Γ).
Defined.

(** * Substitutions  *)

  Definition cwf_ty_from_comp_cat_with_u :  cwf_context_from_comp_cat_with_u → hSet.
  Proof.
    (* types in Γ are tm empty.(el Γ) U*)
    intro Γ.
    use tpair.
    - exact (comp_cat_tm (comp_cat_U ([] & (comp_cat_el Γ)))).
    - abstract (apply comp_cat_tm_isaset).
  Defined.

  Definition cwf_tm_from_comp_cat_with_u : ∏ Γ : cwf_context_from_comp_cat_with_u,
        cwf_ty_from_comp_cat_with_u Γ → hSet.
  Proof.
    (* tm Γ A is tm (⋄ & el Γ) (el A)*)
    intros Γ A.
    use tpair.
    - exact (comp_cat_tm (comp_cat_el A)).
    - abstract (apply comp_cat_tm_isaset).
  Defined.

  Definition cwf_subst_ty_from_comp_cat_with_u :
    ∏ Γ Δ : cwf_context_from_comp_cat_with_u,
        cwf_context_from_comp_cat_with_u ⟦ Δ, Γ ⟧ → cwf_ty_from_comp_cat_with_u Γ → cwf_ty_from_comp_cat_with_u Δ.
  Proof.
    intros Γ Δ s A.
    exact  ( (A [[ s ]]tm) ↑ ⌈comp_cat_univ_sub_iso s⌉).
  Defined.

  Definition cwf_subst_tm_from_comp_cat_with_u :
    ∏ (Γ Δ : cwf_context_from_comp_cat_with_u)
      (f : cwf_context_from_comp_cat_with_u ⟦ Δ, Γ ⟧)
      (A : cwf_ty_from_comp_cat_with_u Γ),
      cwf_tm_from_comp_cat_with_u Γ A →
      cwf_tm_from_comp_cat_with_u Δ (cwf_subst_ty_from_comp_cat_with_u Γ Δ f A).
  Proof.
    intros Γ Δ f A t.
    exact ( (t [[ f ]]tm) ↑ ⌈comp_cat_el_iso f A⌉ ).
  Defined.

  (** * Functorialities *)

  Definition cwf_id_ty_from_comp_cat_with_u :   ∏ (Γ : cwf_context_from_comp_cat_with_u) (A : cwf_ty_from_comp_cat_with_u Γ),
      cwf_subst_ty_from_comp_cat_with_u Γ Γ (identity Γ) A = A.
  Proof.
    intros.
    unfold cwf_subst_ty_from_comp_cat_with_u.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_subst_tm_id.
    }
    rewrite comp_cat_comp_coerce_tm.
    assert (p : ⌈ comp_cat_subst_ty_id_iso (comp_cat_U ([] & comp_cat_el Γ)) ⌉
                  · ⌈ comp_cat_univ_sub_iso (identity Γ) ⌉ = identity _).
    {
      refine (_ @ comp_cat_id_left_subst_ty _ _).
      rewrite assoc'.
      apply cancel_precomposition.
      unfold sub_comp_cat_univ_iso.
      apply cancel_precomposition.
      do 2 apply maponpaths.
      apply homset_property.
    }
    rewrite (comp_cat_coerce_eq p).
    apply comp_cat_id_coerce_tm.
    Qed.

  Definition cwf_comp_ty_from_comp_cat_with_u :
    ∏ (Γ Δ Θ : cwf_context_from_comp_cat_with_u) (g : cwf_context_from_comp_cat_with_u ⟦ Θ, Δ ⟧)
      (f : cwf_context_from_comp_cat_with_u ⟦ Δ, Γ ⟧) (A : cwf_ty_from_comp_cat_with_u Γ),
      cwf_subst_ty_from_comp_cat_with_u Γ Θ (g · f) A =
        cwf_subst_ty_from_comp_cat_with_u Δ Θ g (cwf_subst_ty_from_comp_cat_with_u Γ Δ f A).
  Proof.
    intros.
    unfold cwf_subst_ty_from_comp_cat_with_u.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_subst_tm_comp.
    }
    rewrite comp_cat_comp_coerce_tm.
    rewrite comp_cat_subst_coerce_tm.
    rewrite comp_cat_comp_coerce_tm.
    eapply comp_cat_coerce_eq.
    unfold sub_comp_cat_univ_iso.
    refine (assoc _ _ _ @ _).
    refine (maponpaths (λ z, z · _) (comp_cat_assoc_subst_ty _ _ _ _) @ _).
    rewrite !assoc'.
    etrans.
    2: {
      apply maponpaths_2.
      unfold "⌈ _ ⌉".
      refine (!_).
      apply comp_cat_reindex_coercion_comp_witness.
    }
    refine ( _ @ assoc _ _ _ ).
    apply cancel_precomposition.
    unfold "⌈ _ ⌉".
    refine (_ @ assoc' _ _ _).
    etrans.
    2 : {
      apply maponpaths_2.
      refine (!_).
      apply (comp_cat_reindex_coercion_subst_ty_iso (C := C) _ _ ).
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply  comp_cat_subst_ty_iso_comp.
    }
    etrans.
    2: {
      refine (!_).
      apply  comp_cat_subst_ty_iso_comp.
    }
    do 2 apply maponpaths.
    apply homset_property.
Qed.

  (* This is a transport for the term functorialities *)
  Proposition cwf_from_comp_cat_transport_lemma
              {Γ : cwf_context_from_comp_cat_with_u}
              {A B : cwf_ty_from_comp_cat_with_u Γ}
              (p : A = B)
              (t : cwf_tm_from_comp_cat_with_u Γ A)
    : transportf (cwf_tm_from_comp_cat_with_u Γ) p t
      = t ↑ (comp_cat_el_map p).
  Proof.
    induction p.
    cbn.
    unfold "↑".
    use comp_cat_tm_eq.
    - cbn.
      unfold comp_cat_comp_mor.
      rewrite comprehension_functor_mor_id.
      rewrite id_right.
      apply idpath.
  Qed.

  Definition cwf_id_tm_from_comp_cat_with_u :
    ∏ (Γ : cwf_context_from_comp_cat_with_u)
      (A : cwf_ty_from_comp_cat_with_u Γ)
      (t : cwf_tm_from_comp_cat_with_u Γ A),
      transportf (λ A0 : cwf_ty_from_comp_cat_with_u Γ,
            cwf_tm_from_comp_cat_with_u Γ A0) (cwf_id_ty_from_comp_cat_with_u Γ A)
        (cwf_subst_tm_from_comp_cat_with_u Γ Γ (identity Γ) A t) =
        t.
  Proof.
    intros.
    unfold cwf_subst_tm_from_comp_cat_with_u.
    rewrite cwf_from_comp_cat_transport_lemma.
    etrans.
    {
      do 2 apply maponpaths.
      apply (comp_cat_subst_tm_id).
    }
    do 2 rewrite comp_cat_comp_coerce_tm.
    refine (_ @ comp_cat_id_coerce_tm t).
    apply comp_cat_coerce_eq.
    set (coherence_id := (pr122 C) _ A).
    refine (_ @ !coherence_id).
    unfold comp_cat_el_map.
    unfold "⌈ _ ⌉".
    rewrite assoc.
    do 2 apply maponpaths.
    apply comp_cat_tm_isaset.
  Qed.

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
    intros.
    unfold cwf_subst_tm_from_comp_cat_with_u.
    rewrite cwf_from_comp_cat_transport_lemma.
    etrans.
    {
      do 2 apply maponpaths.
      apply comp_cat_subst_tm_comp.
    }
    do 2 rewrite comp_cat_comp_coerce_tm.
    rewrite comp_cat_subst_coerce_tm.
    rewrite comp_cat_comp_coerce_tm.
    apply comp_cat_coerce_eq.
    set (coherence_comp := (pr222 C) _ _ _ f g A).
    refine (_ @ !coherence_comp @ _).
    unfold comp_cat_el_map.
    rewrite !assoc'.
    do 3 apply maponpaths.
    apply comp_cat_tm_isaset.
    unfold cwf_subst_ty_from_comp_cat_with_u.
    apply maponpaths_2.
    refine (!_).
    apply (comp_cat_reindex_coercion_iso_eq g).
  Qed.

  (** *  Context Extension  *)

  Section extended_context.

    Let Con := cwf_context_from_comp_cat_with_u.
    Let T :=
          (make_cwf_ty_term_subst
             cwf_ty_from_comp_cat_with_u cwf_tm_from_comp_cat_with_u
             cwf_subst_ty_from_comp_cat_with_u cwf_subst_tm_from_comp_cat_with_u
             cwf_id_ty_from_comp_cat_with_u cwf_comp_ty_from_comp_cat_with_u
             cwf_id_tm_from_comp_cat_with_u cwf_comp_tm_from_comp_cat_with_u).

    Local Definition ext_con {Γ : Con} (A : cwf_ty_from_ty_term_subst T Γ): Con := (pr1 SigmaU _ Γ A).

    Local Definition proj {Γ : Con} (A : cwf_ty_from_ty_term_subst T Γ) : ext_con A --> Γ :=
        (comp_cat_comp_mor (⌈ (comp_cat_sigma_el_iso _ _ _ Γ A) ⌉)) · (comp_cat_sigma_proj_1 (comp_cat_el Γ) (comp_cat_el A)).

    Definition cwf_ctx_ext_from_comp_cat_with_u : cwf_ctx_ext T.
      Proof.
        intros Γ A.
        use tpair.
        - exact (ext_con A).
        - set (ctxextproj := (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ Sigma SigmaU _ _ ⌉)) · (comp_cat_sigma_proj_1 (comp_cat_el Γ) (comp_cat_el A))).
          use tpair.
          + exact ctxextproj.
          + cbn.
            simple refine ((comp_cat_var (comp_cat_el A)) [[ _ ]]tm ↑ _).
            2:
             {
              refine (_ · comp_cat_sigma_proj (Σ:=Sigma) (comp_cat_el Γ) (comp_cat_el A) ).
              refine (comp_cat_comp_mor ( ⌈comp_cat_sigma_el_iso _ _ _ _ _⌉)).
            }
            unfold cwf_subst_ty_from_comp_cat_with_u.
            refine (⌈comp_cat_subst_ty_comp_iso _ _ _⌉ · _).
            unfold ctxextproj.
            refine (comp_cat_el_iso _ _ · _).
            eapply comp_cat_el_map.
            abstract(
            unfold comp_cat_sigma_proj_1;
            rewrite !assoc';
            apply idpath).
      Defined.

  End extended_context.

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

  (** Useful lemmas for the universal property  *)

  Lemma cwf_from_comp_cat_with_u_transport_tm
    (CC := cwf_data_from_comp_cat_with_u)
    {Γ Δ : CC}
    {s s' : Γ --> Δ}
    (p : s = s')
    {A : cwf_ty Δ}
    (t : cwf_tm (A [[ s ]])%cwf)
    : (transportf_subst_tm_on_s p t = t ↑ (comp_cat_el_map ((maponpaths (λ z, A [[ z ]]) p)%cwf))).
  Proof.
    induction p.
    cbn.
    refine (!_).
    apply comp_cat_id_coerce_tm.
  Qed.

  Lemma cwf_from_comp_cat_with_u_comp
    (CC := cwf_data_from_comp_cat_with_u)
    {Γ₁ Γ₂ Γ₃ : CC}
    (s : Γ₁ --> Γ₂)
    (s' : Γ₂ --> Γ₃)
    (A : cwf_ty Γ₃)
    (t : cwf_tm ((A [[s']]) [[s]])%cwf)
    : cwf_subst_tm_comp A s' s t = t ↑ comp_cat_el_map (cwf_subst_ty_comp A s' s).
  Proof.
    unfold cwf_subst_tm_comp.
    apply cwf_from_comp_cat_transport_lemma.
  Qed.

  Definition cwf_from_comp_cat_with_u_ctx_ext_iso
    {γ: comp_cat_tm (comp_cat_U [])}
    (Γ := comp_cat_el γ)
    {a: comp_cat_tm (comp_cat_U ([] & Γ))}
    (A := comp_cat_el a)
    : z_iso ([] & comp_cat_el (pr1 SigmaU _ γ a)) ([] & Γ & A)
    := ( z_iso_comp (comp_cat_comp_iso (comp_cat_sigma_el_iso _ _ _ _ _)) (comp_cat_sigma_pair_proj_iso _ _ )).

  Definition cwf_from_comp_cat_with_u_ctx_ext_iso_law
    {γ: comp_cat_tm (comp_cat_U [])}
    (Γ := comp_cat_el γ)
    {a: comp_cat_tm (comp_cat_U ([] & Γ))}
    (A := comp_cat_el a)
    : cwf_from_comp_cat_with_u_ctx_ext_iso · π A · π _ = π _.
  Proof.
    unfold cwf_from_comp_cat_with_u_ctx_ext_iso.
    cbn.
    rewrite assoc4.
    rewrite( assoc' (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU γ a ⌉)) _  (π Γ)).
    rewrite comp_cat_sigma_proj_law.
    rewrite comp_cat_comp_mor_law.
    apply idpath.
  Defined.

  (** * Universal Property  *)

  Section universal_property_beta.

  (* Helper lemma for the universal property proof *)
    Local Lemma qA_subst_helper_lemma
      {Γ Δ : cwf_data_from_comp_cat_with_u}
      (A : cwf_ty Γ)
      (s : cwf_data_from_comp_cat_with_u ⟦ Δ, Γ ⟧)
      (t : cwf_tm (cwf_subst_ty s A))
      : let Δ' := [] & comp_cat_el Δ in
        let Γ' := [] & comp_cat_el Γ in
      pr1 t
        · comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
        · comp_cat_ext_subst s (comp_cat_el A)
        · comp_cat_sigma_pair (Σ:= Sigma)(comp_cat_el Γ) (comp_cat_el A)
        · comp_cat_sigma_proj_1 (comp_cat_el Γ) (comp_cat_el A)
        = s.
    Proof.
      intros.
      unfold comp_cat_sigma_proj_1.
      rewrite (assoc _ (comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A)) _).
      rewrite assoc4.
      eapply pathscomp0.
      - apply cancel_postcomposition.
        apply cancel_precomposition.
        apply comp_cat_sigma_beta.
      - rewrite id_right.
        rewrite <- (assoc _ _ (π (comp_cat_el A))).
        rewrite comp_cat_ext_subst_commute.
        rewrite assoc.
        unfold "π".
        rewrite assoc4.
        set (h := comprehension_functor_mor_comm (comp_cat_comprehension C)
                    (identity Δ') (⌈ comp_cat_el_iso s A ⌉⁻¹)).
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

   Context (Γ Δ : cwf_data_from_comp_cat_with_u)
        (A : cwf_ty Γ)
        (s : cwf_data_from_comp_cat_with_u ⟦ Δ, Γ ⟧)
        (t : cwf_tm (cwf_subst_ty s A)).

   Let Δ' := ([] & comp_cat_el Δ).
   Let Γ' := ([] & comp_cat_el Γ).

  (* The candidate u that witnesses the universal property *)
  Local Definition u
       : comp_cat_morphisms (pr1 C) ([] & comp_cat_el Δ) ([] & comp_cat_el (cwf_extended_con Γ A)).
  Proof.
    cbn in t.
    refine (t · _).
    refine (comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹) · _).
    refine (comp_cat_ext_subst (C:=C) s (comp_cat_el A) · _).
    refine (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) · _).
    exact (comp_cat_comp_mor (⌈ pr12 SigmaU [] Γ A ⌉⁻¹)).
  Defined.

  Let pA := (cwf_projection Γ A).

  (* First equation: u · p_A = s *)
  Local Lemma eq1
    : u · pA  = s.
  Proof.
    cbn.
    set (j := pr12 SigmaU [] Γ A).
    unfold u.
    rewrite !assoc.
    rewrite (assoc _ (comp_cat_comp_mor (⌈ j ⌉))
               (comp_cat_sigma_proj_1
                  (comp_cat_el Γ) (comp_cat_el A))).
    rewrite assoc4.
    eapply pathscomp0.
    - apply cancel_postcomposition.
      apply cancel_precomposition.
      apply comp_cat_comp_mor_z_iso_after_z_iso_inv.
    - rewrite (id_right _).
      apply qA_subst_helper_lemma.
  Qed.

  Lemma eq2_helper
    :  pr1 t
         · (comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
              · (comp_cat_ext_subst s (comp_cat_el A)
                   · (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
                        · comp_cat_comp_mor (⌈ (pr12 SigmaU) [] Γ A ⌉⁻¹))))
         · (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉)
              · comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A) · π (comp_cat_el A))
       = s.
  Proof.
    rewrite !assoc'.
    etrans.
    { do 4 apply maponpaths. rewrite assoc.
      rewrite comp_cat_comp_mor_z_iso_after_z_iso_inv.
      rewrite id_left.
      apply idpath.
    }
    etrans.
    { do 3 apply maponpaths.
      rewrite assoc.
      rewrite comp_cat_sigma_beta.
      apply id_left.
    }
    rewrite comp_cat_ext_subst_commute.
    do 2 rewrite assoc.
    rewrite assoc4.
    rewrite comp_cat_comp_mor_law.
    etrans.
    { apply maponpaths_2.
      apply (pr2 t).
    }
    apply id_left.
  Qed.

  (* Second equation: t = q_A[u] *)
  Local Lemma eq2
    : transportf_subst_tm_on_s (C:= cwf_data_from_comp_cat_with_u) eq1 (cwf_qA_subst _) = t.
  Proof.
    unfold cwf_qA_subst.
    cbn  -[cwf_ctx_ext_from_comp_cat_with_u].
    unfold cwf_subst_tm_from_comp_cat_with_u.
    unfold cwf_subst_ty_from_comp_cat_with_u.
    rewrite cwf_from_comp_cat_with_u_transport_tm.
    rewrite cwf_from_comp_cat_with_u_comp.
    cbn -[comp_cat_comp_mor comp_cat_subst_ty_comp_iso comp_cat_el_iso comp_cat_el_map fiber_category].
    rewrite !comp_cat_comp_coerce_tm.
    rewrite !comp_cat_el_map_comp.
    etrans.
    { do 2 apply maponpaths.
      rewrite <- (comp_cat_comp_coerce_tm (⌈ comp_cat_subst_ty_comp_iso (comp_cat_el A) (π (comp_cat_el A))
         (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉)
          · comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A))
         ⌉) _ _ ).
      apply idpath.
    }
    etrans.
    { apply maponpaths.
      apply comp_cat_subst_coerce_tm.
    }
    etrans.
    { do 2 apply maponpaths.
      apply comp_cat_subst_coerce_tm.
    }
    etrans.
    { apply maponpaths.
      apply comp_cat_comp_coerce_tm.
    }
    rewrite <- comp_cat_reindex_coercion_comp_witness.
    etrans.
    { apply comp_cat_comp_coerce_tm. }
    rewrite comp_cat_reindex_coercion_comp_witness.
    rewrite comp_cat_reindex_coercion_comp_witness.
    etrans.
    {apply maponpaths_2.
     rewrite !assoc'.
     apply maponpaths.
     refine (assoc' _ _ _ @ _).
     apply maponpaths.
     rewrite assoc.
     apply maponpaths_2.
     refine (!_).
     apply comp_cat_el_iso_natural.
    }
    etrans.
    { apply maponpaths_2.
      do 2 apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply comp_cat_el_map_comp.
    }
    unfold u.
    etrans.
    { apply maponpaths_2.
      apply maponpaths.
      refine (assoc _ _ _ @ maponpaths_2 _ _ _ @ _ ).
      apply (comp_cat_univ_coherent_comp' (C:=C)).
      apply idpath.
    }
    rewrite <- comp_cat_subst_tm_comp'.
    rewrite comp_cat_comp_coerce_tm.
    etrans.
    { apply maponpaths_2.
      do 2 refine(assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _ ).
      apply maponpaths_2.
      refine (assoc _ _ _  @ _).
      apply maponpaths_2.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      apply (comp_cat_assoc'_subst_ty (C:=C)). }
    etrans.
    {
      apply maponpaths_2.
      do 3  apply maponpaths_2.
      do 2 (refine (assoc _ _ _ @ _); apply maponpaths_2).
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_left.
    assert (H : pr1 t · (comp_cat_comp_mor (⌈comp_cat_el_iso s A⌉⁻¹)
                           · (comp_cat_ext_subst s (comp_cat_el A)
                                · (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
                                     · comp_cat_comp_mor (⌈(pr12 SigmaU) [] Γ A⌉⁻¹))))
                      · (comp_cat_comp_mor (⌈comp_cat_sigma_el_iso C Sigma SigmaU Γ A⌉)
                           · comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A))
                    = pr1 t · comp_cat_comp_mor (⌈comp_cat_el_iso s A⌉⁻¹)
                        · comp_cat_ext_subst s (comp_cat_el A)).
    { rewrite !assoc'. do 2 apply cancel_precomposition.
      rewrite <- (id_right (comp_cat_ext_subst s (comp_cat_el A))).
      rewrite assoc'.
      apply maponpaths.
      rewrite id_left.
      rewrite !assoc.
      rewrite assoc4.
      rewrite comp_cat_comp_mor_z_iso_after_z_iso_inv.
      rewrite id_right.
      apply comp_cat_sigma_beta.
    }
    etrans.
    { apply maponpaths.
      refine (!_).
      apply (comp_cat_subst_tm_eq (comp_cat_var (comp_cat_el A)) (!H)).
    }
    rewrite comp_cat_comp_coerce_tm.
    set (t' := t ↑ ⌈comp_cat_el_iso s A⌉⁻¹).
    etrans.
    {apply maponpaths.
     apply (@comp_cat_var_subst C _ _ (comp_cat_el A) s t').
    }
    unfold t'.
    do 2 rewrite comp_cat_comp_coerce_tm.
    rewrite <- (comp_cat_id_coerce_tm t).
    apply comp_cat_coerce_eq.
    unfold comp_cat_var_subst_coerce.
    etrans.
    { apply maponpaths.
      do 2 refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      do 3 (refine (assoc _ _ _ @ _); apply maponpaths_2).
      refine (assoc' _ _ _ @ _). apply maponpaths.
      apply comp_cat_comp_iso_natural.
    }
    etrans.
    { apply maponpaths.
      do 4 apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_right.
    etrans.
    { apply maponpaths.
      do 3 apply maponpaths_2.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply comp_cat_subst_ty_iso_comp.
    }
    etrans.
    { apply maponpaths.
      do 3 apply maponpaths_2.
      apply comp_cat_subst_ty_iso_comp.
    }
    etrans.
    {  apply maponpaths.
       refine (assoc' _ _ _ @ _ ) ; apply maponpaths.
       apply comp_cat_el_map_comp.
    }
    apply z_iso_inv_on_right.
    rewrite id_right.
    refine (assoc' _ _ _ @ _).
    assert (Hinv : ⌈comp_cat_el_iso s A⌉ = ⌈z_iso_inv (comp_cat_el_iso s A)⌉⁻¹) by apply idpath.
    etrans.
    2 : {
      refine (!_).
      apply Hinv.
    }
    etrans.
    2: {
      apply id_left.
    }
    apply z_iso_inv_on_left.
    etrans.
    2: {
      refine (!_).
      rewrite <- assoc4.
      do 2 refine (assoc' _ _ _ @ _ ).
      apply maponpaths.
      refine (_ @  comp_cat_el_iso_el_map_el_iso_inv _ _ _).
      - rewrite !assoc'; do 2 apply maponpaths; apply idpath.
      - apply eq2_helper.
    }
    etrans.
    2: {
      refine (!_).
      apply comp_cat_subst_ty_iso_comp.
    }
    Check comp_cat_subst_ty_eq.
    unfold comp_cat_subst_ty_iso.
    etrans.
    2: {
      refine (!_).
      refine (_ @ idtoiso_idpath _ ).
      apply maponpaths.
      apply maponpaths.
      refine (_ @ comp_cat_subst_ty_eq_idpath _ _).
      apply maponpaths.
      apply homset_property.
    }
    apply idpath.
Qed.

  End universal_property_beta.

  Local Definition universal_property_eta
    {Γ Δ : cwf_data_from_comp_cat_with_u}
    {A : cwf_ty Γ} {s : cwf_data_from_comp_cat_with_u ⟦ Δ, (Γ & A)%cwf ⟧}
    : s = u Γ Δ A (s · (p_ A)%cwf) (cwf_subst_tm_comp A (p_ A)%cwf s ((q_ A) [[s ]]tm)%cwf).
  Proof.
    rewrite cwf_from_comp_cat_with_u_comp.
    unfold u.
    rewrite !assoc.
    etrans.
    { refine (!_).
      apply id_right. }
    etrans.
    { apply maponpaths.
      refine (!_).
      apply (comp_cat_comp_mor_z_iso_inv_after_z_iso ((pr12 SigmaU) [] Γ A)).
    }
    etrans.
    { apply (assoc (C:=C)). }
    apply (cancel_postcomposition (C:=C)).
    etrans.
    { refine (!_).
      apply id_right. }
    etrans.
    { apply maponpaths.
      refine (!_).
      apply comp_cat_sigma_eta.
    }
    etrans.
    { apply (assoc (C:=C)). }
    apply (cancel_postcomposition (C:=C)).
    set (i_sigma_code := (pr12 SigmaU)).
    etrans.
    2: {  do 2 apply maponpaths_2.
      apply maponpaths.
      cbn -[comp_cat_comp_mor comp_cat_subst_ty_comp_iso comp_cat_el_iso comp_cat_el_map fiber_category comp_cat_ext_subst].
      apply idpath.
    }
    unfold cwf_subst_tm_from_comp_cat_with_u.
    refine (!_).
    etrans.
    { do 2 apply maponpaths_2.
      do 3 apply maponpaths.
      apply comp_cat_subst_coerce_tm.
    }
    rewrite <- comp_cat_subst_tm_comp'.
    rewrite !comp_cat_comp_coerce_tm.
    rewrite <- comp_cat_extend_subst_eta.
    unfold comp_cat_extend_subst.
    unfold comp_cat_tm_from_extend_subst.
    refine (!_).
    etrans.
    { apply maponpaths.
      use comp_cat_ext_subst_eq.
      - exact (s · (p_ A)%cwf).
      - abstract (rewrite !assoc'; apply idpath).
    }
    rewrite !assoc.
    apply maponpaths_2.
    unfold "↑".
    cbn -[comp_cat_comp_mor comp_cat_subst_ty_comp_iso comp_cat_el_iso comp_cat_el_map fiber_category comp_cat_ext_subst comp_cat_reindex_coercion
            comp_cat_var comp_cat_subst_tm].
    etrans.
    { rewrite assoc'.
      apply maponpaths.
      refine (!_).
      apply comp_cat_comp_mor_comp'.
    }
    refine (!_).
    etrans.
    { rewrite assoc'.
      apply maponpaths.
      refine (!_).
      apply comp_cat_comp_mor_comp'.
    }
    etrans.
    { apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      refine (comp_cat_subst_tm_eq _ _).
      apply assoc'.
    }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    rewrite <- comp_cat_comp_mor_comp'.
    apply maponpaths.
    rewrite comp_cat_reindex_coercion_comp_witness.
    rewrite comp_cat_reindex_coercion_iso_eq.
    etrans.
    {
      apply maponpaths.
      rewrite <- assoc4.
      rewrite !assoc'.
      do 2 apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      refine (!_).
      rewrite comp_cat_reindex_coercion_comp_witness.
      rewrite assoc'.
      apply maponpaths.
      apply (comp_cat_stable_el_map _ _ (maponpaths (fun t => t [[ s ]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉) (cwf_ctx_ext_from_comp_cat_with_u_subproof Γ A))).
    }
    set (universe_data := pr12 C).
    etrans.
    { do 3 apply maponpaths.
      do 3 apply maponpaths_2.
      apply (comp_cat_reindex_coercion_iso_eq (C:=C)).
    }
    etrans.
    { do 3 apply maponpaths.
      rewrite assoc4.
      apply maponpaths_2.
      apply maponpaths.
      apply assoc'.
    }
    etrans.
    { do 3 apply maponpaths.
      apply maponpaths_2.
      rewrite assoc.
      apply maponpaths.
      apply comp_cat_el_map_comp.
    }
    etrans.
    { do 3 apply maponpaths.
      do 2 apply maponpaths_2.
      apply comp_cat_univ_coherent_comp.
    }
    etrans.
    { do 3 apply maponpaths.
      apply maponpaths_2.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply comp_cat_el_map_comp.
    }
    assert (H : (s · (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉) · comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A)
                        · π (comp_cat_el A))) = (s · (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉)
                                                        · comp_cat_sigma_proj_1 (comp_cat_el Γ) (comp_cat_el A))))
      by (unfold comp_cat_sigma_proj_1; apply maponpaths; rewrite assoc; apply idpath).
    etrans.
    { do 3 apply maponpaths.
      do 2 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply (comp_cat_el_iso_el_map_el_iso_inv (C:=C) _ H _).
    }
    etrans.
    { do 2 apply maponpaths.
      refine (!_).
      rewrite <- comp_cat_reindex_coercion_iso_eq.
      rewrite assoc.
      apply maponpaths_2.
      apply (comp_cat_assoc'_subst_ty (C:=C)).
    }
    etrans.
    { apply maponpaths.
      refine (assoc _ _ _ @ _ ).
      do 2 (apply maponpaths_2; refine (assoc _ _ _ @ _)).
      refine ( maponpaths_2 _ _ _  @ _).
      apply z_iso_after_z_iso_inv.
      apply id_left.
    }
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply comp_cat_subst_ty_iso_comp.
    }
    rewrite assoc.
    etrans.
    { apply maponpaths_2.
      apply comp_cat_comp_iso_natural.
    }
    refine (assoc' _ _ _ @ _).
    rewrite comp_cat_subst_ty_iso_comp.
    apply cancel_precomposition.
    do 2 apply maponpaths.
    apply homset_property.
  Qed.

  Definition cwf_universal_property_from_comp_cat_with_u
    : cwf_universal_property cwf_data_from_comp_cat_with_u.
  Proof.
    use make_cwf_universal_property_β_η.
    - intros.
      exact (u Γ Δ A s t).
    - intros.
      exact (eq1 _ _ A s t).
    - intros.
      exact (eq2 _ _ A s t).
    - intros.
      simpl.
      apply universal_property_eta.
  Defined.

  Definition cwf_from_comp_cat_with_u : cwf.
  Proof.
    use make_cwf.
    - exact cwf_data_from_comp_cat_with_u.
    - exact cwf_universal_property_from_comp_cat_with_u.
  Defined.

End Construction.
