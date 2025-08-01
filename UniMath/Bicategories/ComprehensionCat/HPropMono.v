(**

 Propositions in a comprehension category

 Let `C` be a comprehension category with extensional identity types. In `C`, we can
 define that the type `A` in context `Γ` is a proposition in multiple ways.
 1. We can assert that we have a term of type `x = y` in context `Γ , x : A , y : A`.
    This is how the notion of proposition is usually defined in homotopy type theory.
 2. We can assert that the projection `π A` is a monomorphism.
 3. We can assert that for all contexts `Δ` and substitutions `s : Δ --> Γ` all terms
    of type `A [[ s ]]` in context `Δ` are equal.
 4. We can assert that the unique morphism from `A` to the unit type in the category
    of types is a monomorphism.
 In this file, we compare these notions and show that they coincide. We first show
 that a type `A` is a proposition if and only if the projection `π A` is a monomorphism
 [is_hprop_ty_weq_mono_ty]. While this proof is given for DFL full comprehension
 categories, it can be translated to any comprehension category with extensional identity
 types. We also show that the second and third formulations are equivalent
 [mono_ty_weq_all_terms_eq].

 Finally we show that a type is a proposition if and only if the unique morphism to the
 unit type is a monomorphism [subsingleton_weq_mono_ty]. Here we use the fact that the
 comprehension functor in a DFL full comprehension category is an equivalence, because
 this allows one to conclude that it preserves monomorphisms.

 References
 - "Modular correspondence between dependent type theories and categories including
   pretopoi and topoi" by Maietti

 Content
 1. Propositions in a comprehension category
 2. A type `A` is a proposition iff `π A` is a monomorphism
 3. A type `A` is a proposition iff all terms of type `A` in every context are equal
 4. A type `A` is a proposition iff morphisms to the unit is a monomorphism

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodMorphisms.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Mono.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.

Local Open Scope cat.
Local Open Scope comp_cat.

Section MonoVSHProp.
  Context {C : dfl_full_comp_cat}.

  (** * 1. Propositions in a comprehension category *)
  Definition is_hprop_ty
             {Γ : C}
             (A : ty Γ)
             (lhs : tm ((Γ & A) & (A [[ π _ ]])) (A [[ π _ ]] [[ π _ ]])
                  := comp_cat_tm_var (Γ & A) (A [[π A]]))
             (rhs : tm ((Γ & A) & (A [[ π _ ]])) (A [[ π _ ]] [[ π _ ]])
                  := comp_cat_tm_var Γ A [[ π _ ]]tm)
    : UU
    := tm (Γ & A & (A [[ π A ]])) (dfl_ext_identity_type lhs rhs).

  Proposition isaprop_is_hprop_ty
              {Γ : C}
              (A : ty Γ)
    : isaprop (is_hprop_ty A).
  Proof.
    use invproofirrelevance.
    intros t₁ t₂.
    pose (dfl_eq_subst_equalizer_tm (identity _) _ _ (t₁ [[ _ ]]tm) (t₂ [[ _ ]]tm)) as p.
    rewrite !id_sub_comp_cat_tm in p.
    pose proof (maponpaths (λ z, z ↑ id_subst_ty_inv _) p) as q.
    simpl in q.
    rewrite !comp_coerce_comp_cat_tm in q.
    refine (_ @ q @ _).
    - refine (!(id_coerce_comp_cat_tm _) @ _).
      apply maponpaths_2.
      refine (!_).
      apply (z_iso_inv_after_z_iso (id_subst_ty_iso _)).
    - refine (_ @ id_coerce_comp_cat_tm _).
      apply maponpaths_2.
      apply (z_iso_inv_after_z_iso (id_subst_ty_iso _)).
  Qed.

  (** * 2. A type `A` is a proposition iff `π A` is a monomorphism *)

  (**
     We first show that a type is a proposition if its projection is a monomorphism.
     This is proven by doing a calculation.
   *)
  Proposition mono_ty_to_hprop_ty
              {Γ : C}
              {A : ty Γ}
              (HA : isMonic (π A))
    : is_hprop_ty A.
  Proof.
    unfold is_hprop_ty.
    use dfl_ext_identity_type_tm.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
    - rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
      }
      rewrite id_right.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
      }
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
      + rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
        }
        rewrite id_right.
        use HA.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply PullbackSqrCommutes.
        }
        apply idpath.
      + rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          apply comp_cat_tm_eq.
        }
        rewrite id_right.
        apply idpath.
    - rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply comp_cat_tm_eq.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply comp_cat_tm_eq.
      }
      apply idpath.
  Qed.

  (**
     Next we show that the projection of every proposition is a monomorphism, and
     here we use that identity types are extensional. From extensionality, we obtain
     an equality between two terms (that are variables). We perform a suitable
     substitution, and that gives us the desired equality.
   *)
  Section HPropToMono.
    Context {Γ : C}
            {A : ty Γ}
            (HA : is_hprop_ty A)
            {Δ : C}
            {t₁ t₂ : Δ --> Γ & A}
            (p : t₁ · π A = t₂ · π A).

    Definition hprop_ty_to_mono_ty_subst
      : Δ --> Γ & A & (A [[ π _ ]]).
    Proof.
      use (PullbackArrow (comp_cat_pullback _ _)).
      - exact t₁.
      - exact t₂.
      - exact p.
    Defined.

    Proposition hprop_ty_to_mono_ty_eq
      : t₁ = t₂.
    Proof.
      pose proof (maponpaths
                    (λ z, hprop_ty_to_mono_ty_subst
                          · pr1 z
                          · PullbackPr1 (comp_cat_pullback _ _)
                          · PullbackPr1 (comp_cat_pullback _ _))
                    (tm_ext_identity_to_eq HA))
        as q.
      simpl in q.
      refine (_ @ q @ _) ; clear q.
      - refine (!_).
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          apply id_left.
        }
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
      - etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          rewrite PullbackArrow_PullbackPr1.
          rewrite !assoc'.
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
        }
        rewrite id_right.
        apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _)).
    Qed.
  End HPropToMono.

  Proposition hprop_ty_to_mono_ty
              {Γ : C}
              {A : ty Γ}
              (HA : is_hprop_ty A)
    : isMonic (π A).
  Proof.
    intros Δ t₁ t₂ p.
    exact (hprop_ty_to_mono_ty_eq HA p).
  Qed.

  Definition is_hprop_ty_weq_mono_ty
             {Γ : C}
             (A : ty Γ)
    : is_hprop_ty A ≃ isMonic (π A).
  Proof.
    use weqimplimpl.
    - exact hprop_ty_to_mono_ty.
    - exact mono_ty_to_hprop_ty.
    - apply isaprop_is_hprop_ty.
    - apply isapropisMonic.
  Qed.

  (** * 3. A type `A` is a proposition iff all terms of type `A` in every context are equal *)

  (**
     If all terms of type `A` in every context are equal, then we can show that the projection
     morphism of `A` is a monomorphism. The main task is constructing suitable terms for which
     we use the universal mapping property of the pullback.
   *)
  Section UniqueTermsToMono.
    Context {Γ : C}
            {A : ty Γ}
            (HA : ∏ (Δ : C) (s : Δ --> Γ), isaprop (tm Δ (A [[ s ]])))
            {Δ : C}
            {t₁ t₂ : Δ --> Γ & A}
            (p : t₁ · π A = t₂ · π A).

    Definition all_terms_eq_to_mono_type_lhs
      : tm Δ (A [[ t₁ · π A ]]).
    Proof.
      use make_comp_cat_tm.
      - use (PullbackArrow (comp_cat_pullback _ _)).
        + exact t₁.
        + apply identity.
        + abstract
            (rewrite id_left ;
             apply idpath).
      - abstract
          (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _))).
    Defined.

    Definition all_terms_eq_to_mono_type_rhs
      : tm Δ (A [[ t₁ · π A ]]).
    Proof.
      use make_comp_cat_tm.
      - use (PullbackArrow (comp_cat_pullback _ _)).
        + exact t₂.
        + apply identity.
        + abstract
            (rewrite id_left ;
             rewrite p ;
             apply idpath).
      - abstract
          (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _))).
    Defined.

    Proposition all_terms_eq_to_mono_type_lhs_rhs_eq
      : all_terms_eq_to_mono_type_lhs
        =
        all_terms_eq_to_mono_type_rhs.
    Proof.
      exact (proofirrelevance
               _
               (HA Δ (t₁ · π A))
               all_terms_eq_to_mono_type_lhs
               all_terms_eq_to_mono_type_rhs).
    Qed.

    Proposition all_terms_eq_to_mono_type_eq
      : t₁ = t₂.
    Proof.
      pose (maponpaths
              (λ z, pr1 z · PullbackPr1 (comp_cat_pullback _ _))
              all_terms_eq_to_mono_type_lhs_rhs_eq)
        as q.
      simpl in q.
      refine (_ @ q @ _).
      - rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      - rewrite PullbackArrow_PullbackPr1.
        apply idpath.
    Qed.
  End UniqueTermsToMono.

  (**
     To prove the reverse, we first show that all terms in a propositon are equal. Then
     it suffices to prove that the type `A [[ s ]]` is a proposition, so it is enough
     to show that the projection of `A [[ s ]]` is a monomorphism. Here we use that
     monomorphisms are closed under pullback
   *)
  Proposition isaprop_tm_hprop_ty
              {Γ : C}
              {A : ty Γ}
              (HA : is_hprop_ty A)
    : isaprop (tm Γ A).
  Proof.
    use invproofirrelevance.
    intros t₁ t₂.
    use eq_comp_cat_tm.
    use (hprop_ty_to_mono_ty HA).
    rewrite !comp_cat_tm_eq.
    apply idpath.
  Qed.

  Proposition mono_ty_subst_all_terms_eq
              {Γ : C}
              {A : ty Γ}
              (HA : isMonic (π A))
              {Δ : C}
              (s : Δ --> Γ)
    : isaprop (tm Δ (A [[ s ]])).
  Proof.
    use isaprop_tm_hprop_ty.
    use mono_ty_to_hprop_ty.
    pose (m := (π A ,, HA) : Monic _ _ _).
    exact (MonicPullbackisMonic _ m s (comp_cat_pullback A s)).
  Qed.

  Definition mono_ty_weq_all_terms_eq
             {Γ : C}
             {A : ty Γ}
    : isMonic (π A) ≃ ∏ (Δ : C) (s : Δ --> Γ), isaprop (tm Δ (A [[ s ]])).
  Proof.
    use weqimplimpl.
    - exact mono_ty_subst_all_terms_eq.
    - intros HA Δ t₁ t₂ p.
      exact (all_terms_eq_to_mono_type_eq HA p).
    - apply isapropisMonic.
    - do 2 (use impred ; intro).
      apply isapropisaprop.
  Defined.

  (** * 4. A type `A` is a proposition iff morphisms to the unit is a monomorphism *)
  Proposition subsingleton_to_mono_ty
              {Γ : C}
              {A : ty Γ}
              (HA : isMonic (TerminalArrow (dfl_full_comp_cat_terminal Γ) A))
    : isMonic (π A).
  Proof.
    rewrite <- (comp_cat_comp_mor_comm
                  (TerminalArrow (dfl_full_comp_cat_terminal Γ)
                     A)).
    use isMonic_comp.
    - use from_is_monic_cod_fib.
      pose (m := (_ ,, HA) : Monic _ _ _).
      refine (weak_equiv_preserves_monic
                (F := fiber_functor (comp_cat_comprehension C) Γ)
                _
                m).
      use weak_equiv_from_equiv.
      exact (fiber_functor_comprehension_adj_equiv _ Γ).
    - apply is_iso_isMonic.
      apply dfl_full_comp_cat_extend_unit.
  Qed.

  Proposition mono_ty_to_subsingleton
              {Γ : C}
              {A : ty Γ}
              (HA : isMonic (π A))
    : isMonic (TerminalArrow (dfl_full_comp_cat_terminal Γ) A).
  Proof.
    intros A' t₁ t₂ p.
    use (invmaponpathsweq
           (disp_functor_ff_weq
              _
              (full_comp_cat_comprehension_fully_faithful C)
              _ _ _)).
    use eq_mor_cod_fib ; simpl.
    use HA.
    exact (mor_eq _ @ !(mor_eq _)).
  Qed.

  Definition subsingleton_weq_mono_ty
             {Γ : C}
             (A : ty Γ)
    : isMonic (TerminalArrow (dfl_full_comp_cat_terminal Γ) A)
      ≃
      isMonic (π A).
  Proof.
    use weqimplimpl.
    - exact subsingleton_to_mono_ty.
    - exact mono_ty_to_subsingleton.
    - apply isapropisMonic.
    - apply isapropisMonic.
  Qed.
End MonoVSHProp.
