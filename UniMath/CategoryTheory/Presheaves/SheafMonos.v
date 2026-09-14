(**

 The first-order hyperdoctrine of predicates for sheaves

 We already gave concrete descriptions of connectives for predicates of sheaves in the
 file `SheafLogic`. Here we assemble these operations to construct a first-order
 hyperdoctrine over the category of sheaves. In addition, we construct an equivalence
 between this hyperdoctrine and the one arising from monomorphisms in the category of
 sheaves.

 Content
 1. The displayed category of predicates over sheaves
 2. This displayed category is univalent
 3. A cleaving for this displayed category
 4. The connectives
 5. Equivalence with the category of monomorphisms

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrineChosen.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifierSheaf.
Require Import UniMath.CategoryTheory.Presheaves.PresheafLogic.
Require Import UniMath.CategoryTheory.Presheaves.ClosedSieves.
Require Import UniMath.CategoryTheory.Presheaves.SheafLogic.

Local Open Scope cat.

Section SheafLogic.
  Context {C : site}.

  (** * 1. The displayed category of predicates over presheaves *)
  Definition sheaf_predicate_disp_cat_ob_mor
    : disp_cat_ob_mor (cat_of_sheaves C).
  Proof.
    simple refine (_ ,, _).
    - exact sheaf_predicate.
    - exact (λ Γ₁ Γ₂ φ ψ s, sheaf_predicate_entails φ (sheaf_predicate_subst s ψ)).
  Defined.

  Proposition sheaf_predicate_disp_cat_id_comp
    : disp_cat_id_comp _ sheaf_predicate_disp_cat_ob_mor.
  Proof.
    split.
    - intros Γ φ x y f xx p.
      exact p.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ φ₁ φ₂ φ₃ p q x y f xx r.
      refine (q x y f _ _).
      exact (p x y f xx r).
  Qed.

  Definition sheaf_predicate_disp_cat_data
    : disp_cat_data (cat_of_sheaves C).
  Proof.
    simple refine (_ ,, _).
    - exact sheaf_predicate_disp_cat_ob_mor.
    - exact sheaf_predicate_disp_cat_id_comp.
  Defined.

  Proposition sheaf_predicate_disp_cat_axioms
    : disp_cat_axioms _ sheaf_predicate_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply propproperty.
    - intro ; intros.
      apply propproperty.
    - intro ; intros.
      apply propproperty.
    - intro ; intros.
      apply isasetaprop.
      apply propproperty.
  Qed.

  Definition sheaf_predicate_disp_cat
    : disp_cat (cat_of_sheaves C).
  Proof.
    simple refine (_ ,, _).
    - exact sheaf_predicate_disp_cat_data.
    - exact sheaf_predicate_disp_cat_axioms.
  Defined.

  Proposition locally_propositional_sheaf_predicate_disp_cat
    : locally_propositional sheaf_predicate_disp_cat.
  Proof.
    intros Γ₁ Γ₂ s φ ψ.
    apply propproperty.
  Qed.

  (** * 2. This displayed category is univalent *)
  Proposition is_univalent_disp_sheaf_predicate_disp_cat
    : is_univalent_disp sheaf_predicate_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros Γ₁ φ ψ.
    use isweqimplimpl.
    - intro p.
      use psh_term_eq.
      intros x xx.
      use closed_sieve_eq.
      use sieve_eq.
      + refine (λ y g, _).
        pose (pr1 p) as q.
        cbn in g, q.
        exact (q _ _ g xx).
      + refine (λ y g, _).
        pose (pr12 p) as q.
        cbn in g, q.
        exact (q _ _ g xx).
    - apply isaset_psh_term.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply locally_propositional_sheaf_predicate_disp_cat.
  Qed.

  (** * 3. A cleaving for this displayed category *)
  Section CartesianLift.
    Context {Γ₁ Γ₂ : sheaf C}
            (s : sheaf_nat_trans Γ₁ Γ₂)
            (φ : sheaf_predicate Γ₂).

    Proposition cleaving_sheaf_predicate_disp_cat_entails
      : sheaf_predicate_entails
          (sheaf_predicate_subst s φ)
          (sheaf_predicate_subst s φ).
    Proof.
      intros x y f xx p ; cbn in *.
      exact p.
    Qed.

    Proposition is_cartesian_cleaving_sheaf_predicate_disp_cat_entails
      : is_cartesian
          (D := sheaf_predicate_disp_cat)
          cleaving_sheaf_predicate_disp_cat_entails.
    Proof.
      intros Γ₀ s' ψ p.
      use make_iscontr.
      - simple refine (_ ,, _).
        + intros x y f xx q.
          exact (p x y f xx q).
        + apply locally_propositional_sheaf_predicate_disp_cat.
      - intro t.
        use subtypePath.
        {
          intro.
          apply homsets_disp.
        }
        apply locally_propositional_sheaf_predicate_disp_cat.
    Qed.
  End CartesianLift.

  Definition cleaving_sheaf_predicate_disp_cat
    : cleaving sheaf_predicate_disp_cat.
  Proof.
    intros Γ₁ Γ₂ s φ.
    simple refine (_ ,, _).
    - exact (sheaf_predicate_subst s φ).
    - simple refine (_ ,, _).
      + exact (cleaving_sheaf_predicate_disp_cat_entails s φ).
      + exact (is_cartesian_cleaving_sheaf_predicate_disp_cat_entails s φ).
  Defined.

  (** * 4. The connectives *)
  Definition sheaf_predicate_fiberwise_terminal
    : fiberwise_terminal cleaving_sheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - exact locally_propositional_sheaf_predicate_disp_cat.
    - exact truth_sheaf_predicate.
    - exact (λ Γ φ, truth_sheaf_intro φ).
    - exact (λ Γ₁ Γ₂ s, truth_sheaf_subst s).
  Defined.

  Definition sheaf_predicate_fiberwise_initial
    : fiberwise_initial cleaving_sheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - exact locally_propositional_sheaf_predicate_disp_cat.
    - exact false_sheaf_predicate.
    - exact (λ Γ φ, false_sheaf_elim φ).
    - exact (λ Γ₁ Γ₂ s, false_sheaf_subst s).
  Defined.

  Definition sheaf_predicate_fiberwise_binproducts
    : fiberwise_binproducts cleaving_sheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - exact locally_propositional_sheaf_predicate_disp_cat.
    - exact (λ Γ φ ψ, conj_sheaf_predicate φ ψ).
    - exact (λ Γ φ ψ, conj_sheaf_elim_l φ ψ).
    - exact (λ Γ φ ψ, conj_sheaf_elim_r φ ψ).
    - exact (λ Γ φ ψ χ p₁ p₂, conj_sheaf_intro p₁ p₂).
    - exact (λ Γ₁ Γ₂ s φ ψ, conj_sheaf_subst s φ ψ).
  Defined.

  Definition sheaf_predicate_fiberwise_bincoproducts
    : fiberwise_bincoproducts cleaving_sheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - exact locally_propositional_sheaf_predicate_disp_cat.
    - exact (λ Γ φ ψ, disj_sheaf_predicate φ ψ).
    - exact (λ Γ φ ψ, disj_sheaf_intro_l φ ψ).
    - exact (λ Γ φ ψ, disj_sheaf_intro_r φ ψ).
    - exact (λ Γ φ ψ χ p₁ p₂, disj_sheaf_elim p₁ p₂).
    - exact (λ Γ₁ Γ₂ s φ ψ, disj_sheaf_subst s φ ψ).
  Defined.

  Definition sheaf_predicate_fiberwise_exponentials
    : fiberwise_exponentials sheaf_predicate_fiberwise_binproducts.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - exact locally_propositional_sheaf_predicate_disp_cat.
    - exact (λ Γ φ ψ, impl_sheaf_predicate φ ψ).
    - exact (λ Γ φ ψ, impl_sheaf_elim φ ψ).
    - exact (λ Γ φ ψ χ p, impl_sheaf_intro p).
    - exact (λ Γ₁ Γ₂ s φ ψ, impl_sheaf_subst s φ ψ).
  Defined.

  Definition sheaf_logic_hyperdoctrine
    : hyperdoctrine.
  Proof.
    use make_hyperdoctrine.
    - exact (cat_of_sheaves C).
    - exact sheaf_predicate_disp_cat.
    - exact (sheaf_terminal C).
    - exact (sheaf_binproducts C).
    - exact cleaving_sheaf_predicate_disp_cat.
    - exact locally_propositional_sheaf_predicate_disp_cat.
    - exact is_univalent_disp_sheaf_predicate_disp_cat.
  Defined.

  Definition sheaf_logic_universal_quantifiers
    : universal_quantifiers sheaf_logic_hyperdoctrine.
  Proof.
    use universal_quantifiers_from_chosen.
    use make_universal_quantifiers_chosen.
    - exact (λ Γ A φ, forall_sheaf_predicate φ).
    - exact (λ Γ A φ, forall_sheaf_intro φ).
    - exact (λ Γ A φ ψ p, forall_sheaf_elim p).
    - abstract
        (cbn ; unfold prodtofuntoprod ; cbn ;
         intros Γ₁ Γ₂ A s φ x₁ x₂ f xx H y g aa ;
         refine (from_sieve_eq_r
                   (sieve_eq_from_closed
                      (psh_term_pt_eq
                         φ
                         (maponpaths
                            (λ z, z ,, aa)
                            (!(eqtohomot (nat_trans_ax (pr1 s) _ _ (g · f)) _)))))
                      _
                      _) ;
         cbn ;
         rewrite id_left ;
         apply H).
  Defined.

  Definition sheaf_logic_existential_quantifiers
    : existential_quantifiers sheaf_logic_hyperdoctrine.
  Proof.
    use existential_quantifiers_from_chosen.
    use make_existential_quantifiers_chosen.
    - exact (λ Γ A φ, exists_sheaf_predicate φ).
    - exact (λ Γ A φ, exists_sheaf_intro φ).
    - exact (λ Γ A φ ψ p, exists_sheaf_elim p).
    - exact (λ Γ₁ Γ₂ A φ s, exists_sheaf_subst φ s).
  Defined.

  Definition sheaf_logic_equality_formulas
    : equality_formulas sheaf_logic_hyperdoctrine.
  Proof.
    use make_equality_formulas.
    - exact (λ Γ φ, eq_sheaf_predicate φ).
    - exact (λ Γ φ, eq_sheaf_intro φ).
    - exact (λ Γ φ ψ p, eq_sheaf_elim p).
  Defined.

  Definition sheaf_logic_first_order_hyperdoctrine
    : first_order_hyperdoctrine.
  Proof.
    use make_first_order_hyperdoctrine.
    - exact sheaf_logic_hyperdoctrine.
    - exact sheaf_predicate_fiberwise_terminal.
    - exact sheaf_predicate_fiberwise_initial.
    - exact sheaf_predicate_fiberwise_binproducts.
    - exact sheaf_predicate_fiberwise_bincoproducts.
    - exact sheaf_predicate_fiberwise_exponentials.
    - exact sheaf_logic_universal_quantifiers.
    - exact sheaf_logic_existential_quantifiers.
    - exact sheaf_logic_equality_formulas.
  Defined.

  (** * 5. Equivalence with the category of monomorphisms *)
  Section MonoPredicate.
    Context {Γ : sheaf C}
            (φ : sheaf_predicate Γ).

    Definition sheaf_predicate_to_dep_psh_mor
               {x y : C}
               {xx : (Γ x : hSet)}
               {yy : (Γ y : hSet)}
               {s : y --> x}
               (p : # Γ s xx = yy)
               (q : (φ x xx : closed_sieve _) x (identity x))
      : (φ y yy : closed_sieve _) y (identity y).
    Proof.
      induction p.
      cbn ; cbn in q.
      apply (from_sieve_eq_r
               (sieve_eq_from_closed (psh_term_naturality φ s xx))
               (identity y)).
      refine (#ω (φ x xx : closed_sieve _) s _ q).
      cbn.
      rewrite id_left, id_right.
      apply idpath.
    Qed.

    Definition sheaf_predicate_to_dep_psh
      : dep_psh Γ.
    Proof.
      use make_dep_psh.
      - exact (λ x xx, hProp_to_hSet ((φ x xx : closed_sieve x) x (identity x))).
      - intros x y xx yy s p q.
        exact (sheaf_predicate_to_dep_psh_mor p q).
      - abstract
          (intros ;
           apply propproperty).
      - abstract
          (intros ;
           apply propproperty).
    Defined.

    Section SheafAmalgamation.
      Context {x : C}
              {ω : sieve x}
              (p : C x ω)
              {z : matching_family Γ ω}
              (a : amalgamation z)
              (zz : matching_family_dep sheaf_predicate_to_dep_psh z).

      Definition sheaf_predicate_to_dep_sheaf_amalgamation
        : amalgamation_dep a zz.
      Proof.
        use make_amalgamation_dep.
        - use closed_sieve_closed ; cbn.
          rewrite id_precomp_sieve.
          use (site_trans_sieve p).
          intros y g q.
          use sieve_contains_closed.
          pose (from_sieve_eq_l
                  (sieve_eq_from_closed (psh_term_naturality φ g a))
                  (identity _))
            as h.
          cbn in h.
          rewrite id_left in h.
          apply h.
          clear h.
          refine (from_sieve_eq_r
                    (sieve_eq_from_closed
                       (psh_term_pt_eq
                          φ
                          (amalgamation_restr a g q)))
                    (identity y)
                    _).
          cbn.
          rewrite id_left.
          exact (zz y g q).
        - intros y g q.
          apply propproperty.
      Qed.
    End SheafAmalgamation.

    Definition sheaf_predicate_to_dep_sheaf
      : dep_sheaf Γ.
    Proof.
      use make_dep_sheaf.
      - exact sheaf_predicate_to_dep_psh.
      - intros x ω p z a zz.
        use make_iscontr.
        + exact (sheaf_predicate_to_dep_sheaf_amalgamation p a zz).
        + intro aa.
          use amalgamation_dep_eq.
          apply propproperty.
    Defined.

    Definition sheaf_predicate_sub_psh
      : sheaf C
      := total_sheaf sheaf_predicate_to_dep_sheaf.

    Definition sheaf_predicate_incl
      : sheaf_nat_trans sheaf_predicate_sub_psh Γ.
    Proof.
      use make_sheaf_nat_trans.
      use make_nat_trans.
      - exact (λ x xx, pr1 xx).
      - abstract
          (intros x y f ;
           cbn ;
           apply idpath).
    Defined.

    Proposition isMonic_sheaf_predicate_incl
      : isMonic (C := cat_of_sheaves C) sheaf_predicate_incl.
    Proof.
      intros Δ s₁ s₂ p.
      use sheaf_nat_trans_eq.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use funextsec.
      intros xx.
      use subtypePath.
      {
        intro.
        apply propproperty.
      }
      exact (maponpaths (λ (z : sheaf_nat_trans (Δ : sheaf _) _), z x xx) p).
    Qed.
  End MonoPredicate.

  Section MonoPredicateEntail.
    Context {Γ₁ Γ₂ : sheaf C}
            {φ : sheaf_predicate Γ₁}
            {ψ : sheaf_predicate Γ₂}
            (s : sheaf_nat_trans Γ₁ Γ₂)
            (p : sheaf_predicate_entails φ (sheaf_predicate_subst s ψ)).

    Definition sheaf_predicate_entails_to_nat_trans
      : sheaf_nat_trans
          (sheaf_predicate_sub_psh φ)
          (sheaf_predicate_sub_psh ψ).
    Proof.
      use make_sheaf_nat_trans.
      use make_nat_trans.
      - exact (λ x xx, s x (pr1 xx) ,, p _ _ _ _ (pr2 xx)).
      - abstract
          (intros x y f ;
           use funextsec ;
           intro xx ;
           use subtypePath ; [ intro ; apply propproperty | ] ;
           cbn ;
           apply (eqtohomot (nat_trans_ax s _ _ f))).
    Defined.

    Proposition sheaf_predicate_entails_to_nat_trans_comm
      : nat_trans_comp
          _ _ _
          sheaf_predicate_entails_to_nat_trans
          (sheaf_predicate_incl ψ)
        =
        nat_trans_comp
          _ _ _
          (sheaf_predicate_incl φ)
          s.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
    Qed.
  End MonoPredicateEntail.

  Definition sheaf_logic_comprehension_data
    : disp_functor_data
        (functor_identity _)
        sheaf_predicate_disp_cat
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - intros Γ φ.
      simple refine ((_ ,, _) ,, _).
      + exact (sheaf_predicate_sub_psh φ).
      + exact (sheaf_predicate_incl φ).
      + exact (isMonic_sheaf_predicate_incl φ).
    - intros Γ₁ Γ₂ φ ψ s p.
      simple refine ((_ ,, _) ,, tt).
      + exact (sheaf_predicate_entails_to_nat_trans s p).
      + abstract
          (use sheaf_nat_trans_eq ;
           exact (sheaf_predicate_entails_to_nat_trans_comm s p)).
  Defined.

  Definition sheaf_logic_comprehension
    : disp_functor
        (functor_identity _)
        sheaf_predicate_disp_cat
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - exact sheaf_logic_comprehension_data.
    - abstract
        (split ;
         intros ;
         apply locally_propositional_mono_cod_disp_cat).
  Defined.

  Proposition sheaf_entails_from_mono_mor
              {Γ₁ Γ₂ : sheaf C}
              {φ : sheaf_predicate Γ₁}
              {ψ : sheaf_predicate Γ₂}
              (s : sheaf_nat_trans Γ₁ Γ₂)
              (f : sheaf_nat_trans
                     (sheaf_predicate_sub_psh φ)
                     (sheaf_predicate_sub_psh ψ))
              (q : nat_trans_comp
                     _ _ _
                     f
                     (sheaf_predicate_incl ψ)
                   =
                   nat_trans_comp
                     _ _ _
                     (sheaf_predicate_incl φ)
                     s)
    : sheaf_predicate_entails φ (sheaf_predicate_subst s ψ).
  Proof.
    intros x₁ x₂ g xx r ; cbn.
    pose (from_sieve_eq_l
            (sieve_eq_from_closed (psh_term_naturality ψ g (s x₁ xx)))
            (identity _))
      as h.
    cbn in h.
    rewrite id_left in h.
    apply h ; clear h.
    pose (from_sieve_eq_r
            (sieve_eq_from_closed (psh_term_naturality φ g xx))
            (identity _))
      as h.
    cbn in h.
    rewrite id_left in h.
    specialize (h r).
    pose (pr2 (f x₂ (#Γ₁ g xx ,, h))) as p.
    cbn in p.
    pose (eqtohomot (nat_trans_eq_pointwise q x₂) (#Γ₁ g xx ,, h)) as p'.
    cbn in p'.
    rewrite p' in p.
    clear p'.
    pose (eqtohomot (nat_trans_ax s _ _ g) xx) as p'.
    cbn in p'.
    rewrite p' in p.
    exact p.
  Qed.

  Proposition disp_functor_ff_sheaf_logic_comprehension
    : disp_functor_ff sheaf_logic_comprehension.
  Proof.
    intros Γ₁ Γ₂ φ ψ s.
    use isweq_iso.
    - cbn -[sheaf_predicate_entails].
      intro q.
      use sheaf_entails_from_mono_mor.
      + exact (pr11 q).
      + exact (maponpaths pr1 (pr21 q)).
    - intros.
      apply locally_propositional_sheaf_predicate_disp_cat.
    - intros.
      apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Section Eso.
    Context {Γ Δ : sheaf C}
            (τ : sheaf_nat_trans Δ Γ)
            (H : isMonic (C := cat_of_sheaves C) τ).

    Definition sheaf_monic_to_predicate_sieve
               (x : C)
               (γ : (Γ x : hSet))
      : sieve x.
    Proof.
      use make_sieve.
      - refine (λ y f, _).
        use make_hProp.
        + refine (∑ (δ : (Δ y : hSet)), τ y δ = #Γ f γ).
        + abstract
            (use invproofirrelevance ;
             intros [ δ₁ p₁ ] [ δ₂ p₂ ] ;
             use subtypePath ; [ intro ; apply setproperty | ] ;
             cbn ;
             use (isMonic_sheaf_injective H) ;
             exact (p₁ @ !p₂)).
      - abstract
          (cbn ; intros y₁ y₂ g₁ g₂ h p q ;
           induction p ;
           refine (#Δ h (pr1 q) ,, _) ;
           refine (_ @ eqtohomot (!(functor_comp Γ _ _)) _) ;
           cbn ;
           rewrite <- (pr2 q) ;
           exact (eqtohomot (nat_trans_ax τ _ _ h) _)).
    Defined.

    Definition closed_sheaf_monic_matching_family
               {x y : C}
               (γ : (Γ x : hSet))
               (f : y --> x)
      : matching_family Δ (f ^* sheaf_monic_to_predicate_sieve x γ).
    Proof.
      use make_matching_family.
      - exact (λ z h p, pr1 p).
      - abstract
          (cbn ;
           refine (λ z₁ z₂ g₁ g₂ h p q₁ q₂, _) ;
           induction p ;
           use (isMonic_sheaf_injective H) ;
           refine (_ @ !(pr2 q₁)) ;
           refine (eqtohomot (nat_trans_ax τ _ _ h) _ @ _) ;
           cbn ;
           rewrite assoc' ;
           refine (_ @ !(eqtohomot (functor_comp Γ _ h) _)) ;
           cbn ;
           apply maponpaths ;
           exact (pr2 q₂)).
    Defined.

    Proposition is_closed_sheaf_monic_to_predicate_sieve
                (x : C)
                (γ : (Γ x : hSet))
      : is_closed_sieve (sheaf_monic_to_predicate_sieve x γ).
    Proof.
      intros y f p.
      simple refine (_ ,, _) ; cbn.
      - use (sheaf_amalgamation (is_sheaf_sheaf Δ) p).
        exact (closed_sheaf_monic_matching_family γ f).
      - use (sheaf_amalgamation_unique
               (is_sheaf_sheaf Γ)
               p).
        + exact (nat_trans_matching_family τ (closed_sheaf_monic_matching_family γ f)).
        + intros z g q ; cbn.
          refine (!(eqtohomot (nat_trans_ax τ _ _ g) _) @ _).
          cbn.
          apply maponpaths.
          apply (amalgamation_restr
                   (sheaf_amalgamation
                      (is_sheaf_sheaf Δ)
                      p
                      (closed_sheaf_monic_matching_family γ f))
                   g).
        + intros z g q ; cbn ; cbn in q.
          refine (!(pr2 q @ _)).
          exact (eqtohomot (functor_comp Γ _ _) _).
    Defined.

    Definition sheaf_monic_to_predicate_ob
               (x : C)
               (γ : (Γ x : hSet))
      : closed_sieve x.
    Proof.
      use make_closed_sieve.
      - exact (sheaf_monic_to_predicate_sieve x γ).
      - exact (is_closed_sheaf_monic_to_predicate_sieve x γ).
    Defined.

    Proposition sheaf_monic_to_predicate_law
      : psh_term_law (A := subobject_classifier_dep_sheaf Γ) sheaf_monic_to_predicate_ob.
    Proof.
      intros x₁ x₂ f γ.
      cbn.
      use closed_sieve_eq.
      use sieve_eq.
      - intros z g [ δ p ].
        cbn in δ, p ; cbn.
        refine (δ ,, _).
        exact (p @ !(eqtohomot (functor_comp Γ _ _) _)).
      - intros z g [ δ p ].
        cbn in δ, p ; cbn.
        refine (δ ,, _).
        exact (p @ eqtohomot (functor_comp Γ _ _) _).
    Qed.

    Definition sheaf_monic_to_predicate
      : sheaf_predicate_disp_cat Γ.
    Proof.
      use make_psh_term.
      - exact sheaf_monic_to_predicate_ob.
      - exact sheaf_monic_to_predicate_law.
    Defined.

    Proposition sheaf_monic_to_predicate_nat_trans_laws
      : is_nat_trans
          (sheaf_predicate_sub_psh sheaf_monic_to_predicate)
          Δ
          (λ x xx, pr12 xx).
    Proof.
      intros x y f.
      use funextsec.
      intros xx.
      cbn.
      use (isMonic_sheaf_injective H).
      etrans.
      {
        exact (pr2 ((sheaf_predicate_to_dep_psh_mor sheaf_monic_to_predicate  _ _))).
      }
      cbn.
      refine (eqtohomot (functor_id Γ _) _ @ _).
      cbn.
      refine (!_ @ eqtohomot (!(nat_trans_ax τ _ _ f)) _).
      cbn.
      apply maponpaths.
      refine (pr22 xx @ _).
      exact (eqtohomot (functor_id Γ _) _).
    Qed.

    Definition sheaf_monic_to_predicate_nat_trans
      : sheaf_nat_trans
          (sheaf_predicate_sub_psh sheaf_monic_to_predicate)
          Δ.
    Proof.
      use make_sheaf_nat_trans.
      use make_nat_trans.
      - exact (λ x xx, pr12 xx).
      - exact sheaf_monic_to_predicate_nat_trans_laws.
    Defined.

    Definition sheaf_monic_to_predicate_nat_trans_inv_data
      : nat_trans_data
          Δ
          (sheaf_predicate_sub_psh sheaf_monic_to_predicate).
    Proof.
      refine (λ x xx, τ x xx ,, xx ,, _).
      exact (!(eqtohomot (functor_id Γ _) _)).
    Defined.

    Proposition sheaf_monic_to_predicate_nat_trans_inv_laws
      : is_nat_trans
          _ _
          sheaf_monic_to_predicate_nat_trans_inv_data.
    Proof.
      intros x y f.
      use funextsec ; intro xx.
      use dep_psh_total_space_path ; cbn.
      - exact (eqtohomot (nat_trans_ax τ _ _ f) xx).
      - use subtypePath.
        {
          intro.
          apply setproperty.
        }
        use (isMonic_sheaf_injective H).
        etrans.
        {
          exact (pr2 (sheaf_predicate_to_dep_psh_mor sheaf_monic_to_predicate  _ _)).
        }
        refine (!_).
        etrans.
        {
          exact (pr2 (sheaf_predicate_to_dep_psh_mor sheaf_monic_to_predicate  _ _)).
        }
        cbn.
        apply idpath.
    Qed.

    Definition sheaf_monic_to_predicate_nat_trans_inv
      : sheaf_nat_trans
          Δ
          (sheaf_predicate_sub_psh sheaf_monic_to_predicate).
    Proof.
      use make_sheaf_nat_trans.
      use make_nat_trans.
      - exact sheaf_monic_to_predicate_nat_trans_inv_data.
      - exact sheaf_monic_to_predicate_nat_trans_inv_laws.
    Defined.
  End Eso.

  Definition disp_functor_eso_disp_functor_ff_sheaf_logic_comprehension
    : disp_functor_disp_ess_split_surj sheaf_logic_comprehension.
  Proof.
    intros Γ [ [ Δ τ ] H ].
    cbn in Δ, τ, H.
    simple refine (_ ,, _).
    - exact (sheaf_monic_to_predicate τ H).
    - simple refine (_ ,, _ ,, _ ,, _).
      + simple refine ((_ ,, _) ,, tt).
        * exact (sheaf_monic_to_predicate_nat_trans τ H).
        * use sheaf_nat_trans_eq.
          use nat_trans_eq.
          {
            apply homset_property.
          }
          intro x.
          cbn.
          use funextsec.
          intros [ γ [ δ p ] ].
          cbn in *.
          refine (p @ _).
          exact (eqtohomot (functor_id (pr1 Γ) _) _).
      + simple refine ((_ ,, _) ,, tt).
        * exact (sheaf_monic_to_predicate_nat_trans_inv τ H).
        * use sheaf_nat_trans_eq.
          use nat_trans_eq.
          {
            apply homset_property.
          }
          intro x.
          cbn.
          apply idpath.
      + use subtypePath.
        {
          intro.
          apply isapropunit.
        }
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        rewrite transportb_mono_cod_disp.
        use sheaf_nat_trans_eq.
        use nat_trans_eq.
        {
          apply homset_property.
        }
        cbn.
        intro.
        apply idpath.
      + use subtypePath.
        {
          intro.
          apply isapropunit.
        }
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        rewrite transportb_mono_cod_disp.
        use sheaf_nat_trans_eq.
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x.
        use funextsec.
        intros [ xx [ δ p ]] ; cbn in δ, p.
        use dep_psh_total_space_path.
        * exact (p @ eqtohomot (functor_id (pr1 Γ) _) _).
        * cbn.
          use subtypePath.
          {
            intro.
            apply setproperty.
          }
          cbn.
          use (isMonic_sheaf_injective H).
          etrans.
          {
            exact (pr2 (sheaf_predicate_to_dep_psh_mor
                          (sheaf_monic_to_predicate τ H)
                          _ _)).
          }
          cbn.
          exact (!p).
  Qed.
End SheafLogic.
