(**

 The first-order hyperdoctrine of predicates for presheaves

 We already gave concrete descriptions of connectives for predicates of presheaves
 in the file `PresheafLogic`. Here we assemble these operations to construct a
 first-order hyperdoctrine over the category of presheaves. In addition, we construct
 an equivalence between this hyperdoctrine and the one arising from monomorphisms in
 the category of presheaves.

 Content
 1. The displayed category of predicates over presheaves
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
Require Import UniMath.CategoryTheory.Presheaves.PresheafLogic.

Local Open Scope cat.

Section PresheafLogic.
  Context {C : category}.

  (** * 1. The displayed category of predicates over presheaves *)
  Definition presheaf_predicate_disp_cat_ob_mor
    : disp_cat_ob_mor (PreShv C).
  Proof.
    simple refine (_ ,, _).
    - exact presheaf_predicate.
    - exact (λ Γ₁ Γ₂ φ ψ s, presheaf_predicate_entails φ (presheaf_predicate_subst s ψ)).
  Defined.

  Proposition presheaf_predicate_disp_cat_id_comp
    : disp_cat_id_comp _ presheaf_predicate_disp_cat_ob_mor.
  Proof.
    split.
    - intros Γ φ x y f xx p.
      exact p.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ φ₁ φ₂ φ₃ p q x y f xx r.
      refine (q x y f _ _).
      exact (p x y f xx r).
  Qed.

  Definition presheaf_predicate_disp_cat_data
    : disp_cat_data (PreShv C).
  Proof.
    simple refine (_ ,, _).
    - exact presheaf_predicate_disp_cat_ob_mor.
    - exact presheaf_predicate_disp_cat_id_comp.
  Defined.

  Proposition presheaf_predicate_disp_cat_axioms
    : disp_cat_axioms _ presheaf_predicate_disp_cat_data.
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

  Definition presheaf_predicate_disp_cat
    : disp_cat (PreShv C).
  Proof.
    simple refine (_ ,, _).
    - exact presheaf_predicate_disp_cat_data.
    - exact presheaf_predicate_disp_cat_axioms.
  Defined.

  Proposition locally_propositional_presheaf_predicate_disp_cat
    : locally_propositional presheaf_predicate_disp_cat.
  Proof.
    intros Γ₁ Γ₂ s φ ψ.
    apply propproperty.
  Qed.

  (** * 2. This displayed category is univalent *)
  Proposition is_univalent_disp_presheaf_predicate_disp_cat
    : is_univalent_disp presheaf_predicate_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros Γ₁ φ ψ.
    use isweqimplimpl.
    - intro p.
      use psh_term_eq.
      intros x xx.
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
        apply locally_propositional_presheaf_predicate_disp_cat.
  Qed.

  (** * 3. A cleaving for this displayed category *)
  Section CartesianLift.
    Context {Γ₁ Γ₂ : C^op ⟶ SET}
            (s : Γ₁ ⟹ Γ₂)
            (φ : presheaf_predicate Γ₂).

    Proposition cleaving_presheaf_predicate_disp_cat_entails
      : presheaf_predicate_entails
          (presheaf_predicate_subst s φ)
          (presheaf_predicate_subst s φ).
    Proof.
      intros x y f xx p ; cbn in *.
      exact p.
    Qed.

    Proposition is_cartesian_cleaving_presheaf_predicate_disp_cat_entails
      : is_cartesian
          (D := presheaf_predicate_disp_cat)
          cleaving_presheaf_predicate_disp_cat_entails.
    Proof.
      intros Γ₀ s' ψ p.
      use make_iscontr.
      - simple refine (_ ,, _).
        + intros x y f xx q.
          exact (p x y f xx q).
        + apply locally_propositional_presheaf_predicate_disp_cat.
      - intro t.
        use subtypePath.
        {
          intro.
          apply homsets_disp.
        }
        apply locally_propositional_presheaf_predicate_disp_cat.
    Qed.
  End CartesianLift.

  Definition cleaving_presheaf_predicate_disp_cat
    : cleaving presheaf_predicate_disp_cat.
  Proof.
    intros Γ₁ Γ₂ s φ.
    simple refine (_ ,, _).
    - exact (presheaf_predicate_subst s φ).
    - simple refine (_ ,, _).
      + exact (cleaving_presheaf_predicate_disp_cat_entails s φ).
      + exact (is_cartesian_cleaving_presheaf_predicate_disp_cat_entails s φ).
  Defined.

  (** * 4. The connectives *)
  Definition presheaf_predicate_fiberwise_terminal
    : fiberwise_terminal cleaving_presheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_terminal_locally_propositional.
    - exact locally_propositional_presheaf_predicate_disp_cat.
    - exact truth_presheaf_predicate.
    - exact (λ Γ φ, truth_presheaf_intro φ).
    - exact (λ Γ₁ Γ₂ s, truth_presheaf_subst s).
  Defined.

  Definition presheaf_predicate_fiberwise_initial
    : fiberwise_initial cleaving_presheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_initial_locally_propositional.
    - exact locally_propositional_presheaf_predicate_disp_cat.
    - exact false_presheaf_predicate.
    - exact (λ Γ φ, false_presheaf_elim φ).
    - exact (λ Γ₁ Γ₂ s, false_presheaf_subst s).
  Defined.

  Definition presheaf_predicate_fiberwise_binproducts
    : fiberwise_binproducts cleaving_presheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_binproducts_locally_propositional.
    - exact locally_propositional_presheaf_predicate_disp_cat.
    - exact (λ Γ φ ψ, conj_presheaf_predicate φ ψ).
    - exact (λ Γ φ ψ, conj_presheaf_elim_l φ ψ).
    - exact (λ Γ φ ψ, conj_presheaf_elim_r φ ψ).
    - exact (λ Γ φ ψ χ p₁ p₂, conj_presheaf_intro p₁ p₂).
    - exact (λ Γ₁ Γ₂ s φ ψ, conj_presheaf_subst s φ ψ).
  Defined.

  Definition presheaf_predicate_fiberwise_bincoproducts
    : fiberwise_bincoproducts cleaving_presheaf_predicate_disp_cat.
  Proof.
    use make_fiberwise_bincoproducts_locally_propositional.
    - exact locally_propositional_presheaf_predicate_disp_cat.
    - exact (λ Γ φ ψ, disj_presheaf_predicate φ ψ).
    - exact (λ Γ φ ψ, disj_presheaf_intro_l φ ψ).
    - exact (λ Γ φ ψ, disj_presheaf_intro_r φ ψ).
    - exact (λ Γ φ ψ χ p₁ p₂, disj_presheaf_elim p₁ p₂).
    - exact (λ Γ₁ Γ₂ s φ ψ, disj_presheaf_subst s φ ψ).
  Defined.

  Definition presheaf_predicate_fiberwise_exponentials
    : fiberwise_exponentials presheaf_predicate_fiberwise_binproducts.
  Proof.
    use make_fiberwise_exponentials_locally_propositional.
    - exact locally_propositional_presheaf_predicate_disp_cat.
    - exact (λ Γ φ ψ, impl_presheaf_predicate φ ψ).
    - exact (λ Γ φ ψ, impl_presheaf_elim φ ψ).
    - exact (λ Γ φ ψ χ p, impl_presheaf_intro p).
    - exact (λ Γ₁ Γ₂ s φ ψ, impl_presheaf_subst s φ ψ).
  Defined.

  Definition presheaf_logic_hyperdoctrine
    : hyperdoctrine.
  Proof.
    use make_hyperdoctrine.
    - exact (PreShv C).
    - exact presheaf_predicate_disp_cat.
    - exact Terminal_PreShv.
    - exact BinProducts_PreShv.
    - exact cleaving_presheaf_predicate_disp_cat.
    - exact locally_propositional_presheaf_predicate_disp_cat.
    - exact is_univalent_disp_presheaf_predicate_disp_cat.
  Defined.

  Definition presheaf_logic_universal_quantifiers
    : universal_quantifiers presheaf_logic_hyperdoctrine.
  Proof.
    use universal_quantifiers_from_chosen.
    use make_universal_quantifiers_chosen.
    - exact (λ Γ A φ, forall_presheaf_predicate φ).
    - exact (λ Γ A φ, forall_presheaf_intro φ).
    - exact (λ Γ A φ ψ p, forall_presheaf_elim p).
    - abstract
        (cbn ; unfold prodtofuntoprod ; cbn ;
         intros Γ₁ Γ₂ A s φ x₁ x₂ f xx H y g aa ;
         refine (from_sieve_eq_r
                   (psh_term_pt_eq
                      φ
                      (maponpaths
                         (λ z, z ,, aa)
                         (!(eqtohomot (nat_trans_ax s _ _ (g · f)) _))))
                   _
                   _) ;
         cbn ;
         rewrite id_left ;
         apply H).
  Defined.

  Definition presheaf_logic_existential_quantifiers
    : existential_quantifiers presheaf_logic_hyperdoctrine.
  Proof.
    use existential_quantifiers_from_chosen.
    use make_existential_quantifiers_chosen.
    - exact (λ Γ A φ, exists_presheaf_predicate φ).
    - exact (λ Γ A φ, exists_presheaf_intro φ).
    - exact (λ Γ A φ ψ p, exists_presheaf_elim p).
    - abstract
        (intros Γ₁ Γ₂ A s φ x₁ x₂ f xx ;
         use factor_through_squash_hProp ;
         intros [ aa p ] ; cbn in aa, p ;
         use hinhpr ;
         cbn ; unfold prodtofuntoprod ; cbn ;
         refine (aa ,, _) ;
         refine (from_sieve_eq_r
                   (psh_term_pt_eq
                      φ
                      (maponpaths
                         (λ z, z ,, aa)
                         (eqtohomot (nat_trans_ax s _ _ f) _)))
                   _
                   _) ;
         cbn ;
         rewrite id_left ;
         exact p).
  Defined.

  Definition presheaf_logic_equality_formulas
    : equality_formulas presheaf_logic_hyperdoctrine.
  Proof.
    use make_equality_formulas.
    - exact (λ Γ φ, eq_presheaf_predicate φ).
    - exact (λ Γ φ, eq_presheaf_intro φ).
    - exact (λ Γ φ ψ p, eq_presheaf_elim p).
  Defined.

  Definition presheaf_logic_first_order_hyperdoctrine
    : first_order_hyperdoctrine.
  Proof.
    use make_first_order_hyperdoctrine.
    - exact presheaf_logic_hyperdoctrine.
    - exact presheaf_predicate_fiberwise_terminal.
    - exact presheaf_predicate_fiberwise_initial.
    - exact presheaf_predicate_fiberwise_binproducts.
    - exact presheaf_predicate_fiberwise_bincoproducts.
    - exact presheaf_predicate_fiberwise_exponentials.
    - exact presheaf_logic_universal_quantifiers.
    - exact presheaf_logic_existential_quantifiers.
    - exact presheaf_logic_equality_formulas.
  Defined.

  (** * 5. Equivalence with the category of monomorphisms *)
  Section MonoPredicate.
    Context {Γ : C^op ⟶ HSET}
            (φ : presheaf_predicate Γ).

    Definition presheaf_predicate_to_dep_psh_mor
               {x y : C}
               {xx : (Γ x : hSet)}
               {yy : (Γ y : hSet)}
               {s : y --> x}
               (p : # Γ s xx = yy)
               (q : (φ x xx : sieve _) x (identity x))
      : (φ y yy : sieve _) y (identity y).
    Proof.
      induction p.
      cbn ; cbn in q.
      apply (from_sieve_eq_r (psh_term_naturality φ s xx) (identity y)).
      refine (#ω (φ x xx) s _ q).
      cbn.
      rewrite id_left, id_right.
      apply idpath.
    Qed.

    Definition presheaf_predicate_to_dep_psh
      : dep_psh Γ.
    Proof.
      use make_dep_psh.
      - exact (λ x xx, hProp_to_hSet ((φ x xx : sieve x) x (identity x))).
      - intros x y xx yy s p q.
        exact (presheaf_predicate_to_dep_psh_mor p q).
      - abstract
          (intros ;
           apply propproperty).
      - abstract
          (intros ;
           apply propproperty).
    Defined.

    Definition presheaf_predicate_sub_psh
      : C^op ⟶ HSET
      := total_psh presheaf_predicate_to_dep_psh.

    Definition presheaf_predicate_incl
      : presheaf_predicate_sub_psh ⟹ Γ.
    Proof.
      use make_nat_trans.
      - exact (λ x xx, pr1 xx).
      - abstract
          (intros x y f ;
           cbn ;
           apply idpath).
    Defined.

    Proposition isMonic_presheaf_predicate_incl
      : isMonic (C := PreShv C) presheaf_predicate_incl.
    Proof.
      intros Δ s₁ s₂ p.
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
      exact (maponpaths (λ (z : (Δ : _ ⟶ _) ⟹ _), z x xx) p).
    Qed.
  End MonoPredicate.

  Section MonoPredicateEntail.
    Context {Γ₁ Γ₂ : C^op ⟶ HSET}
            {φ : presheaf_predicate Γ₁}
            {ψ : presheaf_predicate Γ₂}
            (s : Γ₁ ⟹ Γ₂)
            (p : presheaf_predicate_entails φ (presheaf_predicate_subst s ψ)).

    Definition presheaf_predicate_entails_to_nat_trans
      : presheaf_predicate_sub_psh φ ⟹ presheaf_predicate_sub_psh ψ.
    Proof.
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

    Proposition presheaf_predicate_entails_to_nat_trans_comm
      : nat_trans_comp
          _ _ _
          presheaf_predicate_entails_to_nat_trans
          (presheaf_predicate_incl ψ)
        =
        nat_trans_comp
          _ _ _
          (presheaf_predicate_incl φ)
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

  Definition presheaf_logic_comprehension_data
    : disp_functor_data
        (functor_identity _)
        presheaf_predicate_disp_cat
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - intros Γ φ.
      simple refine ((_ ,, _) ,, _).
      + exact (presheaf_predicate_sub_psh φ).
      + exact (presheaf_predicate_incl φ).
      + exact (isMonic_presheaf_predicate_incl φ).
    - intros Γ₁ Γ₂ φ ψ s p.
      simple refine ((_ ,, _) ,, tt).
      + exact (presheaf_predicate_entails_to_nat_trans s p).
      + exact (presheaf_predicate_entails_to_nat_trans_comm s p).
  Defined.

  Definition presheaf_logic_comprehension
    : disp_functor
        (functor_identity _)
        presheaf_predicate_disp_cat
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - exact presheaf_logic_comprehension_data.
    - abstract
        (split ;
         intros ;
         apply locally_propositional_mono_cod_disp_cat).
  Defined.

  Proposition presheaf_entails_from_mono_mor
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              {φ : presheaf_predicate Γ₁}
              {ψ : presheaf_predicate Γ₂}
              (s : Γ₁ ⟹ Γ₂)
              (f : presheaf_predicate_sub_psh φ
                   ⟹
                   presheaf_predicate_sub_psh ψ)
              (q : nat_trans_comp
                     _ _ _
                     f
                     (presheaf_predicate_incl ψ)
                   =
                   nat_trans_comp
                     _ _ _
                     (presheaf_predicate_incl φ)
                     s)
    : presheaf_predicate_entails φ (presheaf_predicate_subst s ψ).
  Proof.
    intros x₁ x₂ g xx r ; cbn.
    pose (from_sieve_eq_l (psh_term_naturality ψ g (s x₁ xx)) (identity _)) as h.
    cbn in h.
    rewrite id_left in h.
    apply h ; clear h.
    pose (from_sieve_eq_r (psh_term_naturality φ g xx) (identity _)) as h.
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

  Proposition disp_functor_ff_presheaf_logic_comprehension
    : disp_functor_ff presheaf_logic_comprehension.
  Proof.
    intros Γ₁ Γ₂ φ ψ s.
    use isweq_iso.
    - cbn -[presheaf_predicate_entails].
      intro q.
      use presheaf_entails_from_mono_mor.
      + exact (pr11 q).
      + exact (pr21 q).
    - intros.
      apply locally_propositional_presheaf_predicate_disp_cat.
    - intros.
      apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Section Eso.
    Context {Γ Δ : C^op ⟶ HSET}
            (τ : Δ ⟹ Γ)
            (H : isMonic (C := PreShv C) τ).

    Definition presheaf_monic_to_predicate_ob
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
             use (isMonic_presheaf_injective H) ;
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

    Proposition presheaf_monic_to_predicate_law
      : psh_term_law (A := dep_psh_subobject_classifier_ob Γ) presheaf_monic_to_predicate_ob.
    Proof.
      intros x y f γ.
      cbn.
      use sieve_eq.
      - cbn.
        intros z g [ δ p ].
        refine (δ ,, _).
        exact (p @ !(eqtohomot (functor_comp Γ _ _) _)).
      - cbn.
        intros z g [ δ p ].
        refine (δ ,, _).
        exact (p @ eqtohomot (functor_comp Γ _ _) _).
    Qed.

    Definition presheaf_monic_to_predicate
      : presheaf_predicate_disp_cat Γ.
    Proof.
      use make_psh_term.
      - exact presheaf_monic_to_predicate_ob.
      - exact presheaf_monic_to_predicate_law.
    Defined.

    Proposition presheaf_monic_to_predicate_nat_trans_laws
      : is_nat_trans
          (total_psh (presheaf_predicate_to_dep_psh presheaf_monic_to_predicate))
          Δ
          (λ x xx, pr12 xx).
    Proof.
      intros x y f.
      use funextsec.
      intros xx.
      cbn.
      use (isMonic_presheaf_injective H).
      etrans.
      {
        exact (pr2 ((presheaf_predicate_to_dep_psh_mor presheaf_monic_to_predicate  _ _))).
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

    Definition presheaf_monic_to_predicate_nat_trans
      : total_psh (presheaf_predicate_to_dep_psh presheaf_monic_to_predicate) ⟹ Δ.
    Proof.
      use make_nat_trans.
      - exact (λ x xx, pr12 xx).
      - exact presheaf_monic_to_predicate_nat_trans_laws.
    Defined.

    Definition presheaf_monic_to_predicate_nat_trans_inv_data
      : nat_trans_data
          Δ
          (total_psh (presheaf_predicate_to_dep_psh presheaf_monic_to_predicate)).
    Proof.
      refine (λ x xx, τ x xx ,, xx ,, _).
      exact (!(eqtohomot (functor_id Γ _) _)).
    Defined.

    Proposition presheaf_monic_to_predicate_nat_trans_inv_laws
      : is_nat_trans
          _ _
          presheaf_monic_to_predicate_nat_trans_inv_data.
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
        use (isMonic_presheaf_injective H).
        etrans.
        {
          exact (pr2 (presheaf_predicate_to_dep_psh_mor presheaf_monic_to_predicate  _ _)).
        }
        refine (!_).
        etrans.
        {
          exact (pr2 (presheaf_predicate_to_dep_psh_mor presheaf_monic_to_predicate  _ _)).
        }
        cbn.
        apply idpath.
    Qed.

    Definition presheaf_monic_to_predicate_nat_trans_inv
      : Δ ⟹ total_psh (presheaf_predicate_to_dep_psh presheaf_monic_to_predicate).
    Proof.
      use make_nat_trans.
      - exact presheaf_monic_to_predicate_nat_trans_inv_data.
      - exact presheaf_monic_to_predicate_nat_trans_inv_laws.
    Defined.
  End Eso.

  Definition disp_functor_eso_disp_functor_ff_presheaf_logic_comprehension
    : disp_functor_disp_ess_split_surj presheaf_logic_comprehension.
  Proof.
    intros Γ [ [ Δ τ ] H ].
    cbn in Δ, τ, H.
    simple refine (_ ,, _).
    - exact (presheaf_monic_to_predicate τ H).
    - simple refine (_ ,, _ ,, _ ,, _).
      + simple refine ((_ ,, _) ,, tt).
        * exact (presheaf_monic_to_predicate_nat_trans τ H).
        * use nat_trans_eq.
          {
            apply homset_property.
          }
          intro x.
          cbn.
          use funextsec.
          intros [ γ [ δ p ] ].
          cbn in *.
          refine (p @ _).
          exact (eqtohomot (functor_id Γ _) _).
      + simple refine ((_ ,, _) ,, tt).
        * exact (presheaf_monic_to_predicate_nat_trans_inv τ H).
        * use nat_trans_eq.
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
        use nat_trans_eq.
        {
          apply homset_property.
        }
        intro x.
        use funextsec.
        intros [ xx [ δ p ]] ; cbn in δ, p.
        use dep_psh_total_space_path.
        * exact (p @ eqtohomot (functor_id Γ _) _).
        * cbn.
          use subtypePath.
          {
            intro.
            apply setproperty.
          }
          cbn.
          use (isMonic_presheaf_injective H).
          etrans.
          {
            exact (pr2 (presheaf_predicate_to_dep_psh_mor
                          (presheaf_monic_to_predicate τ H)
                          _ _)).
          }
          cbn.
          exact (!p).
  Qed.
End PresheafLogic.
