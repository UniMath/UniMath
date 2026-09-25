(**

 The Rezk completion of first-order hyperdoctrines

 We show that every first-order hyperdoctrine admits a Rezk completion that is again
 a first-order hyperdoctrine. To do so, we take two steps.
 1. Starting with a displayed category `D` whose displayed morphisms are propositions,
    We construct a new displayed category where we quotient the objects. Two objects
    are identified if we have an isomorphism between them. We also show that we have a
    weak equivalence to the displayed category that we constructed.
 2. We show that the resulting category has the structure of a first-order hyperdoctrine.
    These statements have been proven in the file `Completion.WeakEquivs`.

 The following observation is important: the Rezk completion of a tripos in general only
 gives a weak tripos. The difference between triposes and triposes lies in how we specify
 the comprehension operation. For a tripos, comprehension is given as an actual term,
 but for a weak tripos, comprehension is expressed as an axiom (see Axiom CA in 'Tripos
 Theory in Retrospect'). We can thus only acquire comprehension in a weak tripos in a
 proof after doing existential elimination. If we take the Rezk completion of a tripos,
 then to define the comprehension operation we need to pick a representative and that
 requires the axiom of choice. This usage of choice is present in Example 4.5 of 'Tripos
 Theory in Retrospect'.

 References
 - 'Tripos Theory in Retrospect' by Pitts

 Content
 1. The construction of the displayed category
 2. It is univalent
 3. The weak equivalence
 4. The completion of preorder hyperdoctrines
 5. The completion of first-order hyperdoctrines
 6. Preservation
 7. The completion of triposes

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCartesianClosed.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Completion.WeakEquivs.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Exponentials.

Local Open Scope cat.

Section HyperdoctrineCompletion.
  Context {C : category}
          (D : disp_cat C)
          (HD : locally_propositional D).

  (** * 1. The construction of the displayed category *)
  Definition locally_propositional_z_iso_hrel
             (x : C)
    : hrel (D x).
  Proof.
    intros xx yy.
    use make_hProp.
    - exact (z_iso_disp (identity_z_iso _) xx yy).
    - abstract
        (use isaproptotal2 ;
         [ intro ; apply isaprop_is_z_iso_disp | ] ;
         intros ;
         apply HD).
  Defined.

  Definition locally_propositional_z_iso_eqrel
             (x : C)
    : eqrel (D x).
  Proof.
    use make_eqrel.
    - exact (locally_propositional_z_iso_hrel x).
    - repeat split.
      + intros xx yy zz ff gg ; cbn.
        refine (transportf
                  (λ z, z_iso_disp z _ _)
                  _
                  (z_iso_disp_comp ff gg)).
        abstract
          (use z_iso_eq ;
           apply id_left).
      + intros xx ; cbn.
        apply identity_z_iso_disp.
      + intros xx yy ff ; cbn.
        exact (z_iso_inv_from_z_iso_disp ff).
  Defined.

  Definition hyperdoctrine_completion_disp_cat_disp_ob
             (x : C)
    : UU
    := setquot (locally_propositional_z_iso_eqrel x).

  Definition hyperdoctrine_completion_disp_cat_disp_mor
             {x y : C}
             (f : x --> y)
             (xx : hyperdoctrine_completion_disp_cat_disp_ob x)
             (yy : hyperdoctrine_completion_disp_cat_disp_ob y)
    : hProp_set.
  Proof.
    revert xx.
    use setquotuniv.
    - intros xx.
      revert yy.
      use setquotuniv.
      + intros yy.
        use make_hProp.
        * exact (xx -->[ f ] yy).
        * apply HD.
      + intros yy₁ yy₂ gg ; cbn in gg.
        use hPropUnivalence ; cbn.
        * intros ff.
          refine (transportf
                    (λ z, _ -->[ z ] _)
                    _
                    (ff ;; gg)%mor_disp).
          apply id_right.
        * intros ff.
          refine (transportf
                    (λ z, _ -->[ z ] _)
                    _
                    (ff ;; inv_mor_disp_from_z_iso gg)%mor_disp).
          apply id_right.
    - intros xx₁ xx₂ ff ; cbn in ff.
      revert yy.
      use setquotunivprop'.
      {
        intro.
        apply setproperty.
      }
      intros yy.
      use hPropUnivalence ; cbn.
      + intros gg.
        refine (transportf
                  (λ z, _ -->[ z ] _)
                  _
                  (inv_mor_disp_from_z_iso ff ;; gg)%mor_disp).
        apply id_left.
      + intros gg.
        refine (transportf
                  (λ z, _ -->[ z ] _)
                  _
                  (ff ;; gg)%mor_disp).
        apply id_left.
  Defined.

  Definition hyperdoctrine_completion_disp_cat_ob_mor
    : disp_cat_ob_mor C.
  Proof.
    simple refine (_ ,, _).
    - exact hyperdoctrine_completion_disp_cat_disp_ob.
    - exact (λ x y xx yy f, hyperdoctrine_completion_disp_cat_disp_mor f xx yy : hProp).
  Defined.

  Definition hyperdoctrine_completion_disp_cat_id_comp
    : disp_cat_id_comp C hyperdoctrine_completion_disp_cat_ob_mor.
  Proof.
    split.
    - intros x.
      use setquotunivprop'.
      {
        intro.
        apply propproperty.
      }
      intros xx ; cbn.
      apply id_disp.
    - intros x y z f g xx yy.
      use setquotunivprop'.
      {
        intro.
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros zz ; cbn.
      revert yy.
      use setquotunivprop'.
      {
        intro.
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros yy ; cbn.
      revert xx.
      use setquotunivprop'.
      {
        intro.
        repeat (use impred ; intro).
        apply propproperty.
      }
      intros xx ; cbn.
      intros ff gg.
      exact (ff ;; gg)%mor_disp.
  Qed.

  Definition hyperdoctrine_completion_disp_cat_data
    : disp_cat_data C.
  Proof.
    simple refine (_ ,, _).
    - exact hyperdoctrine_completion_disp_cat_ob_mor.
    - exact hyperdoctrine_completion_disp_cat_id_comp.
  Defined.

  Proposition locally_propositional_hyperdoctrine_completion_disp_cat
    : locally_propositional hyperdoctrine_completion_disp_cat_data.
  Proof.
    intro ; intros.
    apply propproperty.
  Qed.

  Proposition hyperdoctrine_completion_disp_cat_laws
    : disp_cat_axioms C hyperdoctrine_completion_disp_cat_data.
  Proof.
    repeat split.
    - intro ; intros.
      apply locally_propositional_hyperdoctrine_completion_disp_cat.
    - intro ; intros.
      apply locally_propositional_hyperdoctrine_completion_disp_cat.
    - intro ; intros.
      apply locally_propositional_hyperdoctrine_completion_disp_cat.
    - intro ; intros.
      apply isasetaprop.
      apply locally_propositional_hyperdoctrine_completion_disp_cat.
  Qed.

  Definition hyperdoctrine_completion_disp_cat
    : disp_cat C.
  Proof.
    simple refine (_ ,, _).
    - exact hyperdoctrine_completion_disp_cat_data.
    - exact hyperdoctrine_completion_disp_cat_laws.
  Defined.

  (** * 2. It is univalent *)
  Proposition is_univalent_disp_hyperdoctrine_completion_disp_cat
    : is_univalent_disp hyperdoctrine_completion_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros x.
    use setquotunivprop'.
    {
      intro.
      use impred ; intro.
      apply isapropisweq.
    }
    intros xx.
    use setquotunivprop'.
    {
      intro.
      apply isapropisweq.
    }
    intros yy.
    use isweqimplimpl.
    - intros ff.
      use iscompsetquotpr.
      induction ff as [ ff [ gg _ ]].
      cbn in ff, gg.
      refine (ff ,, gg ,, _).
      split ; apply HD.
    - apply isasetsetquot.
    - use isaproptotal2.
      {
        intro.
        apply isaprop_is_z_iso_disp.
      }
      intros.
      apply HD.
  Qed.

  (** * 3. The weak equivalence *)
  Definition hyperdoctrine_completion_disp_cat_functor_data
    : disp_functor_data
        (functor_identity _)
        D
        hyperdoctrine_completion_disp_cat.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, setquotpr _ xx).
    - exact (λ x y xx yy f ff, ff).
  Defined.

  Definition hyperdoctrine_completion_disp_cat_functor
    : disp_functor
        (functor_identity _)
        D
        hyperdoctrine_completion_disp_cat.
  Proof.
    simple refine (_ ,, _).
    - exact hyperdoctrine_completion_disp_cat_functor_data.
    - abstract
        (split ;
         intros ;
         apply locally_propositional_hyperdoctrine_completion_disp_cat).
  Defined.

  Proposition disp_functor_ff_hyperdoctrine_completion_disp_cat_functor
    : disp_functor_ff hyperdoctrine_completion_disp_cat_functor.
  Proof.
    intros x y xx yy f.
    apply idisweq.
  Qed.

  Proposition disp_functor_disp_ess_surj_hyperdoctrine_completion_disp_cat_functor
    : disp_functor_disp_ess_surj hyperdoctrine_completion_disp_cat_functor.
  Proof.
    intros x.
    use setquotunivprop.
    intros xx.
    use hinhpr.
    refine (xx ,, _).
    apply identity_z_iso_disp.
  Qed.
End HyperdoctrineCompletion.

(** * 4. The completion of preorder hyperdoctrines *)
Definition preorder_hyperdoctrine_completion
           (H : preorder_hyperdoctrine)
  : hyperdoctrine.
Proof.
  use make_hyperdoctrine.
  - exact (hyperdoctrine_type_category H).
  - refine (hyperdoctrine_completion_disp_cat
              (hyperdoctrine_formula_disp_cat H)
              _).
    exact (locally_propositional_preorder_hyperdoctrine H).
  - exact (hyperdoctrine_terminal_type H).
  - exact (hyperdoctrine_binproducts H).
  - refine (disp_functor_weak_equivalence_cleaving
              (hyperdoctrine_completion_disp_cat_functor _ _)
              (disp_functor_ff_hyperdoctrine_completion_disp_cat_functor _ _)
              (disp_functor_disp_ess_surj_hyperdoctrine_completion_disp_cat_functor _ _)
              _
              _
              (hyperdoctrine_cleaving H)).
    + exact (pr22 (pr222 H)).
    + apply is_univalent_disp_hyperdoctrine_completion_disp_cat.
  - apply locally_propositional_hyperdoctrine_completion_disp_cat.
  - apply is_univalent_disp_hyperdoctrine_completion_disp_cat.
Defined.

Definition preorder_hyperdoctrine_z_iso_eqrel
           (H : preorder_hyperdoctrine)
           (A : (ty H)%hd)
  : eqrel (hyperdoctrine_formula_disp_cat H A)
  := locally_propositional_z_iso_eqrel
       (hyperdoctrine_formula_disp_cat H)
       (pr22 (pr222 H))
       A.

(** * 5. The completion of first-order hyperdoctrines *)
Definition first_order_preorder_hyperdoctrine_completion
           (H : first_order_preorder_hyperdoctrine)
  : first_order_hyperdoctrine.
Proof.
  use make_first_order_hyperdoctrine.
  - exact (preorder_hyperdoctrine_completion H).
  - use disp_functor_weak_equivalence_fiberwise_terminal.
    apply H.
  - use disp_functor_weak_equivalence_fiberwise_initial.
    apply H.
  - use disp_functor_weak_equivalence_fiberwise_binproducts.
    apply H.
  - use disp_functor_weak_equivalence_fiberwise_bincoproducts.
    apply H.
  - use disp_functor_weak_equivalence_fiberwise_exponentials.
    exact (pr122 (pr222 H)).
  - simple refine (_ ,, _).
    + intros Γ A.
      use disp_functor_weak_equivalence_dependent_product.
      exact (pr11 (pr222 (pr222 H)) Γ A).
    + abstract
        (intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ ;
         use make_is_z_isomorphism ;
         [ | split ; apply locally_propositional_hyperdoctrine_completion_disp_cat] ;
         use (disp_functor_weak_equivalence_dependent_product_stable
                (hyperdoctrine_completion_disp_cat_functor _ _)
                _
                _
                _
                _
                _
                (pr11 (pr222 (pr222 H)) Γ₂ A₂)
                (pr11 (pr222 (pr222 H)) Γ₁ A₁)
                φ) ;
         intros ψ ;
         exact (pr1 (pr21 (pr222 (pr222 H)) _ _ _ _ _ _ p Hp ψ))).
  - simple refine (_ ,, _).
    + intros Γ A.
      use disp_functor_weak_equivalence_dependent_sum.
      exact (pr112 (pr222 (pr222 H)) Γ A).
    + abstract
        (intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ ;
         use make_is_z_isomorphism ;
         [ | split ; apply locally_propositional_hyperdoctrine_completion_disp_cat] ;
         use (disp_functor_weak_equivalence_dependent_sum_stable
                (hyperdoctrine_completion_disp_cat_functor _ _)
                _
                _
                _
                _
                _
                (pr112 (pr222 (pr222 H)) Γ₂ A₂)
                (pr112 (pr222 (pr222 H)) Γ₁ A₁)
                φ) ;
         intros ψ ;
         exact (pr1 (pr212 (pr222 (pr222 H)) _ _ _ _ _ _ p Hp ψ))).
  - intro A.
    use disp_functor_weak_equivalence_dependent_sum.
    exact (pr22 (pr222 (pr222 H)) A).
Defined.

Local Open Scope hyperdoctrine.

Proposition first_order_preorder_hyperdoctrine_completion_form_subst
            {H : first_order_preorder_hyperdoctrine}
            (Hc := first_order_preorder_hyperdoctrine_completion H)
            {Γ₁ Γ₂ : ty H}
            (s : Γ₁ --> Γ₂)
            (φ : form Γ₂)
  : setquotpr
      (preorder_hyperdoctrine_z_iso_eqrel H _)
      (φ [ s ])
    =
    (setquotpr (preorder_hyperdoctrine_z_iso_eqrel H _) φ : form (Γ₂ : ty Hc)) [ s ].
Proof.
  exact (disp_functor_weak_equivalence_preserves_lift
           (hyperdoctrine_completion_disp_cat_functor _ _)
           (disp_functor_ff_hyperdoctrine_completion_disp_cat_functor _ _)
           (disp_functor_disp_ess_surj_hyperdoctrine_completion_disp_cat_functor _ _)
           (pr222 (pr221 H))
           (is_univalent_disp_hyperdoctrine_completion_disp_cat _ _)
           (pr122 (pr221 H))
           s
           φ).
Qed.

(** * 6. Preservation *)
Section Preservation.
  Context (H : first_order_preorder_hyperdoctrine).

  Let Hc : first_order_hyperdoctrine
    := first_order_preorder_hyperdoctrine_completion H.
  Let FF : disp_functor
             (functor_identity _)
             (hyperdoctrine_formula_disp_cat H)
             (hyperdoctrine_formula_disp_cat Hc)
    := hyperdoctrine_completion_disp_cat_functor
         (hyperdoctrine_formula_disp_cat H)
         (locally_propositional_preorder_hyperdoctrine H).

  Let H₁ : disp_functor_ff FF
    := disp_functor_ff_hyperdoctrine_completion_disp_cat_functor
         (hyperdoctrine_formula_disp_cat H)
         (locally_propositional_preorder_hyperdoctrine H).
  Let H₂ : disp_functor_disp_ess_surj FF
    := disp_functor_disp_ess_surj_hyperdoctrine_completion_disp_cat_functor
         (hyperdoctrine_formula_disp_cat H)
         (locally_propositional_preorder_hyperdoctrine H).

  Proposition to_completion_proof
              {Γ : ty H}
              {Δ φ : form Γ}
              (p : Δ ⊢ φ)
    : FF Γ Δ ⊢ FF Γ φ.
  Proof.
    exact (♯FF p)%mor_disp.
  Qed.

  Proposition to_completion_subst
              {Γ₁ Γ₂ : ty H}
              (φ : form Γ₂)
              (s : tm Γ₁ Γ₂)
    : FF Γ₁ (φ [ s ]) = (FF Γ₂ φ) [ s ].
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    pose (weak_equivalence_cartesian_disp_functor
            FF
            H₁ H₂
            (locally_propositional_preorder_hyperdoctrine H)
            (hyperdoctrine_cleaving H))
      as Hp.
    exact (cartesian_disp_functor_disp_z_iso Hp _ _ s φ).
  Qed.

  Proposition to_completion_truth
              (Γ : ty H)
    : FF Γ first_order_preorder_hyperdoctrine_truth
      =
      (⊤ : form (Γ : ty Hc)).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    apply (preserves_terminal_to_z_iso
             _
             (preserves_terminal_fiber_functor_weak_equiv FF H₁ H₂ Γ)).
  Qed.

  Proposition to_completion_false
              (Γ : ty H)
    : FF Γ first_order_preorder_hyperdoctrine_false
      =
      (⊥ : form (Γ : ty Hc)).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    apply (preserves_initial_to_z_iso
             _
             (preserves_initial_fiber_functor_weak_equiv FF H₁ H₂ Γ)).
  Qed.

  Proposition to_completion_conj
              {Γ : ty H}
              (φ ψ : form Γ)
    : FF Γ (first_order_preorder_hyperdoctrine_conj φ ψ)
      =
      (FF Γ φ ∧ FF Γ ψ).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    exact (preserves_binproduct_to_z_iso
             _
             (preserves_binproduct_fiber_functor_weak_equiv FF H₁ H₂ Γ)
             _ _).
  Qed.

  Proposition to_completion_disj
              {Γ : ty H}
              (φ ψ : form Γ)
    : FF Γ (first_order_preorder_hyperdoctrine_disj φ ψ)
      =
      (FF Γ φ ∨ FF Γ ψ).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    exact (preserves_bincoproduct_to_z_iso
             _
             (preserves_bincoproduct_fiber_functor_weak_equiv FF H₁ H₂ Γ)
             _ _).
  Qed.

  Proposition to_completion_impl
              {Γ : ty H}
              (φ ψ : form Γ)
    : FF Γ (first_order_preorder_hyperdoctrine_impl φ ψ)
      =
      (FF Γ φ ⇒ FF Γ ψ).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    refine (_ ,, preserves_exponential_fiber_functor_weak_equiv FF H₁ H₂ _ _ _ _ _ _ _).
    apply is_univalent_disp_hyperdoctrine_completion_disp_cat.
  Qed.

  Proposition to_completion_forall
              {Γ A : ty H}
              (φ : form (Γ ×h A))
    : FF Γ (first_order_preorder_hyperdoctrine_forall φ)
      =
      (∀h (FF (Γ ×h A) φ)).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    use z_iso_inv.
    refine (disp_functor_weak_equivalence_preserves_dependent_product
              FF
              H₁ H₂
              _ _ _ _ _
              φ).
    - exact (locally_propositional_preorder_hyperdoctrine H).
    - exact (is_univalent_disp_hyperdoctrine Hc).
  Qed.

  Proposition to_completion_exists
              {Γ A : ty H}
              (φ : form (Γ ×h A))
    : FF Γ (first_order_preorder_hyperdoctrine_exists φ)
      =
      (∃h (FF (Γ ×h A) φ)).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    use z_iso_inv.
    refine (disp_functor_weak_equivalence_preserves_dependent_sum
              FF
              H₁ H₂
              _ _ _ _ _
              φ).
    - exact (locally_propositional_preorder_hyperdoctrine H).
    - exact (is_univalent_disp_hyperdoctrine Hc).
  Qed.

  Proposition to_completion_equal
              {Γ A : ty H}
              (t₁ t₂ : tm Γ A)
    : FF Γ (first_order_preorder_hyperdoctrine_equal t₁ t₂)
      =
      (first_order_hyperdoctrine_equal (H := Hc) t₁ t₂).
  Proof.
    use (isotoid_disp (is_univalent_disp_hyperdoctrine Hc) (idpath _)).
    use z_iso_disp_from_z_iso_fiber.
    unfold first_order_hyperdoctrine_equal.
    unfold first_order_preorder_hyperdoctrine_equal.
    rewrite to_completion_subst.
    use (functor_on_z_iso
           (fiber_functor_from_cleaving
              _
              (hyperdoctrine_cleaving Hc)
              ⟨ t₁ , t₂ ⟩)).
    use z_iso_inv.
    refine (disp_functor_weak_equivalence_preserves_dependent_sum
              FF
              H₁ H₂
              _ _ _ _ _
              _).
    - exact (locally_propositional_preorder_hyperdoctrine H).
    - exact (is_univalent_disp_hyperdoctrine Hc).
  Qed.
End Preservation.

(** * 7. The completion of triposes *)
Section TriposCompletion.
  Context (H : preorder_tripos).

  Let Hc : first_order_hyperdoctrine
    := first_order_preorder_hyperdoctrine_completion H.

  Section Power.
    Context (X : ty H).

    Let Pow : ty H := pr1 (pr2 H X).
    Let InH : form (X ×h Pow) := pr12 (pr2 H X).
    Let In : form ((X ×h Pow) : ty Hc)
      := hyperdoctrine_completion_disp_cat_functor _ _ _ InH.

    Proposition tripos_completion_law
      : is_weak_tripos_law In.
    Proof.
      intros Γ.
      use setquotunivprop'.
      {
        intro.
        apply locally_propositional_hyperdoctrine_completion_disp_cat.
      }
      intro R.
      pose (pr1 (pr22 (pr2 H X) Γ R)) as R'.
      assert (R = InH [ ⟨ π₁ (tm_var _) , R' [ π₂ (tm_var _) ]tm ⟩ ])
        as p.
      {
        exact (pr2 (pr22 (pr2 H X) Γ R)).
      }
      simpl.
      use (forall_intro (H := Hc)).
      use exists_intro.
      {
        exact (R' [ π₂ (tm_var _) ]tm).
      }
      simplify_form.
      use (forall_intro (H := Hc)).
      rewrite p.
      use (iff_from_eq (H := Hc)).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply first_order_preorder_hyperdoctrine_completion_form_subst.
      }
      hypersimplify.
      apply maponpaths.
      refine (hyperdoctrine_pair_subst _ _ _ @ _).
      hypersimplify.
      apply idpath.
    Qed.
  End Power.

  Definition is_weak_tripos_completion
    : is_weak_tripos Hc.
  Proof.
    intro X.
    pose (Pow := pr1 (pr2 H X)).
    pose (In := pr12 (pr2 H X)).
    simple refine (_ ,, _ ,, _).
    - exact Pow.
    - exact (hyperdoctrine_completion_disp_cat_functor _ _ _ In).
    - apply tripos_completion_law.
  Defined.

  Definition tripos_completion
    : weak_tripos.
  Proof.
    use make_weak_tripos.
    - exact Hc.
    - exact is_weak_tripos_completion.
  Defined.
End TriposCompletion.
