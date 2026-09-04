(**********************************************************************************************

 First-order Hyperdoctrines

 Hyperdoctrines provide a framework in which one can interpret the basic judgments of
 first-order predicate logic. However, if one actually wants to study predicate logic, then
 one also needs to have suitable connectives for the formulas, and one also needs to have an
 equality predicate.

 In this file, we define first-order hyperdoctrines. First-order hyperdoctrines are an extension
 of ordinary hyperdoctrines. In a first-order hyperdoctrine, we can interpret all the usual
 connectives from first-order predicate logic and equality. Note that we focus on intuitionistic
 first-order hyperdoctrines, so the law of excluded middle does not hold in them. For each of
 the connectives, we also define accessors, which are similar to the elimination and introduction
 rules in natural deduction.

 Note that the connectives are defined as follows:
 - Truth: fiberwise terminal object
 - Falsity: fiberwise initial object
 - Conjunction: fiberwise binary products
 - Disjunction: fiberwise binary coproducts
 - Implication: fiberwise exponentials
 - Universal quantification: right adjoint to substitution
 - Existential quantification: left adjoint to substitution
 - Equality: left adjoint to the diagonal
 For the propositional connectives, the introduction and elimination rules arise rather directly
 from the definition of limits and colimits, whereas their preservation under substitution
 follow from the fiberwise preservation. For the quantifiers, their preservation under
 substitution follows from the Beck-Chevalley condition, and their introduction and elimination
 rules follow from the unit and counit of the adjunctions.

 Technically there are some interesting points in this file. To derive the elimination rule for
 disjunction, we use distributivity of products and coproducts. This follows from the fact that
 we have exponentials. As such, taking the binary product with a fixed object is a left adjoint,
 and it thus preserves coproducts.

 Another point arises from the existential quantification. The elimination rule for the
 existential quantifier says that `Δ ⊢ ψ` follows from `Δ ⊢ ∃ φ` and `Δ ∧ φ ⊢ ψ`. To derive this
 rule, we need Frobenius reciprocity, which says that `∃ (Δ ∧ φ)` follows from `Δ ∧ ∃ φ`. Without
 this assumption, we would only be able to derive a weaker rule, where we need to show `φ ⊢ ψ`,
 so without the assumptions in `Δ`. To prove Frobenius reciprocity, we use the implication.

 The equality formula also comes with an introduction and elimination rule. From the elimination
 rule, we can derive symmetry and transitivity of equality. The proof is similar to how one uses
 the J-rule to derive symmetry and transitivity of the identity type. We also derive equality
 principles for terms of the unit type and of the product type. To prove the desired J-rule, we
 use that our hyperdoctrines support universal quantification.

 Finally, note that in our definition, we require left and right adjoints to exist for
 substitution along all morphisms rather than just projections. This is stronger than one would
 usually require, and it does eliminate the syntax as a model. However, in many models all
 of the aforementioned adjoints do exist.

 An important use case of first-order hyperdoctrines is using the internal language for reasoning.
 The internal language is implemented via a shallow embedding. However, one challenge that one
 meets when using this shallow embedding directly, is that one must simplify the goal completely
 by hand. More concretely, there might be several substitutions in the statement that one is
 proving, and to simplify it, one must rewrite using the right substitution laws. The same holds
 for normalizing terms: one must simplify every β-redex by using an appropriate rewrite statement.
 In this file, we also give a tactic that automates these processes. Below we comment on the
 design of this tactic and in the file `PERs.v` in the proof of [eq_per_axioms], we explain
 and demonstrate how this tactic is used.

 References
 - "Adjointness in Foundations" by William Lawvere
 - "Categorical logic" by Andrew Pitts in Handbook of logic in computer science, Volume 5
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. First-order hyperdoctrines
 2. The truth formula
 3. The falsity formula
 4. Conjunction
 5. Weakening of hypotheses
 6. Disjunction
 7. Implication
 8. Universal quantification
 9. Existential quantification
 10. Equality
 11. Derived rules for equality
 12. Derived connectives
 12.1. Bi-implication
 13. A tactic for simplifying goals in the internal language of first-order hyperdoctrines

 **********************************************************************************************)
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
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.Tactics.Simplify.
Require Import UniMath.Tactics.Utilities.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Notations.

Local Open Scope cat.
Local Open Scope hd.

Set Default Proof Mode "Classic".

(** * 1. First-order hyperdoctrines *)
Definition existential_quantifiers
           (H : preorder_hyperdoctrine)
  : UU
  := ∑ (sig : ∏ (Γ A : ty H), dependent_sum (hyperdoctrine_cleaving H) (π₁ (tm_var _))),
     ∏ (Γ₁ Γ₂ A₁ A₂ : ty H)
       (s₁ : Γ₁ --> Γ₂)
       (s₂ : (Γ₁ ×h A₁) --> (Γ₂ ×h A₂))
       (p : s₂ · _ = _ · s₁)
       (Hp : isPullback p),
     left_beck_chevalley
       _
       _ s₁ _ s₂
       p
       (sig _ A₂)
       (sig _ A₁).

Section MakeExistentialQuantifiers.
  Context {H : preorder_hyperdoctrine}
          (ex : ∏ (Γ A : ty H), form (Γ ×h A) → form Γ)
          (ex_i : ∏ (Γ A : ty H)
                    (φ : form (Γ ×h A)),
                  φ ⊢ (ex _ _ φ) [ π₁ (tm_var _) ])
          (ex_e : ∏ (Γ A : ty H)
                    (ψ : form (Γ ×h A))
                    (χ : form Γ)
                    (p : ψ ⊢ χ [ π₁ (tm_var _) ]),
                  ex Γ A ψ ⊢ χ)
          (ex_sub : ∏ (Γ₁ Γ₂ A₁ A₂ : ty H)
                      (s₁ : Γ₁ --> Γ₂)
                      (s₂ : (Γ₁ ×h A₁) --> (Γ₂ ×h A₂))
                      (p : s₂ · π₁ (tm_var (Γ₂ ×h A₂)) = π₁ (tm_var (Γ₁ ×h A₁)) · s₁)
                      (Hp : isPullback p)
                      (φ : form (Γ₂ ×h A₂)),
                    (ex _ _ φ) [ s₁ ] ⊢ ex _ _ (φ [ s₂ ])).

  Definition make_existential_quantifiers_sum
             (Γ A : ty H)
    : dependent_sum (hyperdoctrine_cleaving H) (π₁ (tm_var (Γ ×h A))).
  Proof.
    apply reflections_to_is_right_adjoint.
    intro x.
    use make_reflection'.
    - exact (ex _ _ x).
    - exact (ex_i _ _ x).
    - intros p.
      use make_reflection_arrow.
      + apply ex_e.
        exact (p : _ --> _).
      + abstract apply locally_propositional_preorder_hyperdoctrine.
      + intros.
        abstract apply locally_propositional_preorder_hyperdoctrine.
  Defined.

  Definition make_existential_quantifiers
    : existential_quantifiers H.
  Proof.
    simple refine (_ ,, _).
    - exact make_existential_quantifiers_sum.
    - abstract
        (intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ ;
        simple refine (_ ,, _ ,, _) ;
        [
        | apply locally_propositional_preorder_hyperdoctrine
        | apply locally_propositional_preorder_hyperdoctrine ] ;
         exact (ex_sub _ _ _ _ _ _ _ Hp φ)).
  Defined.
End MakeExistentialQuantifiers.

Definition equality_formulas
           (H : preorder_hyperdoctrine)
  : UU
  := ∏ (A : ty H), dependent_sum (hyperdoctrine_cleaving H) (Δ_{A}).

Section MakeEqualityFormulas.
  Context {H : preorder_hyperdoctrine}
          (eq : ∏ (A : ty H), form A → form (A ×h A))
          (eq_i : ∏ (A : ty H)
                    (φ : form A),
                  φ ⊢ (eq _ φ) [ Δ_{A} ])
          (eq_e : ∏ (A : ty H)
                    (ψ : form A)
                    (χ : form (A ×h A))
                    (p : ψ ⊢ χ [ Δ_{A} ]),
                  eq A ψ ⊢ χ).

  Definition make_equality_formulas
    : equality_formulas H.
  Proof.
    intros A.
    apply reflections_to_is_right_adjoint.
    intro x.
    use make_reflection'.
    - exact (eq _ x).
    - exact (eq_i _ x).
    - intros p.
      use make_reflection_arrow.
      + apply eq_e.
        exact (p : _ --> _).
      + abstract apply locally_propositional_preorder_hyperdoctrine.
      + intros.
        abstract apply locally_propositional_preorder_hyperdoctrine.
  Defined.
End MakeEqualityFormulas.

Definition universal_quantifiers
           (H : preorder_hyperdoctrine)
  : UU
  := ∑ (all : ∏ (Γ A : ty H), dependent_product (hyperdoctrine_cleaving H) (π₁ (tm_var _))),
     ∏ (Γ₁ Γ₂ A₁ A₂ : ty H)
       (s₁ : Γ₁ --> Γ₂)
       (s₂ : (Γ₁ ×h A₁) --> (Γ₂ ×h A₂))
       (p : s₂ · _ = _ · s₁)
       (Hp : isPullback p),
     right_beck_chevalley
       _
       _ s₁ _ s₂
       p
       (all _ A₂)
       (all _ A₁).

Section MakeUniversalQuantifiers.
  Context {H : preorder_hyperdoctrine}
          (all : ∏ (Γ A : ty H), form (Γ ×h A) → form Γ)
          (all_e : ∏ (Γ A : ty H)
                     (φ : form (Γ ×h A)),
                   (all _ _ φ) [ π₁ (tm_var _) ] ⊢ φ)
          (all_i : ∏ (Γ A : ty H)
                     (ψ : form (Γ ×h A))
                     (χ : form Γ)
                     (p : χ [ π₁ (tm_var _) ] ⊢ ψ),
                   χ ⊢ all Γ A ψ)
          (all_sub : ∏ (Γ₁ Γ₂ A₁ A₂ : ty H)
                       (s₁ : Γ₁ --> Γ₂)
                       (s₂ : (Γ₁ ×h A₁) --> (Γ₂ ×h A₂))
                       (p : s₂ · π₁ (tm_var (Γ₂ ×h A₂))
                            =
                            π₁ (tm_var (Γ₁ ×h A₁)) · s₁)
                       (Hp : isPullback p)
                       (φ : form (Γ₂ ×h A₂)),
                     all _ _ (φ [ s₂ ]) ⊢ (all _ _ φ) [ s₁ ]).

  Definition make_universal_quantifiers_prod
             (Γ A : ty H)
    : dependent_product (hyperdoctrine_cleaving H) (π₁ (tm_var (Γ ×h A))).
  Proof.
    apply coreflections_to_is_left_adjoint.
    intro ψ.
    use make_coreflection'.
    - exact (all _ _ ψ).
    - exact (all_e _ _ ψ).
    - intro p.
      use make_coreflection_arrow.
      + apply all_i.
        exact (p : _ --> _).
      + abstract apply locally_propositional_preorder_hyperdoctrine.
      + abstract (
          intros;
          apply locally_propositional_preorder_hyperdoctrine).
  Defined.

  Definition make_universal_quantifiers
    : universal_quantifiers H.
  Proof.
    simple refine (_ ,, _).
    - exact make_universal_quantifiers_prod.
    - abstract
        (intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ ;
        simple refine (_ ,, _ ,, _) ;
        [
        | apply locally_propositional_preorder_hyperdoctrine
        | apply locally_propositional_preorder_hyperdoctrine ] ;
         exact (all_sub _ _ _ _ _ _ _ Hp φ)).
  Defined.
End MakeUniversalQuantifiers.

Definition first_order_preorder_hyperdoctrine
  : UU
  := ∑ (H : preorder_hyperdoctrine),
     fiberwise_terminal (hyperdoctrine_cleaving H)
     ×
     fiberwise_initial (hyperdoctrine_cleaving H)
     ×
     ∑ (P : fiberwise_binproducts (hyperdoctrine_cleaving H)),
     fiberwise_bincoproducts (hyperdoctrine_cleaving H)
     ×
     fiberwise_exponentials P
     ×
     universal_quantifiers H
     ×
     existential_quantifiers H
     ×
     equality_formulas H.

Coercion first_order_preorder_hyperdoctrine_to_preorder_hyperdoctrine
         (H : first_order_preorder_hyperdoctrine)
  : preorder_hyperdoctrine.
Proof.
  exact (pr1 H).
Defined.

Definition first_order_hyperdoctrine
  : UU
  := ∑ (H : hyperdoctrine),
     fiberwise_terminal (hyperdoctrine_cleaving H)
     ×
     fiberwise_initial (hyperdoctrine_cleaving H)
     ×
     ∑ (P : fiberwise_binproducts (hyperdoctrine_cleaving H)),
     fiberwise_bincoproducts (hyperdoctrine_cleaving H)
     ×
     fiberwise_exponentials P
     ×
     universal_quantifiers H
     ×
     existential_quantifiers H
     ×
     equality_formulas H.

Coercion first_order_hyperdoctrine_to_hyperdoctrine
         (H : first_order_hyperdoctrine)
  : hyperdoctrine.
Proof.
  exact (pr1 H).
Defined.

Coercion first_order_hyperdoctrine_to_preorder_hyperdoctrine
         (H : first_order_hyperdoctrine)
  : first_order_preorder_hyperdoctrine.
Proof.
  refine (_
         ,,
         pr12 H
         ,,
         pr122 H
         ,,
         pr1 (pr222 H)
         ,,
         pr12 (pr222 H)
         ,,
         pr122 (pr222 H)
         ,,
         pr1 (pr222 (pr222 H))
         ,,
         pr12 (pr222 (pr222 H))
         ,,
         pr22 (pr222 (pr222 H))).
Defined.

Definition univalent_first_order_hyperdoctrine
  : UU
  := ∑ (H : univalent_hyperdoctrine),
     fiberwise_terminal (hyperdoctrine_cleaving H)
     ×
     fiberwise_initial (hyperdoctrine_cleaving H)
     ×
     ∑ (P : fiberwise_binproducts (hyperdoctrine_cleaving H)),
     fiberwise_bincoproducts (hyperdoctrine_cleaving H)
     ×
     fiberwise_exponentials P
     ×
     universal_quantifiers H
     ×
     existential_quantifiers H
     ×
     equality_formulas H.

Coercion univalent_first_order_hyperdoctrine_to_hyperdoctrine
         (H : univalent_first_order_hyperdoctrine)
  : univalent_hyperdoctrine.
Proof.
  exact (pr1 H).
Defined.

Coercion univalent_first_order_hyperdoctrine_to_first_order
         (H : univalent_first_order_hyperdoctrine)
  : first_order_hyperdoctrine.
Proof.
  exact (_
         ,,
         pr12 H
         ,,
         pr122 H
         ,,
         pr1 (pr222 H)
         ,,
         pr12 (pr222 H)
         ,,
         pr122 (pr222 H)
         ,,
         pr1 (pr222 (pr222 H))
         ,,
         pr12 (pr222 (pr222 H))
         ,,
         pr22 (pr222 (pr222 H))).
Defined.

Definition make_first_order_preorder_hyperdoctrine
           (H : preorder_hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : universal_quantifiers H)
           (DSH : existential_quantifiers H)
           (EQH : equality_formulas H)
  : first_order_preorder_hyperdoctrine
  := H
     ,,
     TH
     ,,
     IH
     ,,
     PH
     ,,
     CH
     ,,
     IMPH
     ,,
     DPH
     ,,
     DSH
     ,,
     EQH.

Definition make_first_order_preorder_hyperdoctrine_all
           (H : preorder_hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : has_dependent_products (hyperdoctrine_cleaving H))
           (DSH : has_dependent_sums (hyperdoctrine_cleaving H))
  : first_order_preorder_hyperdoctrine.
Proof.
  use make_first_order_preorder_hyperdoctrine.
  - exact H.
  - exact TH.
  - exact IH.
  - exact PH.
  - exact CH.
  - exact IMPH.
  - simple refine (_ ,, _).
    + intros.
      apply DPH.
    + intro ; intros.
      apply DPH.
      assumption.
  - simple refine (_ ,, _).
    + intros.
      apply DSH.
    + intro ; intros.
      apply DSH.
      assumption.
  - intro.
    apply DSH.
Defined.

Definition make_first_order_hyperdoctrine
           (H : hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : universal_quantifiers H)
           (DSH : existential_quantifiers H)
           (EQH : equality_formulas H)
  : first_order_hyperdoctrine
  := H
     ,,
     TH
     ,,
     IH
     ,,
     PH
     ,,
     CH
     ,,
     IMPH
     ,,
     DPH
     ,,
     DSH
     ,,
     EQH.

Definition make_first_order_hyperdoctrine_all
           (H : hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : has_dependent_products (hyperdoctrine_cleaving H))
           (DSH : has_dependent_sums (hyperdoctrine_cleaving H))
  : first_order_hyperdoctrine.
Proof.
  use make_first_order_hyperdoctrine.
  - exact H.
  - exact TH.
  - exact IH.
  - exact PH.
  - exact CH.
  - exact IMPH.
  - simple refine (_ ,, _).
    + intros.
      apply DPH.
    + intro ; intros.
      apply DPH.
      assumption.
  - simple refine (_ ,, _).
    + intros.
      apply DSH.
    + intro ; intros.
      apply DSH.
      assumption.
  - intro.
    apply DSH.
Defined.

Definition make_univalent_first_order_hyperdoctrine
           (H : univalent_hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : universal_quantifiers H)
           (DSH : existential_quantifiers H)
           (EQH : equality_formulas H)
  : univalent_first_order_hyperdoctrine
  := H
     ,,
     TH
     ,,
     IH
     ,,
     PH
     ,,
     CH
     ,,
     IMPH
     ,,
     DPH
     ,,
     DSH
     ,,
     EQH.

Definition make_univalent_first_order_hyperdoctrine_all
           (H : univalent_hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : has_dependent_products (hyperdoctrine_cleaving H))
           (DSH : has_dependent_sums (hyperdoctrine_cleaving H))
  : univalent_first_order_hyperdoctrine.
Proof.
  use make_univalent_first_order_hyperdoctrine.
  - exact H.
  - exact TH.
  - exact IH.
  - exact PH.
  - exact CH.
  - exact IMPH.
  - simple refine (_ ,, _).
    + intros.
      apply DPH.
    + intro ; intros.
      apply DPH.
      assumption.
  - simple refine (_ ,, _).
    + intros.
      apply DSH.
    + intro ; intros.
      apply DSH.
      assumption.
  - intro.
    apply DSH.
Defined.

(** * 2. The truth formula *)
Definition first_order_hyperdoctrine_truth
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
  : form Γ
  := terminal_obj_in_fib (pr12 H) Γ.

Notation "'⊤'" := first_order_hyperdoctrine_truth : hyperdoctrine.

Proposition truth_intro
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (Δ : form Γ)
  : Δ ⊢ ⊤.
Proof.
  exact (TerminalArrow (terminal_in_fib (pr12 H) Γ) Δ).
Qed.

Proposition truth_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (s : tm Γ₁ Γ₂)
  : ⊤ [ s ] = ⊤.
Proof.
  use (isotoid_disp _ (idpath _)).
  - apply is_univalent_disp_hyperdoctrine.
  - use z_iso_disp_from_z_iso_fiber.
    apply (preserves_terminal_to_z_iso _ (pr212 H _ _ s) _ _).
Qed.

(** * 3. The falsity formula *)
Definition first_order_hyperdoctrine_false
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
  : form Γ
  := initial_obj_in_fib (pr122 H) Γ.

Notation "'⊥'" := first_order_hyperdoctrine_false : hyperdoctrine.

Proposition false_elim
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (Δ φ : form Γ)
            (p : Δ ⊢ ⊥)
  : Δ ⊢ φ.
Proof.
  use (hyperdoctrine_cut p).
  exact (InitialArrow (initial_in_fib (pr122 H) Γ) φ).
Qed.

Proposition false_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (s : Γ₁ --> Γ₂)
  : ⊥ [ s ] = ⊥.
Proof.
  use (isotoid_disp _ (idpath _)).
  - apply is_univalent_disp_hyperdoctrine.
  - use z_iso_disp_from_z_iso_fiber.
    apply (preserves_initial_to_z_iso _ (pr2 (pr122 H) _ _ s) _ _).
Qed.

(** * 4. Conjunction *)
Definition first_order_hyperdoctrine_conj
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
           (φ ψ : form Γ)
  : form Γ
  := BinProductObject _ (binprod_in_fib (pr1 (pr222 H)) φ ψ).

Notation "φ ∧ ψ" := (first_order_hyperdoctrine_conj φ ψ) : hyperdoctrine.

Proposition conj_intro
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ)
            (q : Δ ⊢ ψ)
  : Δ ⊢ φ ∧ ψ.
Proof.
  exact (BinProductArrow _ (binprod_in_fib (pr1 (pr222 H)) φ ψ) p q).
Qed.

Proposition conj_elim_left
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ ∧ ψ)
  : Δ ⊢ φ.
Proof.
  use (hyperdoctrine_cut p).
  apply (BinProductPr1 _ (binprod_in_fib (pr1 (pr222 H)) φ ψ)).
Qed.

Proposition conj_elim_right
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ ∧ ψ)
  : Δ ⊢ ψ.
Proof.
  use (hyperdoctrine_cut p).
  apply (BinProductPr2 _ (binprod_in_fib (pr1 (pr222 H)) φ ψ)).
Qed.

Proposition conj_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (s : Γ₁ --> Γ₂)
            (φ ψ : form Γ₂)
  : (φ ∧ ψ) [ s ] = (φ [ s ] ∧ ψ [ s ]).
Proof.
  use (isotoid_disp _ (idpath _)).
  - apply is_univalent_disp_hyperdoctrine.
  - use z_iso_disp_from_z_iso_fiber.
    use (preserves_binproduct_to_z_iso _ (pr21 (pr222 H) _ _ s)).
Qed.

(** * 5. Weakening of hypotheses *)

(**
   The presence of conjunction allows us to add assumptions to the formula context.
   We can derive the proper weaking rules for that.
 *)
Proposition weaken_left
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ₁ φ : form Γ}
            (p : Δ₁ ⊢ φ)
            (Δ₂ : form Γ)
  : Δ₁ ∧ Δ₂ ⊢ φ.
Proof.
  use (hyperdoctrine_cut _ p).
  apply (BinProductPr1 _ (binprod_in_fib (pr1 (pr222 H)) Δ₁ Δ₂)).
Qed.

Proposition weaken_right
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ₂ φ : form Γ}
            (p : Δ₂ ⊢ φ)
            (Δ₁ : form Γ)
  : Δ₁ ∧ Δ₂ ⊢ φ.
Proof.
  use (hyperdoctrine_cut _ p).
  apply (BinProductPr2 _ (binprod_in_fib (pr1 (pr222 H)) Δ₁ Δ₂)).
Qed.

Proposition weaken_cut
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ)
            (q : Δ ∧ φ ⊢ ψ)
  : Δ ⊢ ψ.
Proof.
  refine (hyperdoctrine_cut _ q).
  use (BinProductArrow _ (binprod_in_fib _ Δ φ)).
  - apply hyperdoctrine_hyp.
  - exact p.
Qed.

Proposition weaken_to_empty
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ : form Γ}
            (p : ⊤ ⊢ φ)
  : Δ ⊢ φ.
Proof.
  refine (hyperdoctrine_cut _ p).
  use truth_intro.
Qed.

Proposition hyp_sym
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ Δ' φ : form Γ}
            (p : Δ ∧ Δ' ⊢ φ)
  : Δ' ∧ Δ ⊢ φ.
Proof.
  refine (hyperdoctrine_cut _ p).
  use conj_intro.
  - use weaken_right.
    apply hyperdoctrine_hyp.
  - use weaken_left.
    apply hyperdoctrine_hyp.
Qed.

Proposition hyp_ltrans
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ Δ' Δ'' φ : form Γ}
            (p : Δ ∧ (Δ' ∧ Δ'') ⊢ φ)
  : (Δ ∧ Δ') ∧ Δ'' ⊢ φ.
Proof.
  refine (hyperdoctrine_cut _ p).
  use conj_intro.
  - do 2 use weaken_left.
    apply hyperdoctrine_hyp.
  - use conj_intro.
    + use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      apply hyperdoctrine_hyp.
Qed.

Proposition hyp_rtrans
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ Δ' Δ'' φ : form Γ}
            (p : (Δ ∧ Δ') ∧ Δ'' ⊢ φ)
  : Δ ∧ (Δ' ∧ Δ'') ⊢ φ.
Proof.
  refine (hyperdoctrine_cut _ p).
  use conj_intro.
  - use conj_intro.
    + use weaken_left.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      use weaken_left.
      apply hyperdoctrine_hyp.
  - do 2 use weaken_right.
    apply hyperdoctrine_hyp.
Qed.

Proposition conj_assoc
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (φ₁ φ₂ φ₃ : form Γ)
  : ((φ₁ ∧ φ₂) ∧ φ₃) = (φ₁ ∧ (φ₂ ∧ φ₃)).
Proof.
  use hyperdoctrine_formula_eq.
  - apply hyp_ltrans.
    apply hyperdoctrine_hyp.
  - apply hyp_rtrans.
    apply hyperdoctrine_hyp.
Qed.

(** * 6. Disjunction *)
Definition first_order_hyperdoctrine_disj
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
           (φ ψ : form Γ)
  : form Γ
  := BinCoproductObject (bincoprod_in_fib (pr12 (pr222 H)) φ ψ).

Notation "φ ∨ ψ" := (first_order_hyperdoctrine_disj φ ψ) : hyperdoctrine.

Proposition disj_intro_left
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ)
  : Δ ⊢ φ ∨ ψ.
Proof.
  use (hyperdoctrine_cut p).
  apply (BinCoproductIn1 (bincoprod_in_fib (pr12 (pr222 H)) φ ψ)).
Qed.

Proposition disj_intro_right
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ ψ)
  : Δ ⊢ φ ∨ ψ.
Proof.
  use (hyperdoctrine_cut p).
  apply (BinCoproductIn2 (bincoprod_in_fib (pr12 (pr222 H)) φ ψ)).
Qed.

Proposition distributivity
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (φ ψ χ : form Γ)
  : φ ∧ (ψ ∨ χ) ⊢ (φ ∧ ψ) ∨ (φ ∧ χ).
Proof.
  exact (pr1 (distributivity_fiberwise_exponentials
                (pr12 (pr222 H))
                (pr122 (pr222 H))
                φ ψ χ)).
Defined.

Proposition disj_elim
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ χ : form Γ}
            (p : Δ ⊢ φ ∨ ψ)
            (q : Δ ∧ φ ⊢ χ)
            (r : Δ ∧ ψ ⊢ χ)
  : Δ ⊢ χ.
Proof.
  refine (hyperdoctrine_cut
            _
            (BinCoproductArrow (bincoprod_in_fib (pr12 (pr222 H)) (Δ ∧ φ) (Δ ∧ ψ)) q r)).
  use (weaken_cut p).
  apply distributivity.
Qed.

Proposition disj_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (s : Γ₁ --> Γ₂)
            (φ ψ : form Γ₂)
  : (φ ∨ ψ) [ s ] = (φ [ s ] ∨ ψ [ s ]).
Proof.
  use (isotoid_disp _ (idpath _)).
  - apply is_univalent_disp_hyperdoctrine.
  - use z_iso_disp_from_z_iso_fiber.
    use (preserves_bincoproduct_to_z_iso _ (pr212 (pr222 H) _ _ s)).
Qed.

(** * 7. Implication *)
Definition first_order_hyperdoctrine_impl
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
           (φ ψ : form Γ)
  : form Γ
  := exp_in_fib (pr122 (pr222 H)) φ ψ.

Notation "φ ⇒ ψ" := (first_order_hyperdoctrine_impl φ ψ) : hyperdoctrine.

Proposition impl_intro
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ∧ φ ⊢ ψ)
  : Δ ⊢ φ ⇒ ψ.
Proof.
  refine (lam_in_fib (pr122 (pr222 H)) _).
  use (hyperdoctrine_cut _ p).
  apply hyp_sym.
  apply hyperdoctrine_hyp.
Qed.

Proposition impl_elim
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ)
            (q : Δ ⊢ φ ⇒ ψ)
  : Δ ⊢ ψ.
Proof.
  use (hyperdoctrine_cut _ (eval_in_fib (pr122 (pr222 H)) φ ψ)).
  use conj_intro.
  - exact p.
  - exact q.
Qed.

Proposition impl_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (s : Γ₁ --> Γ₂)
            (φ ψ : form Γ₂)
  : (φ ⇒ ψ) [ s ] = (φ [ s ] ⇒ ψ [ s ]).
Proof.
  use (isotoid_disp _ (idpath _)).
  - apply is_univalent_disp_hyperdoctrine.
  - use z_iso_disp_from_z_iso_fiber.
    exact (_ ,, preserves_exponentials_in_fib (pr122 (pr222 H)) s φ ψ).
Qed.

Proposition impl_id
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (φ : form Γ)
  : ⊤ ⊢ φ ⇒ φ.
Proof.
  use impl_intro.
  use weaken_right.
  apply hyperdoctrine_hyp.
Qed.

(** * 8. Universal quantification *)
Definition first_order_hyperdoctrine_forall
           {H : first_order_hyperdoctrine}
           {Γ A : ty H}
           (φ : form (Γ ×h A))
  : form Γ
  := right_adjoint (pr11 (pr222 (pr222 H)) Γ A) φ.

Notation "'∀h' φ" := (first_order_hyperdoctrine_forall φ) (at level 10)
    : hyperdoctrine.

Proposition forall_intro
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {φ : form (Γ ×h A)}
            (p : Δ [ π₁ (tm_var _) ] ⊢ φ)
  : Δ ⊢ ∀h φ.
Proof.
  use (hyperdoctrine_cut
         (unit_from_left_adjoint ((pr11 (pr222 (pr222 H))) Γ A) Δ)).
  use (#(right_adjoint ((pr11 (pr222 (pr222 H))) Γ A))).
  exact p.
Qed.

Proposition forall_elim
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {φ : form (Γ ×h A)}
            (p : Δ ⊢ ∀h φ)
            (t : tm Γ A)
  : Δ ⊢ φ [ ⟨ tm_var _ , t ⟩ ].
Proof.
  use (hyperdoctrine_cut p).
  assert ((∀h φ)[ π₁ (tm_var (Γ ×h A)) ] ⊢ φ) as r.
  {
    exact (counit_from_left_adjoint ((pr11 (pr222 (pr222 H))) Γ A) φ).
  }
  pose (hyperdoctrine_proof_subst ⟨ tm_var Γ , t ⟩ r) as r'.
  rewrite hyperdoctrine_comp_subst in r'.
  rewrite hyperdoctrine_pair_comp_pr1 in r'.
  rewrite hyperdoctrine_id_subst in r'.
  exact r'.
Qed.

Proposition quantifier_subst_pb_eq
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (A : ty H)
            (s : tm Γ₁ Γ₂)
  : s [ π₁ (tm_var (Γ₁ ×h A)) ]tm
    =
    (π₁ (tm_var _)) [ ⟨ s [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]tm.
Proof.
  rewrite hyperdoctrine_pair_comp_pr1.
  apply idpath.
Qed.

Definition quantifier_subst_pb
           {H : first_order_hyperdoctrine}
           {Γ₁ Γ₂ : ty H}
           (A : ty H)
           (s : tm Γ₁ Γ₂)
  : isPullback (!(quantifier_subst_pb_eq A s)).
Proof.
  intros Γ' t t' p.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros ζ₁ ζ₂ ;
       use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
       refine (hyperdoctrine_pair_eta _ @ _ @ !(hyperdoctrine_pair_eta _)) ;
       pose (pr22 ζ₁) as q ;
       rewrite hyperdoctrine_pr1_comp in q ;
       rewrite id_right in q ;
       rewrite q ; clear q ;
       pose (pr22 ζ₂) as q ;
       rewrite hyperdoctrine_pr1_comp in q ;
       rewrite id_right in q ;
       rewrite q ; clear q ;
       apply maponpaths ;
       pose (maponpaths (λ z, π₂ z) (pr12 ζ₁)) as q ; cbn in q ;
       rewrite (hyperdoctrine_pair_comp (H := H)) in q ;
       unfold tm_subst in q ;
       rewrite !assoc in q ;
       rewrite (hyperdoctrine_pr1_comp (H := H)) in q ;
       rewrite hyperdoctrine_pr2_comp in q ;
       rewrite !id_right in q ;
       rewrite hyperdoctrine_pair_pr2 in q ;
       rewrite q ;
       clear q ;
       pose (maponpaths (λ z, π₂ z) (pr12 ζ₂)) as q ; cbn in q ;
       rewrite (hyperdoctrine_pair_comp (H := H)) in q ;
       unfold tm_subst in q ;
       rewrite !assoc in q ;
       rewrite (hyperdoctrine_pr1_comp (H := H)) in q ;
       rewrite hyperdoctrine_pr2_comp in q ;
       rewrite !id_right in q ;
       rewrite hyperdoctrine_pair_pr2 in q ;
       rewrite q ;
       clear q ;
       apply idpath).
  - refine (⟨ t' , t · π₂ (tm_var _) ⟩ ,, _ ,, _).
    + abstract
        (rewrite hyperdoctrine_pair_comp ;
         unfold tm_subst ;
         rewrite !assoc ;
         rewrite hyperdoctrine_pair_comp_pr1' ;
         rewrite hyperdoctrine_pair_comp_pr2' ;
         rewrite <- p ;
         rewrite hyperdoctrine_pr1_comp ;
         rewrite hyperdoctrine_pr2_comp ;
         rewrite !id_right ;
         rewrite <- hyperdoctrine_pair_eta ;
         apply idpath).
    + abstract
        (rewrite hyperdoctrine_pair_comp_pr1' ;
         apply idpath).
Defined.

Proposition forall_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : ty H}
            (s : tm Γ₁ Γ₂)
            (φ : form (Γ₂ ×h A))
  : (∀h φ) [ s ]
    =
    (∀h (φ [ ⟨ s [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ])).
Proof.
  pose (pr21 (pr222 (pr222 H)) _ _ _ _ _ _ _ (quantifier_subst_pb A s) φ) as p.
  pose (f := (_ ,, p) : z_iso _ _).
  use hyperdoctrine_formula_eq.
  - apply f.
  - exact (inv_from_z_iso f).
Qed.

(** * 9. Existential quantification *)
Definition first_order_hyperdoctrine_exists
           {H : first_order_hyperdoctrine}
           {Γ A : ty H}
           (φ : form (Γ ×h A))
  : form Γ
  := left_adjoint (pr112 (pr222 (pr222 H)) Γ A) φ.

Notation "'∃h' φ" := (first_order_hyperdoctrine_exists φ) (at level 10)
    : hyperdoctrine.

Proposition exists_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : ty H}
            (s : tm Γ₁ Γ₂)
            (φ : form (Γ₂ ×h A))
  : (∃h φ) [ s ]
    =
    ∃h (φ [ ⟨ s [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]).
Proof.
  pose (pr212 (pr222 (pr222 H)) _ _ _ _ _ _ _ (quantifier_subst_pb A s) φ) as p.
  pose (f := (_ ,, p) : z_iso _ _).
  use hyperdoctrine_formula_eq.
  - exact (inv_from_z_iso f).
  - apply f.
Qed.

Proposition exists_intro
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {φ : form (Γ ×h A)}
            {t : tm Γ A}
            (p : Δ ⊢ φ [ ⟨ tm_var _ , t ⟩ ])
  : Δ ⊢ ∃h φ.
Proof.
  use (hyperdoctrine_cut p).
  assert (φ ⊢ (∃h φ) [ π₁ (tm_var (Γ ×h A)) ]) as r.
  {
    exact (unit_from_right_adjoint ((pr112 (pr222 (pr222 H))) Γ A) φ).
  }
  pose (hyperdoctrine_proof_subst ⟨ tm_var Γ , t ⟩ r) as r'.
  rewrite hyperdoctrine_comp_subst in r'.
  rewrite hyperdoctrine_pair_comp_pr1 in r'.
  rewrite hyperdoctrine_id_subst in r'.
  exact r'.
Qed.

Proposition exists_elim_empty
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ ψ : form Γ}
            {φ : form (Γ ×h A)}
            (p : Δ ⊢ ∃h φ)
            (q : φ ⊢ ψ [ π₁ (tm_var (Γ ×h A)) ])
  : Δ ⊢ ψ.
Proof.
  assert (∃h (ψ [ π₁ (tm_var (Γ ×h A)) ]) ⊢ ψ) as r.
  {
    exact (counit_from_right_adjoint ((pr112 (pr222 (pr222 H))) Γ A) ψ).
  }
  use (hyperdoctrine_cut _ r).
  use (hyperdoctrine_cut p).
  use (#(left_adjoint ((pr112 (pr222 (pr222 H))) Γ A))).
  exact q.
Qed.

Proposition frobenius_reciprocity
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (φ : form (Γ ×h A))
            (Δ : form Γ)
  : Δ ∧ (∃h φ) ⊢ (∃h (Δ [ π₁ (tm_var (Γ ×h A)) ] ∧ φ)).
Proof.
  enough (∃h φ ⊢ Δ ⇒ ∃h (Δ [ π₁ (tm_var (Γ ×h A)) ] ∧ φ)) as r₁.
  {
    assert (Δ ∧ ∃h φ ⊢ Δ ⇒ ∃h (Δ [ π₁ (tm_var (Γ ×h A)) ] ∧ φ)) as r₂.
    {
      use weaken_right.
      exact r₁.
    }
    refine (impl_elim _ r₂).
    use weaken_left.
    apply hyperdoctrine_hyp.
  }
  use (exists_elim_empty (hyperdoctrine_hyp _)).
  rewrite impl_subst.
  use impl_intro.
  rewrite exists_subst.
  use exists_intro.
  - exact (π₂ (tm_var _)).
  - rewrite hyperdoctrine_comp_subst.
    rewrite hyperdoctrine_pair_subst.
    rewrite tm_subst_comp.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite tm_subst_var.
    rewrite conj_subst.
    rewrite hyperdoctrine_comp_subst.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite <- hyperdoctrine_pair_eta.
    rewrite hyperdoctrine_id_subst.
    use hyp_sym.
    apply hyperdoctrine_hyp.
Qed.

Proposition exists_elim
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ ψ : form Γ}
            {φ : form (Γ ×h A)}
            (p : Δ ⊢ ∃h φ)
            (q : Δ [ π₁ (tm_var (Γ ×h A)) ] ∧ φ ⊢ ψ [ π₁ (tm_var (Γ ×h A)) ])
  : Δ ⊢ ψ.
Proof.
  assert (∃h (ψ [ π₁ (tm_var (Γ ×h A)) ]) ⊢ ψ) as r.
  {
    exact (counit_from_right_adjoint ((pr112 (pr222 (pr222 H))) Γ A) ψ).
  }
  use (hyperdoctrine_cut _ r).
  use (weaken_cut p).
  use (hyperdoctrine_cut (frobenius_reciprocity _ _)).
  use (#(left_adjoint ((pr112 (pr222 (pr222 H))) Γ A))).
  exact q.
Qed.

(** * 10. Equality *)
Definition first_order_hyperdoctrine_equal
           {H : first_order_hyperdoctrine}
           {Γ A : ty H}
           (t₁ t₂ : tm Γ A)
  : form Γ
  := (left_adjoint (pr22 (pr222 (pr222 H)) A) ⊤) [ ⟨ t₁ , t₂ ⟩ ].

Notation "t₁ ≡ t₂" := (first_order_hyperdoctrine_equal t₁ t₂)
    : hyperdoctrine.

Proposition equal_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : ty H}
            (s : Γ₁ --> Γ₂)
            (t₁ t₂ : tm Γ₂ A)
  : (t₁ ≡ t₂) [ s ] = (t₁ [ s ]tm ≡ t₂ [ s ]tm).
Proof.
  unfold first_order_hyperdoctrine_equal.
  rewrite hyperdoctrine_comp_subst.
  apply maponpaths.
  apply hyperdoctrine_pair_subst.
Qed.

Proposition hyperdoctrine_refl'
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (t : tm Γ A)
  : ⊤ ⊢ t ≡ t.
Proof.
  assert (⊤ ⊢ (left_adjoint (pr22 (pr222 (pr222 H)) A) ⊤) [ Δ_{A} ]) as p.
  {
    exact (unit_from_right_adjoint (pr22 (pr222 (pr222 H)) A) ⊤).
  }
  pose (hyperdoctrine_proof_subst t p) as q.
  rewrite truth_subst in q.
  rewrite hyperdoctrine_comp_subst in q.
  rewrite hyperdoctrine_diag_subst in q.
  exact q.
Qed.

Proposition hyperdoctrine_refl
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (Δ : form Γ)
            (t : tm Γ A)
  : Δ ⊢ t ≡ t.
Proof.
  use weaken_to_empty.
  use hyperdoctrine_refl'.
Qed.

Proposition hyperdoctrine_refl_eq
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (Δ : form Γ)
            {t₁ t₂ : tm Γ A}
            (p : t₁ = t₂)
  : Δ ⊢ t₁ ≡ t₂.
Proof.
  induction p.
  apply hyperdoctrine_refl.
Qed.

Proposition hyperdoctrine_eq_elim_help
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (φ : form (A ×h A))
            (p : ⊤ ⊢ φ [ Δ_{A} ])
            (t₁ t₂ : tm Γ A)
  : t₁ ≡ t₂ ⊢ φ [ ⟨ t₁ , t₂ ⟩ ].
Proof.
  pose (counit_from_right_adjoint (pr22 (pr222 (pr222 H)) A) φ) as r.
  pose (hyperdoctrine_proof_subst ⟨ t₁ , t₂ ⟩ r) as r'.
  use (hyperdoctrine_cut _ r').
  unfold first_order_hyperdoctrine_equal.
  use hyperdoctrine_proof_subst.
  use (#(left_adjoint (pr22 (pr222 (pr222 H)) A))).
  exact p.
Qed.

Proposition hyperdoctrine_eq_elim_help_con'
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (φ : form ((A ×h A) ×h Γ))
            (p : ⊤ ⊢ φ [ ⟨ Δ_{A} [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ])
            (t₁ t₂ : tm Γ A)
  : t₁ ≡ t₂ ⊢ φ [ ⟨ ⟨ t₁ , t₂ ⟩ , tm_var _ ⟩ ].
Proof.
  assert (⊤ ⊢ (∀h φ) [ Δ_{ A } ]) as q.
  {
    rewrite forall_subst.
    use forall_intro.
    rewrite truth_subst.
    rewrite hyperdoctrine_diag_subst.
    rewrite hyperdoctrine_diag_subst in p.
    exact p.
  }
  refine (hyperdoctrine_cut (hyperdoctrine_eq_elim_help (∀h φ) q t₁ t₂) _).
  rewrite forall_subst.
  use (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) (tm_var _))).
  rewrite hyperdoctrine_comp_subst.
  rewrite hyperdoctrine_pair_subst.
  rewrite tm_subst_comp.
  rewrite hyperdoctrine_pair_comp_pr1.
  rewrite hyperdoctrine_pair_comp_pr2.
  rewrite tm_subst_var.
  apply hyperdoctrine_hyp.
Qed.

Definition hyperdoctrine_eq_elim_help_con_sub
           {H : first_order_hyperdoctrine}
           (Γ A : ty H)
  : tm ((A ×h A) ×h Γ) (Γ ×h (A ×h A)).
Proof.
  refine ⟨ _ , ⟨ _ , _ ⟩ ⟩.
  - exact (π₂ (tm_var _)).
  - exact ((π₁ (tm_var _)) [ π₁ (tm_var _) ]tm).
  - exact ((π₂ (tm_var _)) [ π₁ (tm_var _) ]tm).
Defined.

Proposition hyperdoctrine_eq_elim_help_con
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (φ : form (Γ ×h (A ×h A)))
            (p : ⊤ ⊢ φ [ ⟨ π₁ (tm_var _) , Δ_{A} [ π₂ (tm_var _) ]tm ⟩ ])
            (t₁ t₂ : tm Γ A)
  : t₁ ≡ t₂ ⊢ φ [ ⟨ tm_var _ , ⟨ t₁ , t₂ ⟩ ⟩ ].
Proof.
  pose (s := hyperdoctrine_eq_elim_help_con_sub Γ A).
  assert (⊤ ⊢ φ [s] [⟨ Δ_{ A } [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩])
    as q.
  {
    unfold s, hyperdoctrine_eq_elim_help_con_sub.
    rewrite hyperdoctrine_comp_subst.
    rewrite hyperdoctrine_diag_subst.
    rewrite !hyperdoctrine_pair_subst.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !tm_subst_comp.
    rewrite !hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite hyperdoctrine_diag_subst in p.
    pose (hyperdoctrine_proof_subst ⟨ π₂ (tm_var _) , π₁ (tm_var _) ⟩ p) as p'.
    rewrite truth_subst in p'.
    refine (hyperdoctrine_cut p' _).
    rewrite hyperdoctrine_comp_subst.
    rewrite !hyperdoctrine_pair_subst.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !hyperdoctrine_pair_comp_pr1.
    apply hyperdoctrine_hyp.
  }
  use (hyperdoctrine_cut (hyperdoctrine_eq_elim_help_con' (φ [ s ]) q t₁ t₂)).
  unfold s, hyperdoctrine_eq_elim_help_con_sub.
  rewrite hyperdoctrine_comp_subst.
  rewrite !hyperdoctrine_pair_subst.
  rewrite hyperdoctrine_pair_comp_pr2.
  rewrite !tm_subst_comp.
  rewrite !hyperdoctrine_pair_comp_pr1.
  rewrite hyperdoctrine_pair_comp_pr2.
  apply hyperdoctrine_hyp.
Qed.

Proposition hyperdoctrine_eq_elim
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            (φ : form (Γ ×h A))
            {t₁ t₂ : tm Γ A}
            (p : Δ ⊢ t₁ ≡ t₂)
            (q : Δ ⊢ φ [ ⟨ tm_var _ , t₁ ⟩ ])
  : Δ ⊢ φ [ ⟨ tm_var _ , t₂ ⟩ ].
Proof.
  pose (φ [ ⟨ π₁ (tm_var _) , (π₁ (tm_var _)) [ π₂ (tm_var _) ]tm ⟩ ]
        ⇒
        φ [ ⟨ π₁ (tm_var _) , (π₂ (tm_var _)) [ π₂ (tm_var _) ]tm ⟩ ])
    as ψ.
  assert (⊤ ⊢ ψ [⟨ π₁ (tm_var (Γ ×h A)), Δ_{ A } [ π₂ (tm_var (Γ ×h A)) ]tm ⟩])
    as r.
  {
    unfold ψ.
    rewrite impl_subst.
    rewrite !hyperdoctrine_comp_subst.
    rewrite !hyperdoctrine_pair_subst.
    rewrite !tm_subst_comp.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite <- !tm_subst_comp.
    unfold hyperdoctrine_diag.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !var_tm_subst.
    apply impl_id.
  }
  pose proof (hyperdoctrine_eq_elim_help_con ψ r t₁ t₂) as r'.
  unfold ψ in r'.
  rewrite impl_subst in r'.
  rewrite !hyperdoctrine_comp_subst in r'.
  rewrite !hyperdoctrine_pair_subst in r'.
  rewrite !tm_subst_comp in r'.
  rewrite hyperdoctrine_pair_comp_pr1 in r'.
  rewrite hyperdoctrine_pair_comp_pr2 in r'.
  rewrite hyperdoctrine_pair_comp_pr1 in r'.
  rewrite hyperdoctrine_pair_comp_pr2 in r'.
  use (impl_elim q).
  use (hyperdoctrine_cut p).
  exact r'.
Qed.

(** * 11. Derived rules for equality *)
Proposition hyperdoctrine_eq_sym
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {t₁ t₂ : tm Γ A}
            (p : Δ ⊢ t₁ ≡ t₂)
  : Δ ⊢ t₂ ≡ t₁.
Proof.
  pose (φ := (π₂ (tm_var _) ≡ t₁ [ π₁ (tm_var _) ]tm) : form (Γ ×h A)).
  assert (Δ ⊢ φ [⟨ tm_var Γ , t₁ ⟩]) as q.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !tm_subst_comp.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite tm_subst_var.
    rewrite hyperdoctrine_pair_comp_pr2.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p q) as r.
  unfold φ in r.
  rewrite equal_subst in r.
  rewrite !tm_subst_comp in r.
  rewrite hyperdoctrine_pair_comp_pr1 in r.
  rewrite tm_subst_var in r.
  rewrite hyperdoctrine_pair_comp_pr2 in r.
  exact r.
Qed.

Proposition hyperdoctrine_eq_trans
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {t₁ t₂ t₃ : tm Γ A}
            (p : Δ ⊢ t₁ ≡ t₂)
            (p' : Δ ⊢ t₂ ≡ t₃)
  : Δ ⊢ t₁ ≡ t₃.
Proof.
  pose (φ := (π₂ (tm_var _) ≡ t₃ [ π₁ (tm_var _) ]tm) : form (Γ ×h A)).
  assert (Δ ⊢ φ [⟨ tm_var Γ , t₂ ⟩]) as q.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !tm_subst_comp.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite tm_subst_var.
    rewrite hyperdoctrine_pair_comp_pr2.
    exact p'.
  }
  pose (hyperdoctrine_eq_elim φ (hyperdoctrine_eq_sym p) q) as r.
  unfold φ in r.
  rewrite equal_subst in r.
  rewrite !tm_subst_comp in r.
  rewrite hyperdoctrine_pair_comp_pr1 in r.
  rewrite tm_subst_var in r.
  rewrite hyperdoctrine_pair_comp_pr2 in r.
  exact r.
Qed.

Proposition hyperdoctrine_eq_transportf
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {t₁ t₂ : tm Γ A}
            (φ : form A)
            (p : Δ ⊢ t₁ ≡ t₂)
            (q : Δ ⊢ φ [ t₁ ])
  : Δ ⊢ φ [ t₂ ].
Proof.
  assert (Δ ⊢ t₁ ≡ t₂ ∧ φ [ t₁ ]) as r.
  {
    exact (conj_intro p q).
  }
  refine (hyperdoctrine_cut r _).
  pose (hyperdoctrine_eq_elim
          (φ [ π₂ (tm_var _) ])
          (weaken_left (hyperdoctrine_hyp _) _)
          (weaken_right (hyperdoctrine_hyp _) (t₁ ≡ t₂)))
    as h.
  rewrite !hyperdoctrine_comp_subst in h.
  rewrite !hyperdoctrine_pr2_subst in h.
  rewrite !var_tm_subst in h.
  rewrite !hyperdoctrine_pair_pr2 in h.
  exact h.
Qed.

Proposition hyperdoctrine_eq_transportb
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {t₁ t₂ : tm Γ A}
            (φ : form A)
            (p : Δ ⊢ t₁ ≡ t₂)
            (q : Δ ⊢ φ [ t₂ ])
  : Δ ⊢ φ [ t₁ ].
Proof.
  use (hyperdoctrine_eq_transportf _ _ q).
  use hyperdoctrine_eq_sym.
  exact p.
Qed.

Proposition hyperdoctrine_unit_eq_prf
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (t : tm Γ 𝟙)
            (Δ : form Γ)
  : Δ ⊢ t ≡ !!.
Proof.
  use hyperdoctrine_refl_eq.
  apply hyperdoctrine_unit_eq.
Qed.

Proposition hyperdoctrine_unit_tm_eq
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (t t' : tm Γ 𝟙)
            (Δ : form Γ)
  : Δ ⊢ t ≡ t'.
Proof.
  refine (hyperdoctrine_eq_trans (hyperdoctrine_unit_eq_prf t Δ) _).
  use hyperdoctrine_eq_sym.
  apply hyperdoctrine_unit_eq_prf.
Qed.

Proposition hyperdoctrine_eq_pr1
            {H : first_order_hyperdoctrine}
            {Γ A B : ty H}
            {Δ : form Γ}
            {t t' : tm Γ (A ×h B)}
            (p : Δ ⊢ t ≡ t')
  : Δ ⊢ π₁ t ≡ π₁ t'.
Proof.
  pose (φ := ((π₁ t) [ π₁ (tm_var _) ]tm ≡ π₁ (π₂ (tm_var (Γ ×h A ×h B)))) : form (Γ ×h A ×h B)).
  assert (Δ ⊢ φ [⟨ tm_var Γ , t ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !tm_subst_comp.
    rewrite !hyperdoctrine_pr1_subst.
    rewrite var_tm_subst.
    rewrite hyperdoctrine_pair_pr1.
    rewrite tm_subst_var.
    rewrite !hyperdoctrine_pr2_subst.
    rewrite var_tm_subst.
    rewrite hyperdoctrine_pair_pr2.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !tm_subst_comp in r'.
  rewrite !hyperdoctrine_pr1_subst in r'.
  rewrite var_tm_subst in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite tm_subst_var in r'.
  rewrite !hyperdoctrine_pr2_subst in r'.
  rewrite var_tm_subst in r'.
  rewrite hyperdoctrine_pair_pr2 in r'.
  exact r'.
Qed.

Proposition hyperdoctrine_eq_pr2
            {H : first_order_hyperdoctrine}
            {Γ A B : ty H}
            {Δ : form Γ}
            {t t' : tm Γ (A ×h B)}
            (p : Δ ⊢ t ≡ t')
  : Δ ⊢ π₂ t ≡ π₂ t'.
Proof.
  pose (φ := ((π₂ t) [ π₁ (tm_var _) ]tm ≡ π₂ (π₂ (tm_var (Γ ×h A ×h B)))) : form (Γ ×h A ×h B)).
  assert (Δ ⊢ φ [⟨ tm_var Γ , t ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !tm_subst_comp.
    rewrite !hyperdoctrine_pr1_subst.
    rewrite var_tm_subst.
    rewrite hyperdoctrine_pair_pr1.
    rewrite tm_subst_var.
    rewrite !hyperdoctrine_pr2_subst.
    rewrite var_tm_subst.
    rewrite hyperdoctrine_pair_pr2.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !tm_subst_comp in r'.
  rewrite !hyperdoctrine_pr1_subst in r'.
  rewrite var_tm_subst in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite tm_subst_var in r'.
  rewrite !hyperdoctrine_pr2_subst in r'.
  rewrite var_tm_subst in r'.
  rewrite hyperdoctrine_pair_pr2 in r'.
  exact r'.
Qed.

Proposition hyperdoctrine_eq_pair_left
            {H : first_order_hyperdoctrine}
            {Γ A B : ty H}
            {Δ : form Γ}
            {s₁ s₂ : tm Γ A}
            (p : Δ ⊢ s₁ ≡ s₂)
            (t : tm Γ B)
  : Δ ⊢ ⟨ s₁ , t ⟩ ≡ ⟨ s₂ , t ⟩.
Proof.
  pose (φ := (⟨ s₁ [ π₁ (tm_var _) ]tm , t [ π₁ (tm_var _) ]tm ⟩
              ≡
              ⟨ π₂ (tm_var _) , t [ π₁ (tm_var _) ]tm ⟩)
          : form (Γ ×h A)).
  assert (Δ ⊢ φ [⟨ tm_var Γ , s₁ ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !hyperdoctrine_pair_subst.
    rewrite !tm_subst_comp.
    rewrite hyperdoctrine_pr1_subst.
    rewrite hyperdoctrine_pr2_subst.
    rewrite !var_tm_subst.
    rewrite hyperdoctrine_pair_pr1.
    rewrite hyperdoctrine_pair_pr2.
    rewrite !tm_subst_var.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !hyperdoctrine_pair_subst in r'.
  rewrite !tm_subst_comp in r'.
  rewrite hyperdoctrine_pr1_subst in r'.
  rewrite hyperdoctrine_pr2_subst in r'.
  rewrite !var_tm_subst in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite hyperdoctrine_pair_pr2 in r'.
  rewrite !tm_subst_var in r'.
  exact r'.
Qed.

Proposition hyperdoctrine_eq_pair_right
            {H : first_order_hyperdoctrine}
            {Γ A B : ty H}
            {Δ : form Γ}
            (s : tm Γ A)
            {t₁ t₂ : tm Γ B}
            (p : Δ ⊢ t₁ ≡ t₂)
  : Δ ⊢ ⟨ s , t₁ ⟩ ≡ ⟨ s , t₂ ⟩.
Proof.
  pose (φ := (⟨ s [ π₁ (tm_var _) ]tm , t₁ [ π₁ (tm_var _) ]tm ⟩
              ≡
              ⟨ s [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩)
          : form (Γ ×h B)).
  assert (Δ ⊢ φ [⟨ tm_var Γ , t₁ ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !hyperdoctrine_pair_subst.
    rewrite !tm_subst_comp.
    rewrite hyperdoctrine_pr1_subst.
    rewrite hyperdoctrine_pr2_subst.
    rewrite !var_tm_subst.
    rewrite hyperdoctrine_pair_pr1.
    rewrite hyperdoctrine_pair_pr2.
    rewrite !tm_subst_var.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !hyperdoctrine_pair_subst in r'.
  rewrite !tm_subst_comp in r'.
  rewrite hyperdoctrine_pr1_subst in r'.
  rewrite hyperdoctrine_pr2_subst in r'.
  rewrite !var_tm_subst in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite hyperdoctrine_pair_pr2 in r'.
  rewrite !tm_subst_var in r'.
  exact r'.
Qed.

Proposition hyperdoctrine_eq_pair_eq
            {H : first_order_hyperdoctrine}
            {Γ A B : ty H}
            {Δ : form Γ}
            {s₁ s₂ : tm Γ A}
            (p : Δ ⊢ s₁ ≡ s₂)
            {t₁ t₂ : tm Γ B}
            (q : Δ ⊢ t₁ ≡ t₂)
  : Δ ⊢ ⟨ s₁ , t₁ ⟩ ≡ ⟨ s₂ , t₂ ⟩.
Proof.
  exact (hyperdoctrine_eq_trans
           (hyperdoctrine_eq_pair_left p _)
           (hyperdoctrine_eq_pair_right _ q)).
Qed.

Proposition hyperdoctrine_eq_prod_eq
            {H : first_order_hyperdoctrine}
            {Γ A B : ty H}
            {Δ : form Γ}
            {t₁ t₂ : tm Γ (A ×h B)}
            (p : Δ ⊢ π₁ t₁ ≡ π₁ t₂)
            (q : Δ ⊢ π₂ t₁ ≡ π₂ t₂)
  : Δ ⊢ t₁ ≡ t₂.
Proof.
  rewrite (hyperdoctrine_pair_eta t₁).
  rewrite (hyperdoctrine_pair_eta t₂).
  use hyperdoctrine_eq_pair_eq.
  - exact p.
  - exact q.
Qed.

Proposition hyperdoctrine_subst_eq
            {H : first_order_hyperdoctrine}
            {Γ Γ' B : ty H}
            {Δ : form _}
            {s₁ s₂ : tm Γ Γ'}
            (p : Δ ⊢ s₁ ≡ s₂)
            (t : tm Γ' B)
  : Δ ⊢ t [ s₁ ]tm ≡ t [ s₂ ]tm.
Proof.
  pose (φ := t [ s₁ [ π₁ (tm_var _) ]tm ]tm ≡ t [ π₂ (tm_var _) ]tm).
  assert (Δ ⊢ φ [⟨ tm_var Γ, s₁ ⟩]) as q.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !tm_subst_comp.
    rewrite hyperdoctrine_pr1_subst.
    rewrite hyperdoctrine_pr2_subst.
    rewrite var_tm_subst.
    rewrite hyperdoctrine_pair_pr1.
    rewrite hyperdoctrine_pair_pr2.
    rewrite tm_subst_var.
    apply hyperdoctrine_refl.
  }
  pose (r := hyperdoctrine_eq_elim φ p q).
  unfold φ in r.
  rewrite equal_subst in r.
  rewrite !tm_subst_comp in r.
  rewrite hyperdoctrine_pr1_subst in r.
  rewrite hyperdoctrine_pr2_subst in r.
  rewrite var_tm_subst in r.
  rewrite hyperdoctrine_pair_pr1 in r.
  rewrite hyperdoctrine_pair_pr2 in r.
  rewrite tm_subst_var in r.
  exact r.
Qed.

(** * 12. Derived connectives *)

(** * 12.1. Bi-implication *)
Definition first_order_hyperdoctrine_iff
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
           (φ ψ : form Γ)
  : form Γ
  := (φ ⇒ ψ) ∧ (ψ ⇒ φ).

Notation "φ ⇔ ψ" := (first_order_hyperdoctrine_iff φ ψ) : hyperdoctrine.

Proposition iff_intro
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ∧ φ ⊢ ψ)
            (q : Δ ∧ ψ ⊢ φ)
  : Δ ⊢ φ ⇔ ψ.
Proof.
  use conj_intro.
  - use impl_intro.
    exact p.
  - use impl_intro.
    exact q.
Qed.

Proposition iff_elim_left
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ ⇔ ψ)
            (q : Δ ⊢ φ)
  : Δ ⊢ ψ.
Proof.
  use (impl_elim q).
  exact (conj_elim_left p).
Qed.

Proposition iff_elim_right
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ ⇔ ψ)
            (q : Δ ⊢ ψ)
  : Δ ⊢ φ.
Proof.
  use (impl_elim q).
  exact (conj_elim_right p).
Qed.

Proposition iff_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (s : tm Γ₁ Γ₂)
            (φ ψ : form Γ₂)
  : ((φ ⇔ ψ) [ s ])
    =
    (φ [ s ] ⇔ ψ [ s ]).
Proof.
  unfold first_order_hyperdoctrine_iff.
  rewrite conj_subst.
  rewrite !impl_subst.
  apply idpath.
Qed.

Proposition iff_refl
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (Δ φ : form Γ)
  : Δ ⊢ φ ⇔ φ.
Proof.
  use iff_intro.
  - use weaken_right.
    apply hyperdoctrine_hyp.
  - use weaken_right.
    apply hyperdoctrine_hyp.
Qed.

Proposition iff_sym
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ ⇔ ψ)
  : Δ ⊢ ψ ⇔ φ.
Proof.
  use iff_intro.
  - use (iff_elim_right (weaken_left p _)).
    use weaken_right.
    apply hyperdoctrine_hyp.
  - use (iff_elim_left (weaken_left p _)).
    use weaken_right.
    apply hyperdoctrine_hyp.
Qed.

Proposition iff_trans
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ χ : form Γ}
            (p : Δ ⊢ φ ⇔ ψ)
            (q : Δ ⊢ ψ ⇔ χ)
  : Δ ⊢ φ ⇔ χ.
Proof.
  use iff_intro.
  - use (iff_elim_left (weaken_left q _)).
    use (iff_elim_left (weaken_left p _)).
    use weaken_right.
    apply hyperdoctrine_hyp.
  - use (iff_elim_right (weaken_left p _)).
    use (iff_elim_right (weaken_left q _)).
    use weaken_right.
    apply hyperdoctrine_hyp.
Qed.

Proposition iff_true_true
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ)
            (q : Δ ⊢ ψ)
  : Δ ⊢ φ ⇔ ψ.
Proof.
  use iff_intro.
  - use weaken_left.
    exact q.
  - use weaken_left.
    exact p.
Qed.

(** * 12.2. Negation *)
Definition first_order_hyperdoctrine_neg
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
           (φ : form Γ)
  : form Γ
  := φ ⇒ ⊥.

Notation "¬ φ" := (first_order_hyperdoctrine_neg φ) : hyperdoctrine.

Proposition neg_intro
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ∧ φ ⊢ ⊥)
  : Δ ⊢ ¬ φ.
Proof.
  use impl_intro.
  exact p.
Qed.

Proposition neg_elim
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            {Δ φ ψ : form Γ}
            (p : Δ ⊢ φ)
            (q : Δ ⊢ ¬ φ)
  : Δ ⊢ ψ.
Proof.
  use false_elim.
  use (impl_elim p).
  exact q.
Qed.

Proposition neg_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            (s : tm Γ₁ Γ₂)
            (φ : form Γ₂)
  : (¬ φ) [ s ]
    =
    ¬ (φ [ s ]).
Proof.
  unfold first_order_hyperdoctrine_neg.
  rewrite impl_subst.
  rewrite false_subst.
  apply idpath.
Qed.

(** * 13. A tactic for simplifying goals in the internal language of first-order hyperdoctrines *)

(**
  The tactic `hypersimplify` helps proving statements in the internal language of a hyperdoctrine.
  Such goals are of the shape `Δ ⊢ φ`. The tactic simplifies `Δ` and φ` by propagating the
  substitutions and by putting all terms that occur in either `Δ` or φ` in normal form. The tactic
  can print the rewrite statements that can replace it, by invoking `hypersimplify true` in Ltac2 or
  `hypersimplifyp` in Ltac1 (see the `Notation` commands further down).

  The tactic uses identities with two different levels:
  - The rewrites with level 0 are those that express how substitution acts on formulas, and are used
    to propagate substitutions in `Δ` and `φ`.
  - The rewrites with level 1 are all rewrite rules on terms in the language, used to normalize all
    terms in `Δ` and `φ`.

  In some cases, it is a bit faster to use `hypersimplify_form` to simplify the formula and delay using
  the full `hypersimplify` until it is necessary. The reason why this helps, is because one might
  have made the goal smaller and removed some unnecessary assumptions using weakening.
  This is demonstrated in `PERs.v` in the proof of [eq_per_axioms].

  The tactic can be extended with new traversals and rewrites. For example, handling of `~` is added
  in `PERs.v`.
 *)

Set Default Proof Mode "Ltac2".

Ltac2 mutable hypertraversals () : t_traversal list := [].

Ltac2 Set hypertraversals as traversals := fun _ =>
  (make_traversal (fun () => match! goal with | [|- (_  [ ?b]tm) = _ ] => '(λ x,  x [$b ]tm) end)  "" " [ _ ]tm") ::
  (make_traversal (fun () => match! goal with | [|- (?a [  _]tm) = _ ] => '(λ x,  $a[ x ]tm) end)    "_ [" "]tm") ::
  (make_traversal (fun () => match! goal with | [|- (_  [ ?b]  ) = _ ] => '(λ x,  x [$b ]  ) end) " " " [ _ ]"  ) ::
  (make_traversal (fun () => match! goal with | [|- (?a [  _]  ) = _ ] => '(λ x,  $a[ x ]  ) end)    "_ [" "]"  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ∧ ?b   ) = _ ] => '(λ x,  x ∧$b    ) end)  "" " ∧ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ∧  _   ) = _ ] => '(λ x,  $a∧ x    ) end)    "_ ∧ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ∨ ?b   ) = _ ] => '(λ x,  x ∨$b    ) end)  "" " ∨ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ∨  _   ) = _ ] => '(λ x,  $a∨ x    ) end)    "_ ∨ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ⇒ ?b   ) = _ ] => '(λ x,  x ⇒$b    ) end)  "" " ⇒ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ⇒  _   ) = _ ] => '(λ x,  $a⇒ x    ) end)    "_ ⇒ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ≡ ?b   ) = _ ] => '(λ x,  x ≡$b    ) end)  "" " ≡ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ≡  _   ) = _ ] => '(λ x,  $a≡ x    ) end)    "_ ≡ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (_  ⇔ ?b   ) = _ ] => '(λ x,  x ⇔$b    ) end)  "" " ⇔ _"    ) ::
  (make_traversal (fun () => match! goal with | [|- (?a ⇔  _   ) = _ ] => '(λ x,  $a⇔ x    ) end)    "_ ⇔ " ""  ) ::
  (make_traversal (fun () => match! goal with | [|- (⟨_ ,?b⟩   ) = _ ] => '(λ x, ⟨x ,$b⟩   ) end) "⟨" " , _⟩"   ) ::
  (make_traversal (fun () => match! goal with | [|- (⟨?a, _⟩   ) = _ ] => '(λ x, ⟨$a, x⟩   ) end)   "⟨_ , " "⟩" ) ::
  (make_traversal (fun () => match! goal with | [|- (∀h _      ) = _ ] => '(λ x, ∀h x      ) end)  "∀h " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (∃h _      ) = _ ] => '(λ x, ∃h x      ) end)  "∃h " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (¬  _      ) = _ ] => '(λ x, ¬  x      ) end)   "¬ " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (π₁ _      ) = _ ] => '(λ x, π₁ x      ) end)  "π₁ " ""     ) ::
  (make_traversal (fun () => match! goal with | [|- (π₂ _      ) = _ ] => '(λ x, π₂ x      ) end)  "π₂ " ""     ) ::
  traversals ().

Ltac2 mutable hyperrewrites () : (int * t_rewrite) list := [].

Ltac2 Set hyperrewrites as rewrites := fun () =>
  (0, (pn:(⊤[_]),            (fun () => '(truth_subst _                 )), "truth_subst _"                 )) ::
  (0, (pn:(⊥[_]),            (fun () => '(false_subst _                 )), "false_subst _"                 )) ::
  (0, (pn:((_ ∧ _)[_]),      (fun () => '(conj_subst _ _ _              )), "conj_subst _ _ _"              )) ::
  (0, (pn:((_ ∨ _)[_]),      (fun () => '(disj_subst _ _ _              )), "disj_subst _ _ _"              )) ::
  (0, (pn:((_ ⇒ _)[_]),      (fun () => '(impl_subst _ _ _              )), "impl_subst _ _ _"              )) ::
  (0, (pn:((_ ⇔ _)[_]),      (fun () => '(iff_subst _ _ _               )), "iff_subst _ _ _"               )) ::
  (0, (pn:((_ ≡ _)[_]),      (fun () => '(equal_subst _ _ _             )), "equal_subst _ _ _"             )) ::
  (0, (pn:((∀h _)[_]),       (fun () => '(forall_subst _ _              )), "forall_subst _ _"              )) ::
  (0, (pn:((∃h _)[_]),       (fun () => '(exists_subst _ _              )), "exists_subst _ _"              )) ::
  (0, (pn:((¬ _)[_]),        (fun () => '(neg_subst _ _                 )), "neg_subst _ _"                 )) ::
  (0, (pn:((_[_])[_]),       (fun () => '(hyperdoctrine_comp_subst _ _ _)), "hyperdoctrine_comp_subst _ _ _")) ::
  (0, (pn:(_[tm_var _]),     (fun () => '(hyperdoctrine_id_subst _      )), "hyperdoctrine_id_subst _"      )) ::
  (1, (pn:((π₁ _)[_]tm),     (fun () => '(hyperdoctrine_pr1_subst _ _   )), "hyperdoctrine_pr1_subst _ _"   )) ::
  (1, (pn:((π₂ _)[_]tm),     (fun () => '(hyperdoctrine_pr2_subst _ _   )), "hyperdoctrine_pr2_subst _ _"   )) ::
  (1, (pn:(⟨_, _⟩[_]tm),     (fun () => '(hyperdoctrine_pair_subst _ _ _)), "hyperdoctrine_pair_subst _ _ _")) ::
  (1, (pn:((tm_var _)[_]tm), (fun () => '(var_tm_subst _                )), "var_tm_subst _"                )) ::
  (1, (pn:((_ [_]tm)[_]tm),  (fun () => '(tm_subst_comp _ _ _           )), "tm_subst_comp _ _ _"           )) ::
  (1, (pn:(_[tm_var _]tm),   (fun () => '(tm_subst_var _                )), "tm_subst_var _"                )) ::
  (1, (pn:(π₁⟨_, _⟩),        (fun () => '(hyperdoctrine_pair_pr1 _ _    )), "hyperdoctrine_pair_pr1 _ _"    )) ::
  (1, (pn:(π₂⟨_, _⟩),        (fun () => '(hyperdoctrine_pair_pr2 _ _    )), "hyperdoctrine_pair_pr2 _ _"    )) ::
  (1, (pn:(!![_]tm),         (fun () => '(hyperdoctrine_unit_tm_subst _ )), "hyperdoctrine_unit_tm_subst _ ")) ::
  rewrites ().

Ltac2 hypertop_traversals (ltac2 : bool) (print: bool) : ((unit -> unit) * navigation) list :=
  ((fun () => match! goal with
    | [ |- _ = _ ] => refine '(!(_ @ !_))
    end), {
      left := [""];
      right := [""];
      preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(_ @ !maponpaths "], " ", ").");
      print := print
  }) :: ((fun () => match! goal with
    | [ |- _ = _ ] => refine '(_ @ _)
    end), {
      left := [""];
      right := [""];
      preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(maponpaths "], " ", " @ _).");
      print := print
  }) :: ((fun () => match! goal with
    | [ |- ?a ⊢ _ ] => refine '(transportb (λ x, $a ⊢ x) _ _); cbv beta
    end), {
      left := ["_ ⊢ "];
      right := [""];
      preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(transportb "], " ", " _).");
      print := print
  }) :: ((fun () => match! goal with
    | [ |- _ ⊢ ?b ] => refine '(transportb (λ x, x ⊢ $b) _ _); cbv beta
    end), {
      left := [""];
      right := [" ⊢ _"];
      preinpostfix := (String.concat "" ["refine "; (if ltac2 then "'" else ""); "(transportb "], " ", " _).");
      print := print
  }) :: [].

Ltac2 hypersimplify0 (ltac2 : bool option) (print: bool option) : int option -> unit :=
  simplify
  (List.rev (hypertraversals ()))
  (List.rev (hyperrewrites ()))
  (List.rev (hypertop_traversals (Option.default true ltac2) (Option.default false print))).

Ltac2 Notation "hypersimplify" print(opt(next)) n(opt(next)) := hypersimplify0 (Some true) print (n).

Set Default Proof Mode "Classic".

Tactic Notation "hypersimplify" := ltac2:(hypersimplify0 (Some false) (Some false) None).
Tactic Notation "hypersimplifyp" := ltac2:(hypersimplify0 (Some false) (Some true) None).
Tactic Notation "hypersimplify_form" := ltac2:(hypersimplify0 (Some false) (Some false) (Some 0)).
Tactic Notation "hypersimplifyp_form" := ltac2:(hypersimplify0 (Some false) (Some true) (Some 0)).

Ltac simplify_form_step :=
  rewrite ?truth_subst,
    ?false_subst,
    ?conj_subst,
    ?disj_subst,
    ?impl_subst,
    ?forall_subst,
    ?exists_subst,
    ?equal_subst,
    ?iff_subst,
    ?neg_subst,
    ?hyperdoctrine_comp_subst,
    ?hyperdoctrine_id_subst.

Ltac simplify_form :=
  repeat (progress simplify_form_step).

Ltac simplify_term_step :=
  rewrite ?hyperdoctrine_pr1_subst,
    ?hyperdoctrine_pr2_subst,
    ?hyperdoctrine_pair_subst,
    ?var_tm_subst,
    ?tm_subst_comp,
    ?tm_subst_var,
    ?hyperdoctrine_pair_pr1,
    ?hyperdoctrine_pair_pr2,
    ?hyperdoctrine_unit_tm_subst.

Ltac simplify_term :=
  repeat (progress simplify_term_step).

Ltac simplify := simplify_form ; simplify_term.
