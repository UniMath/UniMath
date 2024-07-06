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

 **********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
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
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. First-order hyperdoctrines *)
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
     has_dependent_products (hyperdoctrine_cleaving H)
     ×
     has_dependent_sums (hyperdoctrine_cleaving H).

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
     has_dependent_products (hyperdoctrine_cleaving H)
     ×
     has_dependent_sums (hyperdoctrine_cleaving H).

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
         pr2 (pr222 (pr222 H))).
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
     has_dependent_products (hyperdoctrine_cleaving H)
     ×
     has_dependent_sums (hyperdoctrine_cleaving H).

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
         pr2 (pr222 (pr222 H))).
Defined.

Definition make_first_order_hyperdoctrine
           (H : hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : has_dependent_products (hyperdoctrine_cleaving H))
           (DSH : has_dependent_sums (hyperdoctrine_cleaving H))
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
     DSH.

Definition make_univalent_first_order_hyperdoctrine
           (H : univalent_hyperdoctrine)
           (TH : fiberwise_terminal (hyperdoctrine_cleaving H))
           (IH : fiberwise_initial (hyperdoctrine_cleaving H))
           (PH : fiberwise_binproducts (hyperdoctrine_cleaving H))
           (CH : fiberwise_bincoproducts (hyperdoctrine_cleaving H))
           (IMPH : fiberwise_exponentials PH)
           (DPH : has_dependent_products (hyperdoctrine_cleaving H))
           (DSH : has_dependent_sums (hyperdoctrine_cleaving H))
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
     DSH.

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

Notation "φ ∧ ψ" := (first_order_hyperdoctrine_conj φ ψ).

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
  use (BinProductArrow _ (binprod_in_fib (pr1 (pr222 H)) Δ φ)).
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

(** * 6. Disjunction *)
Definition first_order_hyperdoctrine_disj
           {H : first_order_hyperdoctrine}
           {Γ : ty H}
           (φ ψ : form Γ)
  : form Γ
  := BinCoproductObject (bincoprod_in_fib (pr12 (pr222 H)) φ ψ).

Notation "φ ∨ ψ" := (first_order_hyperdoctrine_disj φ ψ).

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

Notation "φ ⇒ ψ" := (first_order_hyperdoctrine_impl φ ψ).

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
  := dep_prod (pr1 (pr222 (pr222 H))) (π₁ (identity (Γ ×h A))) φ.

Notation "'∀h' φ" := (first_order_hyperdoctrine_forall φ) (at level 10)
    : hyperdoctrine.

Proposition forall_intro
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {φ : form (Γ ×h A)}
            (p : Δ [ π₁ (identity _) ] ⊢ φ)
  : Δ ⊢ ∀h φ.
Proof.
  use (hyperdoctrine_cut
         (dep_prod_unit (pr1 (pr222 (pr222 H))) (π₁ (identity (Γ ×h A))) Δ)).
  use dep_prod_mor.
  cbn.
  exact p.
Qed.

Proposition forall_elim
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            {Δ : form Γ}
            {φ : form (Γ ×h A)}
            (p : Δ ⊢ ∀h φ)
            (t : tm Γ A)
  : Δ ⊢ φ [ ⟨ identity _ , t ⟩ ].
Proof.
  use (hyperdoctrine_cut p).
  assert ((∀h φ)[ π₁ (identity (Γ ×h A)) ] ⊢ φ) as r.
  {
    exact (dep_prod_counit (pr1 (pr222 (pr222 H))) (π₁ (identity (Γ ×h A))) φ).
  }
  pose (hyperdoctrine_proof_subst ⟨ identity Γ , t ⟩ r) as r'.
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
  : π₁ (identity (Γ₁ ×h A)) · s
    =
    ⟨ π₁ (identity _) · s , π₂ (identity _) ⟩ · π₁ (identity _).
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
       rewrite !assoc in q ;
       rewrite (hyperdoctrine_pr1_comp (H := H)) in q ;
       rewrite hyperdoctrine_pr2_comp in q ;
       rewrite !id_right in q ;
       rewrite hyperdoctrine_pair_pr2 in q ;
       rewrite q ;
       clear q ;
       pose (maponpaths (λ z, π₂ z) (pr12 ζ₂)) as q ; cbn in q ;
       rewrite (hyperdoctrine_pair_comp (H := H)) in q ;
       rewrite !assoc in q ;
       rewrite (hyperdoctrine_pr1_comp (H := H)) in q ;
       rewrite hyperdoctrine_pr2_comp in q ;
       rewrite !id_right in q ;
       rewrite hyperdoctrine_pair_pr2 in q ;
       rewrite q ;
       clear q ;
       apply idpath).
  - refine (⟨ t' , t · π₂ (identity _) ⟩ ,, _ ,, _).
    + abstract
        (rewrite hyperdoctrine_pair_comp ;
         rewrite !assoc ;
         rewrite hyperdoctrine_pair_comp_pr1 ;
         rewrite hyperdoctrine_pair_comp_pr2 ;
         rewrite <- p ;
         rewrite hyperdoctrine_pr1_comp ;
         rewrite hyperdoctrine_pr2_comp ;
         rewrite !id_right ;
         rewrite <- hyperdoctrine_pair_eta ;
         apply idpath).
    + abstract
        (rewrite hyperdoctrine_pair_comp_pr1 ;
         apply idpath).
Defined.

Proposition forall_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : ty H}
            (s : tm Γ₁ Γ₂)
            (φ : form (Γ₂ ×h A))
  : (∀h φ) [ s ]
    =
    (∀h (φ [ ⟨ π₁ (identity _) · s , π₂ (identity _) ⟩ ])).
Proof.
  pose (pr21 (pr222 (pr222 H)) _ _ _ _ _ _ _ _ _ (quantifier_subst_pb A s) φ) as p.
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
  := dep_sum (pr2 (pr222 (pr222 H))) (π₁ (identity (Γ ×h A))) φ.

Notation "'∃h' φ" := (first_order_hyperdoctrine_exists φ) (at level 10)
    : hyperdoctrine.

Proposition exists_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : ty H}
            (s : tm Γ₁ Γ₂)
            (φ : form (Γ₂ ×h A))
  : (∃h φ) [ s ]
    =
    ∃h (φ [ ⟨ π₁ (identity _) · s , π₂ (identity _) ⟩ ]).
Proof.
  pose (pr22 (pr222 (pr222 H)) _ _ _ _ _ _ _ _ _ (quantifier_subst_pb A s) φ) as p.
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
            (p : Δ ⊢ φ [ ⟨ identity _ , t ⟩ ])
  : Δ ⊢ ∃h φ.
Proof.
  use (hyperdoctrine_cut p).
  assert (φ ⊢ (∃h φ) [ π₁ (identity (Γ ×h A)) ]) as r.
  {
    exact (dep_sum_unit (pr2 (pr222 (pr222 H))) (π₁ (identity (Γ ×h A))) φ).
  }
  pose (hyperdoctrine_proof_subst ⟨ identity Γ , t ⟩ r) as r'.
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
            (q : φ ⊢ ψ [ π₁ (identity (Γ ×h A)) ])
  : Δ ⊢ ψ.
Proof.
  assert (∃h (ψ [ π₁ (identity (Γ ×h A)) ]) ⊢ ψ) as r.
  {
    exact (dep_sum_counit (pr2 (pr222 (pr222 H))) (π₁ (identity (Γ ×h A))) ψ).
  }
  use (hyperdoctrine_cut _ r).
  use (hyperdoctrine_cut p).
  use dep_sum_mor.
  exact q.
Qed.

Proposition frobenius_reciprocity
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (φ : form (Γ ×h A))
            (Δ : form Γ)
  : Δ ∧ (∃h φ) ⊢ (∃h (Δ [ π₁ (identity (Γ ×h A)) ] ∧ φ)).
Proof.
  enough (∃h φ ⊢ Δ ⇒ ∃h (Δ [ π₁ (identity (Γ ×h A)) ] ∧ φ)) as r₁.
  {
    assert (Δ ∧ ∃h φ ⊢ Δ ⇒ ∃h (Δ [ π₁ (identity (Γ ×h A)) ] ∧ φ)) as r₂.
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
  - exact (π₂ (identity _)).
  - rewrite hyperdoctrine_comp_subst.
    rewrite hyperdoctrine_pair_comp.
    rewrite !assoc.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !id_left.
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
            (q : Δ [ π₁ (identity (Γ ×h A)) ] ∧ φ ⊢ ψ [ π₁ (identity (Γ ×h A)) ])
  : Δ ⊢ ψ.
Proof.
  assert (∃h (ψ [ π₁ (identity (Γ ×h A)) ]) ⊢ ψ) as r.
  {
    exact (dep_sum_counit (pr2 (pr222 (pr222 H))) (π₁ (identity (Γ ×h A))) ψ).
  }
  use (hyperdoctrine_cut _ r).
  use (weaken_cut p).
  use (hyperdoctrine_cut (frobenius_reciprocity _ _)).
  use dep_sum_mor.
  exact q.
Qed.

(** * 10. Equality *)
Definition first_order_hyperdoctrine_equal
           {H : first_order_hyperdoctrine}
           {Γ A : ty H}
           (t₁ t₂ : tm Γ A)
  : form Γ
  := (dep_sum (pr2 (pr222 (pr222 H))) (Δ_{A}) ⊤) [ ⟨ t₁ , t₂ ⟩ ].

Notation "t₁ ≡ t₂" := (first_order_hyperdoctrine_equal t₁ t₂)
    : hyperdoctrine.

Proposition equal_subst
            {H : first_order_hyperdoctrine}
            {Γ₁ Γ₂ A : ty H}
            (s : Γ₁ --> Γ₂)
            (t₁ t₂ : tm Γ₂ A)
  : (t₁ ≡ t₂) [ s ] = (s · t₁ ≡ s · t₂).
Proof.
  unfold first_order_hyperdoctrine_equal.
  rewrite hyperdoctrine_comp_subst.
  rewrite hyperdoctrine_pair_comp.
  apply idpath.
Qed.

Proposition hyperdoctrine_refl'
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (t : tm Γ A)
  : ⊤ ⊢ t ≡ t.
Proof.
  assert (⊤ ⊢ (dep_sum (pr2 (pr222 (pr222 H))) (Δ_{A}) ⊤) [ Δ_{A} ]) as p.
  {
    exact (dep_sum_unit (pr2 (pr222 (pr222 H))) (Δ_{A}) ⊤).
  }
  pose (hyperdoctrine_proof_subst t p) as q.
  rewrite truth_subst in q.
  rewrite hyperdoctrine_comp_subst in q.
  rewrite hyperdoctrine_diag_comp in q.
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
  pose (dep_sum_counit (pr2 (pr222 (pr222 H))) (Δ_{A}) φ) as r.
  pose (hyperdoctrine_proof_subst ⟨ t₁ , t₂ ⟩ r) as r'.
  use (hyperdoctrine_cut _ r').
  unfold first_order_hyperdoctrine_equal.
  use hyperdoctrine_proof_subst.
  use dep_sum_mor.
  exact p.
Qed.

Proposition hyperdoctrine_eq_elim_help_con'
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (φ : form ((A ×h A) ×h Γ))
            (p : ⊤ ⊢ φ [ ⟨ π₁ (identity _) · Δ_{A} , π₂ (identity _) ⟩ ])
            (t₁ t₂ : tm Γ A)
  : t₁ ≡ t₂ ⊢ φ [ ⟨ ⟨ t₁ , t₂ ⟩ , identity _ ⟩ ].
Proof.
  assert (⊤ ⊢ (∀h φ) [ Δ_{ A } ]) as q.
  {
    rewrite forall_subst.
    use forall_intro.
    rewrite truth_subst.
    rewrite hyperdoctrine_diag_comp.
    rewrite hyperdoctrine_diag_comp in p.
    exact p.
  }
  refine (hyperdoctrine_cut (hyperdoctrine_eq_elim_help (∀h φ) q t₁ t₂) _).
  rewrite forall_subst.
  use (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) (identity _))).
  rewrite hyperdoctrine_comp_subst.
  rewrite hyperdoctrine_pair_comp.
  rewrite !assoc.
  rewrite hyperdoctrine_pair_comp_pr1.
  rewrite hyperdoctrine_pair_comp_pr2.
  rewrite id_left.
  apply hyperdoctrine_hyp.
Qed.

Definition hyperdoctrine_eq_elim_help_con_sub
           {H : first_order_hyperdoctrine}
           (Γ A : ty H)
  : tm ((A ×h A) ×h Γ) (Γ ×h (A ×h A)).
Proof.
  refine ⟨ _ , ⟨ _ , _ ⟩ ⟩.
  - exact (π₂ (identity _)).
  - exact (π₁ (identity _) · π₁ (identity _)).
  - exact (π₁ (identity _) · π₂ (identity _)).
Defined.

Proposition hyperdoctrine_eq_elim_help_con
            {H : first_order_hyperdoctrine}
            {Γ A : ty H}
            (φ : form (Γ ×h (A ×h A)))
            (p : ⊤ ⊢ φ [ ⟨ π₁ (identity _) , π₂ (identity _) · Δ_{A} ⟩ ])
            (t₁ t₂ : tm Γ A)
  : t₁ ≡ t₂ ⊢ φ [ ⟨ identity _ , ⟨ t₁ , t₂ ⟩ ⟩ ].
Proof.
  pose (s := hyperdoctrine_eq_elim_help_con_sub Γ A).
  assert (⊤ ⊢ φ [s] [⟨ π₁ (identity _) · Δ_{ A }, π₂ (identity _) ⟩])
    as q.
  {
    unfold s, hyperdoctrine_eq_elim_help_con_sub.
    rewrite hyperdoctrine_comp_subst.
    rewrite hyperdoctrine_diag_comp.
    rewrite !hyperdoctrine_pair_comp.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !assoc.
    rewrite !hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite hyperdoctrine_diag_comp in p.
    pose (hyperdoctrine_proof_subst ⟨ π₂ (identity _) , π₁ (identity _) ⟩ p) as p'.
    rewrite truth_subst in p'.
    refine (hyperdoctrine_cut p' _).
    rewrite hyperdoctrine_comp_subst.
    rewrite !hyperdoctrine_pair_comp.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !hyperdoctrine_pair_comp_pr1.
    apply hyperdoctrine_hyp.
  }
  use (hyperdoctrine_cut (hyperdoctrine_eq_elim_help_con' (φ [ s ]) q t₁ t₂)).
  unfold s, hyperdoctrine_eq_elim_help_con_sub.
  rewrite hyperdoctrine_comp_subst.
  rewrite !hyperdoctrine_pair_comp.
  rewrite hyperdoctrine_pair_comp_pr2.
  rewrite !assoc.
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
            (q : Δ ⊢ φ [ ⟨ identity _ , t₁ ⟩ ])
  : Δ ⊢ φ [ ⟨ identity _ , t₂ ⟩ ].
Proof.
  pose (φ [ ⟨ π₁ (identity _) , π₂ (identity _) · π₁ (identity _) ⟩ ]
        ⇒
        φ [ ⟨ π₁ (identity _) , π₂ (identity _) · π₂ (identity _) ⟩ ])
    as ψ.
  assert (⊤ ⊢ ψ [⟨ π₁ (identity (Γ ×h A)), π₂ (identity (Γ ×h A)) · Δ_{ A} ⟩])
    as r.
  {
    unfold ψ.
    rewrite impl_subst.
    rewrite !hyperdoctrine_comp_subst.
    rewrite !hyperdoctrine_pair_comp.
    rewrite !assoc.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !assoc'.
    unfold hyperdoctrine_diag.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite hyperdoctrine_pair_comp_pr2.
    rewrite !id_right.
    apply impl_id.
  }
  pose proof (hyperdoctrine_eq_elim_help_con ψ r t₁ t₂) as r'.
  unfold ψ in r'.
  rewrite impl_subst in r'.
  rewrite !hyperdoctrine_comp_subst in r'.
  rewrite !hyperdoctrine_pair_comp in r'.
  rewrite !assoc in r'.
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
  pose (φ := (π₂ (identity _) ≡ π₁ (identity _) · t₁) : form (Γ ×h A)).
  assert (Δ ⊢ φ [⟨ identity Γ , t₁ ⟩]) as q.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !assoc.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite id_left.
    rewrite hyperdoctrine_pair_comp_pr2.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p q) as r.
  unfold φ in r.
  rewrite equal_subst in r.
  rewrite !assoc in r.
  rewrite hyperdoctrine_pair_comp_pr1 in r.
  rewrite id_left in r.
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
  pose (φ := (π₂ (identity _) ≡ π₁ (identity _) · t₃) : form (Γ ×h A)).
  assert (Δ ⊢ φ [⟨ identity Γ , t₂ ⟩]) as q.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !assoc.
    rewrite hyperdoctrine_pair_comp_pr1.
    rewrite id_left.
    rewrite hyperdoctrine_pair_comp_pr2.
    exact p'.
  }
  pose (hyperdoctrine_eq_elim φ (hyperdoctrine_eq_sym p) q) as r.
  unfold φ in r.
  rewrite equal_subst in r.
  rewrite !assoc in r.
  rewrite hyperdoctrine_pair_comp_pr1 in r.
  rewrite id_left in r.
  rewrite hyperdoctrine_pair_comp_pr2 in r.
  exact r.
Qed.

Proposition hyperdoctrine_unit_eq
            {H : first_order_hyperdoctrine}
            {Γ : ty H}
            (t : tm Γ 𝟙)
            (Δ : form Γ)
  : Δ ⊢ t ≡ !!.
Proof.
  use hyperdoctrine_refl_eq.
  apply hyperdoctrine_unit_eq.
Qed.

Proposition hyperdoctrine_eq_pr1
            {H : first_order_hyperdoctrine}
            {Γ A B : ty H}
            {Δ : form Γ}
            {t t' : tm Γ (A ×h B)}
            (p : Δ ⊢ t ≡ t')
  : Δ ⊢ π₁ t ≡ π₁ t'.
Proof.
  pose (φ := (π₁ (identity _) · π₁ t ≡ π₁ (π₂ (identity (Γ ×h A ×h B)))) : form (Γ ×h A ×h B)).
  assert (Δ ⊢ φ [⟨ identity Γ , t ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !assoc.
    rewrite !hyperdoctrine_pr1_comp.
    rewrite id_right.
    rewrite hyperdoctrine_pair_pr1.
    rewrite id_left.
    rewrite !hyperdoctrine_pr2_comp.
    rewrite id_right.
    rewrite hyperdoctrine_pair_pr2.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !assoc in r'.
  rewrite !hyperdoctrine_pr1_comp in r'.
  rewrite id_right in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite id_left in r'.
  rewrite !hyperdoctrine_pr2_comp in r'.
  rewrite id_right in r'.
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
  pose (φ := (π₁ (identity _) · π₂ t ≡ π₂ (π₂ (identity (Γ ×h A ×h B)))) : form (Γ ×h A ×h B)).
  assert (Δ ⊢ φ [⟨ identity Γ , t ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !assoc.
    rewrite !hyperdoctrine_pr1_comp.
    rewrite id_right.
    rewrite hyperdoctrine_pair_pr1.
    rewrite id_left.
    rewrite !hyperdoctrine_pr2_comp.
    rewrite id_right.
    rewrite hyperdoctrine_pair_pr2.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !assoc in r'.
  rewrite !hyperdoctrine_pr1_comp in r'.
  rewrite id_right in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite id_left in r'.
  rewrite !hyperdoctrine_pr2_comp in r'.
  rewrite id_right in r'.
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
  pose (φ := (⟨ π₁ (identity _) · s₁ , π₁ (identity _) · t ⟩
              ≡
              ⟨ π₂ (identity _) , π₁ (identity _) · t ⟩)
          : form (Γ ×h A)).
  assert (Δ ⊢ φ [⟨ identity Γ , s₁ ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !hyperdoctrine_pair_comp.
    rewrite !assoc.
    rewrite hyperdoctrine_pr1_comp.
    rewrite hyperdoctrine_pr2_comp.
    rewrite !id_right.
    rewrite hyperdoctrine_pair_pr1.
    rewrite hyperdoctrine_pair_pr2.
    rewrite !id_left.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !hyperdoctrine_pair_comp in r'.
  rewrite !assoc in r'.
  rewrite hyperdoctrine_pr1_comp in r'.
  rewrite hyperdoctrine_pr2_comp in r'.
  rewrite !id_right in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite hyperdoctrine_pair_pr2 in r'.
  rewrite !id_left in r'.
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
  pose (φ := (⟨ π₁ (identity _) · s , π₁ (identity _) · t₁ ⟩
              ≡
              ⟨ π₁ (identity _) · s , π₂ (identity _) ⟩)
          : form (Γ ×h B)).
  assert (Δ ⊢ φ [⟨ identity Γ , t₁ ⟩]) as r.
  {
    unfold φ.
    rewrite equal_subst.
    rewrite !hyperdoctrine_pair_comp.
    rewrite !assoc.
    rewrite hyperdoctrine_pr1_comp.
    rewrite hyperdoctrine_pr2_comp.
    rewrite !id_right.
    rewrite hyperdoctrine_pair_pr1.
    rewrite hyperdoctrine_pair_pr2.
    rewrite !id_left.
    apply hyperdoctrine_refl.
  }
  pose (hyperdoctrine_eq_elim φ p r) as r'.
  unfold φ in r'.
  rewrite equal_subst in r'.
  rewrite !hyperdoctrine_pair_comp in r'.
  rewrite !assoc in r'.
  rewrite hyperdoctrine_pr1_comp in r'.
  rewrite hyperdoctrine_pr2_comp in r'.
  rewrite !id_right in r'.
  rewrite hyperdoctrine_pair_pr1 in r'.
  rewrite hyperdoctrine_pair_pr2 in r'.
  rewrite !id_left in r'.
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
