(**********************************************************************************************

 Hyperdoctrines

 In the field of categorical logic hyperdoctrines give a categorical structure in which one
 can interpret a framework for predicate logic. A hyperdoctrine is given by a category, which
 is the category of types and terms, together with a contravariant functor over it that lands in
 the category of partial order. This functor sends every type to the partial order of formulas
 over it, where the elements are given by formulas and the relation is given by provability. Note
 that in a hyperdoctrine, contexts and types are conflated, and terms and substitutions are
 conflated as well. Both contexts and types are interpreted as objects in the category, and both
 terms and substitutions are interpreted as morphisms.

 In this file, we formalize this notion. The most notable difference between the formalization
 and the definition described in the previous paragraph is the usage of displayed categories.
 More precisely, we do not represent a hyperdoctrine using a contravariant functor, but instead
 with a fibration that satisfies certain properties. These properties are local propositionality,
 which expresses that all displayed morphisms living over the same morphism in the base are equal.
 This implies that every fiber is a preorder, because all morphisms over the identity are the
 same. In addition, we require that this displayed category is a fibration, so that we have a
 substitution operation, and we require that this displayed category is univalent, so that the
 fibers are partial orders rather than just preorders. This increases the usability of the
 resulting language, and most examples satisfy this extra condition. The reason why this extra
 condition, is because type formers are only preserved up to isomorphism usually. If the
 displayed category is univalent, then these isomorphisms become equalities and we are also
 guaranteed to have a set of formulas. This allows us to rewrite with the substitution laws.

 We start by defining hyperdoctrines, and then we provide suitable accessors. These accessors
 essentially give a shallow embedding of first order predicate logic using hyperdoctrines. We
 also define suitable notations.

 References
 - "Adjointness in Foundations" by William Lawvere
 - "Categorical logic" by Andrew Pitts in Handbook of logic in computer science, Volume 5
 - "Tripos Theory in Retrospect" by Andrew Pitts

 Content
 1. Structure of hyperdoctrines
 2. Accessors for types in a hyperdoctrine
 3. Accessors for terms in a hyperdoctrine
 3.1. Substitution on terms
 3.2. Terms for the unit type
 3.3. Terms for the binary product type
 4. Formulas in a hyperdoctrine
 5. Proof terms in a hyperdoctrine
 6. Equality of formulas
 7. Substitution on formulas in a hyperdoctrine

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
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Declare Scope hyperdoctrine.
Delimit Scope hyperdoctrine with hd.

Local Open Scope hd.

(** * 1. Structure of hyperdoctrines *)
Definition preorder_hyperdoctrine
  : UU
  := ∑ (C : category)
       (D : disp_cat C),
     Terminal C
     ×
     BinProducts C
     ×
     cleaving D
     ×
     locally_propositional D.

Definition make_preorder_hyperdoctrine
           (C : category)
           (D : disp_cat C)
           (T : Terminal C)
           (BP : BinProducts C)
           (HD : cleaving D)
           (HD' : locally_propositional D)
  : preorder_hyperdoctrine
  := C ,, D ,, T ,, BP ,, HD ,, HD'.

Definition hyperdoctrine
  : UU
  := ∑ (C : category)
       (D : disp_cat C),
     Terminal C
     ×
     BinProducts C
     ×
     cleaving D
     ×
     locally_propositional D
     ×
     is_univalent_disp D.

Definition make_hyperdoctrine
           (C : category)
           (D : disp_cat C)
           (T : Terminal C)
           (BP : BinProducts C)
           (HD : cleaving D)
           (HD' : locally_propositional D)
           (HD'' : is_univalent_disp D)
  : hyperdoctrine
  := C ,, D ,, T ,, BP ,, HD ,, HD' ,, HD''.

Definition univalent_hyperdoctrine
  : UU
  := ∑ (C : category)
       (D : disp_cat C),
     Terminal C
     ×
     BinProducts C
     ×
     cleaving D
     ×
     locally_propositional D
     ×
     is_univalent_disp D
     ×
     is_univalent C.

Definition make_univalent_hyperdoctrine
           (C : category)
           (D : disp_cat C)
           (T : Terminal C)
           (BP : BinProducts C)
           (HD : cleaving D)
           (HD' : locally_propositional D)
           (HD'' : is_univalent_disp D)
           (HC : is_univalent C)
  : univalent_hyperdoctrine
  := C ,, D ,, T ,, BP ,, HD ,, HD' ,, HD'' ,, HC.

Coercion hyperdoctrine_to_preorder_hyperdoctrine
         (H : hyperdoctrine)
  : preorder_hyperdoctrine.
Proof.
  exact (pr1 H
         ,,
         pr12 H
         ,,
         pr122 H
         ,,
         pr1 (pr222 H)
         ,,
         pr12 (pr222 H)
         ,,
         pr122 (pr222 H)).
Defined.

Coercion univalent_hyperdoctrine_to_hyperdoctrine
         (H : univalent_hyperdoctrine)
  : hyperdoctrine.
Proof.
  exact (pr1 H
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
         pr1 (pr222 (pr222 H))).
Defined.

(** * 2. Accessors for types in a hyperdoctrine *)
Definition hyperdoctrine_type_category
           (H : preorder_hyperdoctrine)
  : category
  := pr1 H.

Definition hyperdoctrine_type
           (H : preorder_hyperdoctrine)
  : UU
  := ob (hyperdoctrine_type_category H).

Notation "'ty'" := hyperdoctrine_type : hyperdoctrine.

Definition hyperdoctrine_terminal_type
           (H : preorder_hyperdoctrine)
  : Terminal (hyperdoctrine_type_category H)
  := pr122 H.

Definition hyperdoctrine_unit_type
           {H : preorder_hyperdoctrine}
  : ty H
  := TerminalObject (hyperdoctrine_terminal_type H).

Notation "'𝟙'" := hyperdoctrine_unit_type : hyperdoctrine.

Definition hyperdoctrine_binproducts
           (H : preorder_hyperdoctrine)
  : BinProducts (hyperdoctrine_type_category H)
  := pr1 (pr222 H).

Definition hyperdoctrine_product
           {H : preorder_hyperdoctrine}
           (A B : ty H)
  : ty H
  := BinProductObject _ (hyperdoctrine_binproducts H A B).

Notation "A ×h B" := (hyperdoctrine_product A B) (at level 75, right associativity)
    : hyperdoctrine.

(** * 3. Accessors for terms in a hyperdoctrine *)

(** Note that for identity and composition we can reuse the notation of categories *)
Definition hyperdoctrine_term
           {H : preorder_hyperdoctrine}
           (Γ A : ty H)
  : UU
  := Γ --> A.

Notation "'tm'" := hyperdoctrine_term : hyperdoctrine.

Definition tm_var
           {H : preorder_hyperdoctrine}
           (A : ty H)
  : tm A A
  := identity _.

(** * 3.1. Substitution on terms *)
Definition tm_subst
           {H : preorder_hyperdoctrine}
           {Γ₁ Γ₂ A : ty H}
           (t : tm Γ₂ A)
           (s : tm Γ₁ Γ₂)
  : tm Γ₁ A
  := s · t.

Notation "t [ s ]tm" := (tm_subst t s) (at level 10) : hyperdoctrine.

Proposition tm_subst_var
            {H : preorder_hyperdoctrine}
            {Γ A : ty H}
            (t : tm Γ A)
  : t [ tm_var Γ ]tm = t.
Proof.
  unfold tm_subst, tm_var.
  apply id_left.
Qed.

Proposition var_tm_subst
            {H : preorder_hyperdoctrine}
            {Γ A : ty H}
            (t : tm Γ A)
  : (tm_var A) [ t ]tm = t.
Proof.
  unfold tm_subst, tm_var.
  apply id_right.
Qed.

Proposition tm_subst_comp
            {H : preorder_hyperdoctrine}
            {Γ₁ Γ₂ Γ₃ A : ty H}
            (s₁ : tm Γ₁ Γ₂)
            (s₂ : tm Γ₂ Γ₃)
            (t : tm Γ₃ A)
  : (t [ s₂ ]tm) [ s₁ ]tm = t [ s₂ [ s₁ ]tm ]tm.
Proof.
  unfold tm_subst.
  apply assoc.
Qed.

(** * 3.2. Terms for the unit type *)
Definition hyperdoctrine_unit_term
           {H : preorder_hyperdoctrine}
           {Γ : ty H}
  : tm Γ 𝟙
  := TerminalArrow _ _.

Notation "'!!'" := hyperdoctrine_unit_term : hyperdoctrine.

Proposition hyperdoctrine_unit_eq
            {H : preorder_hyperdoctrine}
            {Γ : ty H}
            (t₁ t₂ : tm Γ 𝟙)
  : t₁ = t₂.
Proof.
  apply TerminalArrowEq.
Qed.

Proposition hyperdoctrine_unit_eta
            {H : preorder_hyperdoctrine}
            {Γ : ty H}
            (t : tm Γ 𝟙)
  : t = !!.
Proof.
  apply hyperdoctrine_unit_eq.
Qed.

Proposition hyperdoctrine_unit_tm_subst
            {H : preorder_hyperdoctrine}
            {Γ Γ' : ty H}
            (s : tm Γ Γ')
  : !! [ s ]tm = !!.
Proof.
  apply hyperdoctrine_unit_eq.
Qed.

(** * 3.3. Terms for the binary product type *)
Definition hyperdoctrine_pr1
           {H : preorder_hyperdoctrine}
           {Γ A B : ty H}
           (t : tm Γ (A ×h B))
  : tm Γ A
  := t · BinProductPr1 _ _.

Notation "'π₁'" := hyperdoctrine_pr1 : hyperdoctrine.

Definition hyperdoctrine_pr2
           {H : preorder_hyperdoctrine}
           {Γ A B : ty H}
           (t : tm Γ (A ×h B))
  : tm Γ B
  := t · BinProductPr2 _ _.

Notation "'π₂'" := hyperdoctrine_pr2 : hyperdoctrine.

Definition hyperdoctrine_pair
           {H : preorder_hyperdoctrine}
           {Γ A B : ty H}
           (t₁ : tm Γ A)
           (t₂ : tm Γ B)
  : tm Γ (A ×h B)
  := BinProductArrow _ _ t₁ t₂.

Notation "⟨ t₁ , t₂ ⟩" := (hyperdoctrine_pair t₁ t₂) : hyperdoctrine.

Definition hyperdoctrine_diag
           {H : preorder_hyperdoctrine}
           (A : ty H)
  : tm A (A ×h A)
  := ⟨ tm_var _ , tm_var _ ⟩.

Notation "Δ_{ A }" := (hyperdoctrine_diag A) : hyperdoctrine.

Proposition hyperdoctrine_pair_pr1
            {H : preorder_hyperdoctrine}
            {Γ A B : ty H}
            (t₁ : tm Γ A)
            (t₂ : tm Γ B)
  : π₁ ⟨ t₁ , t₂ ⟩ = t₁.
Proof.
  unfold hyperdoctrine_pr1, hyperdoctrine_pair.
  apply BinProductPr1Commutes.
Qed.

Proposition hyperdoctrine_pair_pr2
            {H : preorder_hyperdoctrine}
            {Γ A B : ty H}
            (t₁ : tm Γ A)
            (t₂ : tm Γ B)
  : π₂ ⟨ t₁ , t₂ ⟩ = t₂.
Proof.
  unfold hyperdoctrine_pr2, hyperdoctrine_pair.
  apply BinProductPr2Commutes.
Qed.

Proposition hyperdoctrine_pr1_subst
            {H : preorder_hyperdoctrine}
            {Γ Γ' A B : ty H}
            (s : tm Γ Γ')
            (t : tm Γ' (A ×h B))
  : (π₁ t) [ s ]tm = π₁ (t [ s ]tm).
Proof.
  unfold hyperdoctrine_pr1, hyperdoctrine_pair.
  apply assoc.
Qed.

Proposition hyperdoctrine_pr1_comp
            {H : preorder_hyperdoctrine}
            {Γ Γ' A B : ty H}
            (s : tm Γ Γ')
            (t : tm Γ' (A ×h B))
  : s · π₁ t = π₁ (s · t).
Proof.
  apply hyperdoctrine_pr1_subst.
Qed.

Proposition hyperdoctrine_pair_comp_pr1
            {H : preorder_hyperdoctrine}
            {Γ A B : ty H}
            (t₁ : tm Γ A)
            (t₂ : tm Γ B)
  : (π₁ (tm_var _)) [ ⟨ t₁ , t₂ ⟩ ]tm = t₁.
Proof.
  rewrite hyperdoctrine_pr1_subst.
  unfold tm_subst.
  rewrite id_right.
  rewrite hyperdoctrine_pair_pr1.
  apply idpath.
Qed.

Proposition hyperdoctrine_pair_comp_pr1'
            {H : preorder_hyperdoctrine}
            {Γ A B : ty H}
            (t₁ : tm Γ A)
            (t₂ : tm Γ B)
  : ⟨ t₁, t₂ ⟩ · π₁ (tm_var (A ×h B)) = t₁.
Proof.
  apply hyperdoctrine_pair_comp_pr1.
Qed.

Proposition hyperdoctrine_pr2_subst
            {H : preorder_hyperdoctrine}
            {Γ Γ' A B : ty H}
            (s : tm Γ Γ')
            (t : tm Γ' (A ×h B))
  : (π₂ t) [ s ]tm = π₂ (t [ s ]tm).
Proof.
  unfold hyperdoctrine_pr2, hyperdoctrine_pair.
  apply assoc.
Qed.

Proposition hyperdoctrine_pr2_comp
            {H : preorder_hyperdoctrine}
            {Γ Γ' A B : ty H}
            (s : tm Γ Γ')
            (t : tm Γ' (A ×h B))
  : s · π₂ t = π₂ (s · t).
Proof.
  apply hyperdoctrine_pr2_subst.
Qed.

Proposition hyperdoctrine_pair_comp_pr2
            {H : preorder_hyperdoctrine}
            {Γ A B : ty H}
            (t₁ : tm Γ A)
            (t₂ : tm Γ B)
  : (π₂ (tm_var _)) [ ⟨ t₁ , t₂ ⟩ ]tm = t₂.
Proof.
  rewrite hyperdoctrine_pr2_subst.
  unfold tm_subst.
  rewrite id_right.
  rewrite hyperdoctrine_pair_pr2.
  apply idpath.
Qed.

Proposition hyperdoctrine_pair_comp_pr2'
            {H : preorder_hyperdoctrine}
            {Γ A B : ty H}
            (t₁ : tm Γ A)
            (t₂ : tm Γ B)
  : ⟨ t₁, t₂ ⟩ · π₂ (tm_var (A ×h B)) = t₂.
Proof.
  apply hyperdoctrine_pair_comp_pr2.
Qed.

Proposition hyperdoctrine_pair_subst
            {H : preorder_hyperdoctrine}
            {Γ Γ' A B : ty H}
            (s : tm Γ Γ')
            (t₁ : tm Γ' A)
            (t₂ : tm Γ' B)
  : ⟨ t₁ , t₂ ⟩ [ s ]tm = ⟨ t₁ [ s ]tm , t₂ [ s ]tm ⟩.
Proof.
  unfold hyperdoctrine_pair.
  apply precompWithBinProductArrow.
Qed.

Proposition hyperdoctrine_pair_comp
            {H : preorder_hyperdoctrine}
            {Γ Γ' A B : ty H}
            (s : tm Γ Γ')
            (t₁ : tm Γ' A)
            (t₂ : tm Γ' B)
  : s · ⟨ t₁, t₂ ⟩ = ⟨ s · t₁, s · t₂ ⟩.
Proof.
  apply hyperdoctrine_pair_subst.
Qed.

Proposition hyperdoctrine_pair_eta
            {H : preorder_hyperdoctrine}
            {Γ A B : ty H}
            (t : tm Γ (A ×h B))
  : t = ⟨ π₁ t , π₂ t ⟩.
Proof.
  unfold hyperdoctrine_pr1, hyperdoctrine_pr2, hyperdoctrine_pair.
  apply BinProductArrowEta.
Qed.

Proposition hyperdoctrine_diag_subst
            {H : preorder_hyperdoctrine}
            {Γ A : ty H}
            (t : tm Γ A)
  : Δ_{ A } [ t ]tm = ⟨ t , t ⟩.
Proof.
  unfold hyperdoctrine_diag.
  rewrite hyperdoctrine_pair_subst.
  unfold tm_subst.
  rewrite !id_right.
  apply idpath.
Qed.

(** * 4. Formulas in a hyperdoctrine *)
Definition hyperdoctrine_formula_disp_cat
           (H : preorder_hyperdoctrine)
  : disp_cat (hyperdoctrine_type_category H)
  := pr12 H.

Definition hyperdoctrine_formula
           {H : preorder_hyperdoctrine}
           (A : ty H)
  : UU
  := ob_disp (hyperdoctrine_formula_disp_cat H) A.

Notation "'form'" := hyperdoctrine_formula : hyperdoctrine.

Definition is_univalent_disp_hyperdoctrine
           (H : hyperdoctrine)
  : is_univalent_disp _
  := pr222 (pr222 H).

Proposition locally_propositional_preorder_hyperdoctrine
            (H : preorder_hyperdoctrine)
  : locally_propositional (hyperdoctrine_formula_disp_cat H).
Proof.
  exact (pr22 (pr222 H)).
Defined.

Proposition isaset_hyperdoctrine_formula
            {H : hyperdoctrine}
            (A : ty H)
  : isaset (form A).
Proof.
  use locally_propositional_to_obj_set.
  - exact (is_univalent_disp_hyperdoctrine H).
  - apply locally_propositional_preorder_hyperdoctrine.
Defined.

(** * 5. Proof terms in a hyperdoctrine *)
Definition hyperdoctrine_proof
           {H : preorder_hyperdoctrine}
           {A : ty H}
           (Δ ψ : form A)
  : UU
  := Δ -->[ identity _ ] ψ.

Notation "Δ ⊢ ψ" := (hyperdoctrine_proof Δ ψ) (at level 100) : hyperdoctrine.

Proposition hyperdoctrine_proof_eq
            {H : preorder_hyperdoctrine}
            {A : ty H}
            {Δ ψ : form A}
            (p q : Δ ⊢ ψ)
  : p = q.
Proof.
  apply (pr22 (pr222 H)).
Qed.

Proposition hyperdoctrine_hyp
            {H : preorder_hyperdoctrine}
            {A : ty H}
            (φ : form A)
  : φ ⊢ φ.
Proof.
  apply id_disp.
Qed.

Proposition hyperdoctrine_cut
            {H : preorder_hyperdoctrine}
            {A : ty H}
            {Δ ψ χ : form A}
            (p : Δ ⊢ ψ)
            (q : ψ ⊢ χ)
  : Δ ⊢ χ.
Proof.
  exact (transportf _ (id_left _) (p ;; q))%mor_disp.
Qed.

(** * 6. Equality of formulas *)
Proposition hyperdoctrine_formula_eq
            {H : hyperdoctrine}
            {A : ty H}
            {φ ψ : form A}
            (p : φ ⊢ ψ)
            (q : ψ ⊢ φ)
  : φ = ψ.
Proof.
  use (isotoid_disp (is_univalent_disp_hyperdoctrine H) (idpath _)).
  use make_z_iso_disp.
  - exact p.
  - refine (q ,, _ ,, _) ; apply (pr122 (pr222 H)).
Qed.

Proposition hyperdoctrine_formula_eq_f
            {H : hyperdoctrine}
            {A : ty H}
            {φ ψ : form A}
            (p : φ = ψ)
  : φ ⊢ ψ.
Proof.
  induction p.
  apply hyperdoctrine_hyp.
Qed.

Proposition hyperdoctrine_formula_eq_b
            {H : hyperdoctrine}
            {A : ty H}
            {φ ψ : form A}
            (p : φ = ψ)
  : ψ ⊢ φ.
Proof.
  induction p.
  apply hyperdoctrine_hyp.
Qed.

(** * 7. Substitution on formulas in a hyperdoctrine *)
Definition hyperdoctrine_cleaving
           (H : preorder_hyperdoctrine)
  : cleaving _
  := pr12 (pr222 H).

Definition hyperdoctrine_subst
           {H : preorder_hyperdoctrine}
           {Γ₁ Γ₂ : ty H}
           (φ : form Γ₂)
           (s : tm Γ₁ Γ₂)
  : form Γ₁
  := cleaving_ob (hyperdoctrine_cleaving H) s φ.

Notation "φ [ s ]" := (hyperdoctrine_subst φ s) (at level 10) : hyperdoctrine.

Proposition hyperdoctrine_id_subst
            {H : hyperdoctrine}
            {Γ : ty H}
            (φ : form Γ)
  : φ [ tm_var _ ] = φ.
Proof.
  refine (!_).
  use (isotoid_disp (is_univalent_disp_hyperdoctrine H) (idpath _)).
  use z_iso_disp_from_z_iso_fiber.
  exact (_ ,, is_nat_z_iso_fiber_functor_from_cleaving_identity (pr12 (pr222 H)) Γ φ).
Qed.

Proposition hyperdoctrine_comp_subst
            {H : hyperdoctrine}
            {Γ₁ Γ₂ Γ₃ : ty H}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (φ : form Γ₃)
  : φ [ s₂ ] [ s₁ ] = φ [ s₂ [ s₁ ]tm ].
Proof.
  use (isotoid_disp (is_univalent_disp_hyperdoctrine H) (idpath _)).
  use z_iso_disp_from_z_iso_fiber.
  exact (nat_z_iso_pointwise_z_iso
           (fiber_functor_from_cleaving_comp_nat_z_iso (pr12 (pr222 H)) s₂ s₁)
           φ).
Qed.

Proposition hyperdoctrine_proof_subst
            {H : preorder_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            {Δ φ : form Γ₂}
            (s : tm Γ₁ Γ₂)
            (p : Δ ⊢ φ)
  : Δ [ s ] ⊢ φ [ s ].
Proof.
  exact (#(fiber_functor_from_cleaving _ (hyperdoctrine_cleaving H) s) p).
Qed.

Proposition from_disp_mor_hyperdoctrine
            {H : preorder_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            {Δ : form Γ₁}
            {φ : form Γ₂}
            (s : tm Γ₁ Γ₂)
            (p : Δ -->[ s ] φ)
  : Δ ⊢ φ [ s ].
Proof.
  use (cartesian_factorisation
         (cartesian_lift_is_cartesian _ _ (hyperdoctrine_cleaving H _ _ s φ))).
  exact (transportb
           (λ z, _ -->[ z ] _)
           (id_left _)
           p).
Qed.

Proposition to_disp_mor_hyperdoctrine
            {H : preorder_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            {Δ : form Γ₁}
            {φ : form Γ₂}
            (s : tm Γ₁ Γ₂)
            (p : Δ ⊢ φ [ s ])
  : Δ -->[ s ] φ.
Proof.
  refine (transportf (λ z, _ -->[ z ] _) (id_left _) (p ;; _)%mor_disp).
  exact (mor_disp_of_cartesian_lift _ _ (hyperdoctrine_cleaving H _ _ s φ)).
Qed.

Proposition disp_mor_eq_hyperdoctrine
            {H : preorder_hyperdoctrine}
            {Γ₁ Γ₂ : ty H}
            {Δ : form Γ₁}
            {φ : form Γ₂}
            (s : tm Γ₁ Γ₂)
            (p q : Δ -->[ s ] φ)
  : p = q.
Proof.
  apply (pr22 (pr222 H)).
Qed.
