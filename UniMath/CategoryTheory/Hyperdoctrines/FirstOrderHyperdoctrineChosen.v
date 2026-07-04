(**

 First-order hyperdoctrines with chosen pullbacks for stability

 The existential and universal quantifiers in a first-order hyperdoctrine satisfy a
 stablity condition that expresses that these quantifiers are preserved under
 substitution. They are phrased by talking about all pullback squares in the base
 category. However, we can simplify these conditions for first-order hyperdoctrines.
 This is because the pullback squares used to express the Beck-Chevalley condition,
 are all isomorphic to a particular one, which we construct using binary products.
 In this file, we show that the usual stability condition for the universal and the
 existential quantifiers follow from the version where we talk about a particular
 pullback square in the base.

 Content
 1. The pullback square in the category of types
 2. Existential quantifiers with chosen pullbacks
 3. Universal quantifiers with chosen pullbacks

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.BeckChevalleyChosenProd.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.BeckChevalleyChosenSum.
Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.FiberEquivalence.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.
Local Open Scope hd.

(** * 1. The pullback square in the category of types *)
Definition prod_pullback_eq
           {H : preorder_hyperdoctrine}
           {Γ₁ Γ₂ : hyperdoctrine_type_category H}
           (A : hyperdoctrine_type_category H)
           (s : Γ₁ --> Γ₂)
  : BinProductOfArrows _ _ _ s (identity _) · π₁ (tm_var (Γ₂ ×h A))
    =
    π₁ (tm_var (Γ₁ ×h A)) · s.
Proof.
  unfold "π₁", tm_var.
  rewrite !id_left.
  rewrite BinProductOfArrowsPr1.
  apply idpath.
Qed.

Definition prod_pullback
           {H : preorder_hyperdoctrine}
           {Γ₁ Γ₂ : hyperdoctrine_type_category H}
           (A : hyperdoctrine_type_category H)
           (s : Γ₁ --> Γ₂)
  : isPullback (prod_pullback_eq A s).
Proof.
  intros Z f g p.
  use make_iscontr.
  - simple refine (_ ,, _ ,, _).
    + use BinProductArrow.
      * exact g.
      * exact (f · BinProductPr2 _ _).
    + abstract
        (cbn ;
         use BinProductArrowsEq ;
         [ rewrite !assoc' ;
           rewrite BinProductOfArrowsPr1 ;
           rewrite !assoc ;
           rewrite BinProductPr1Commutes ;
           rewrite <- p ;
           unfold "π₁", tm_var ;
           rewrite !id_left ;
           apply idpath
         | rewrite !assoc' ;
           rewrite BinProductOfArrowsPr2 ;
           rewrite id_right ;
           rewrite BinProductPr2Commutes ;
           apply idpath ]).
    + abstract
        (cbn ;
         unfold "π₁", tm_var ;
         rewrite !id_left ;
         apply BinProductPr1Commutes).
  - abstract
      (intros φ ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply homset_property | ] ;
       cbn ;
       use (BinProductArrowUnique _ _ _ _ _ _ _ _ _) ;
       [ refine (_ @ pr22 φ) ;
         unfold "π₁", tm_var ;
         rewrite !id_left ;
         apply idpath
       | rewrite <- (pr12 φ) ;
         rewrite !assoc' ;
         rewrite BinProductOfArrowsPr2 ;
         rewrite id_right ;
         apply idpath ]).
Defined.

(** * 2. Existential quantifiers with chosen pullbacks *)
Definition existential_quantifiers_chosen
           (H : preorder_hyperdoctrine)
  : UU
  := ∑ (sig : ∏ (Γ A : ty H), dependent_sum (hyperdoctrine_cleaving H) (π₁ (tm_var _))),
     ∏ (Γ₁ Γ₂ A : ty H)
       (s : Γ₁ --> Γ₂),
     left_beck_chevalley
       _
       _ s _ (BinProductOfArrows _ _ _ s (identity A))
       (prod_pullback_eq A s)
       (sig Γ₂ A)
       (sig Γ₁ A).

Definition existential_quantifiers_from_chosen
           {H : preorder_hyperdoctrine}
           (E : existential_quantifiers_chosen H)
  : existential_quantifiers H.
Proof.
  refine (pr1 E ,, _).
  intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ.
  pose (PB := make_Pullback _ Hp).
  pose (PB' := make_Pullback _ (prod_pullback A₂ s₁)).
  simple refine (left_beck_chevalley_adj_equiv'
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   (pr2 E _ _ _ _ φ)).
  - use fiber_functor_from_cleaving.
    + apply hyperdoctrine_cleaving.
    + exact (z_iso_inv (z_iso_from_Pullback_to_Pullback PB PB')).
  - apply fiber_functor_cleaving_of_z_iso_adj_equiv.
  - refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso _ _ _)
              (fiber_functor_on_eq_nat_z_iso _ _)).
    apply (PullbackArrow_PullbackPr2 PB).
  - refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso _ _ _)
              (fiber_functor_on_eq_nat_z_iso _ _)).
    apply (PullbackArrow_PullbackPr1 PB).
  - intro.
    apply locally_propositional_preorder_hyperdoctrine.
Defined.

Section MakeExistentialQuantifiersChosen.
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
          (ex_sub : ∏ (Γ₁ Γ₂ A : ty H)
                      (s : Γ₁ --> Γ₂)
                      (φ : form (Γ₂ ×h A)),
                    (ex _ _ φ) [ s ]
                    ⊢
                    ex _ _ (φ [ BinProductOfArrows _ _ _ s (identity _) ])).

  Definition make_existential_quantifiers_sum_chosen
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

  Definition make_existential_quantifiers_chosen
    : existential_quantifiers_chosen H.
  Proof.
    simple refine (_ ,, _).
    - exact make_existential_quantifiers_sum_chosen.
    - abstract
        (intros Γ₁ Γ₂ A s φ ;
         simple refine (_ ,, _ ,, _) ;
         [
         | apply locally_propositional_preorder_hyperdoctrine
         | apply locally_propositional_preorder_hyperdoctrine ] ;
         apply ex_sub).
  Defined.
End MakeExistentialQuantifiersChosen.

(** * 3. Universal quantifiers with chosen pullbacks *)
Definition universal_quantifiers_chosen
           (H : preorder_hyperdoctrine)
  : UU
  := ∑ (all : ∏ (Γ A : ty H), dependent_product (hyperdoctrine_cleaving H) (π₁ (tm_var _))),
     ∏ (Γ₁ Γ₂ A : ty H)
       (s : Γ₁ --> Γ₂),
    right_beck_chevalley
       _
       _ s _ (BinProductOfArrows _ _ _ s (identity A))
       (prod_pullback_eq A s)
       (all Γ₂ A)
       (all Γ₁ A).

Definition universal_quantifiers_from_chosen
           {H : preorder_hyperdoctrine}
           (E : universal_quantifiers_chosen H)
  : universal_quantifiers H.
Proof.
  refine (pr1 E ,, _).
  intros Γ₁ Γ₂ A₁ A₂ s₁ s₂ p Hp φ.
  pose (PB := make_Pullback _ Hp).
  pose (PB' := make_Pullback _ (prod_pullback A₂ s₁)).
  simple refine (right_beck_chevalley_adj_equiv'
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   _
                   (pr2 E _ _ _ _ φ)).
  - use fiber_functor_from_cleaving.
    + apply hyperdoctrine_cleaving.
    + exact (z_iso_inv (z_iso_from_Pullback_to_Pullback PB PB')).
  - apply fiber_functor_cleaving_of_z_iso_adj_equiv.
  - refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso _ _ _)
              (fiber_functor_on_eq_nat_z_iso _ _)).
    apply (PullbackArrow_PullbackPr2 PB).
  - refine (nat_z_iso_comp
              (fiber_functor_from_cleaving_comp_nat_z_iso _ _ _)
              (fiber_functor_on_eq_nat_z_iso _ _)).
    apply (PullbackArrow_PullbackPr1 PB).
  - intro.
    apply locally_propositional_preorder_hyperdoctrine.
Defined.

Section MakeUniversalQuantifiersChosen.
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
          (all_sub : ∏ (Γ₁ Γ₂ A : ty H)
                       (s : Γ₁ --> Γ₂)
                       (φ : form (Γ₂ ×h A)),
                     all _ _ (φ [ BinProductOfArrows _ _ _ s (identity _) ])
                     ⊢
                     (all _ _ φ) [ s ]).

  Definition make_universal_quantifiers_prod_chosen
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

  Definition make_universal_quantifiers_chosen
    : universal_quantifiers_chosen H.
  Proof.
    simple refine (_ ,, _).
    - exact make_universal_quantifiers_prod_chosen.
    - abstract
        (intros Γ₁ Γ₂ A s φ ;
        simple refine (_ ,, _ ,, _) ;
        [
        | apply locally_propositional_preorder_hyperdoctrine
        | apply locally_propositional_preorder_hyperdoctrine ] ;
         apply all_sub).
  Defined.
End MakeUniversalQuantifiersChosen.
