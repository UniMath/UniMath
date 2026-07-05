(**

 Full subcomprehension categories

 Content
 1. Predicates on comprehension categories
 2. The full subcomprehension category for a predicate
 3. Predicates on DFL full comprehension categories
 4. Full subcomprehension categories of DFL full comprehension categories
 5. ∏-types in the full subcomprehension categories
 6. The inclusion

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.FullSubDispCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.Democracy.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.EqualizerTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.ProductTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.UnitTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Predicates on comprehension categories *)
Definition comp_cat_pred_data
           (C : comp_cat)
  : UU
  := ∑ (PC : C → hProp), ∏ (Γ : C), PC Γ → ty Γ → hProp.

Definition make_comp_cat_pred_data
           {C : comp_cat}
           (PC : C → hProp)
           (PT : ∏ (Γ : C), PC Γ → ty Γ → hProp)
  : comp_cat_pred_data C
  := PC ,, PT.

Definition comp_cat_pred_con
           {C : comp_cat}
           (P : comp_cat_pred_data C)
           (Γ : C)
  : hProp
  := pr1 P Γ.

Definition comp_cat_pred_ty
           {C : comp_cat}
           (P : comp_cat_pred_data C)
           {Γ : C}
           (p : comp_cat_pred_con P Γ)
           (A : ty Γ)
  : hProp
  := pr2 P Γ p A.

Definition comp_cat_pred
           (C : comp_cat)
  : UU
  := ∑ (P : comp_cat_pred_data C),
     (comp_cat_pred_con P [])
     ×
     (∏ (Γ : C) (A : ty Γ) (p : comp_cat_pred_con P Γ),
      comp_cat_pred_ty P p A
      → comp_cat_pred_con P (Γ & A))
     ×
     (∏ (Γ₁ Γ₂ : C)
        (A : ty Γ₂)
        (s : Γ₁ --> Γ₂)
        (p₁ : comp_cat_pred_con P Γ₁)
        (p₂ : comp_cat_pred_con P Γ₂),
      comp_cat_pred_ty P p₂ A
      → comp_cat_pred_ty P p₁ (A [[ s ]])).

Definition make_comp_cat_pred
           {C : comp_cat}
           (P : comp_cat_pred_data C)
           (Pe : comp_cat_pred_con P [])
           (Pc : ∏ (Γ : C) (A : ty Γ) (p : comp_cat_pred_con P Γ),
                 comp_cat_pred_ty P p A
                 → comp_cat_pred_con P (Γ & A))
           (Ps : ∏ (Γ₁ Γ₂ : C)
                   (A : ty Γ₂)
                   (s : Γ₁ --> Γ₂)
                   (p₁ : comp_cat_pred_con P Γ₁)
                   (p₂ : comp_cat_pred_con P Γ₂),
                 comp_cat_pred_ty P p₂ A
                 → comp_cat_pred_ty P p₁ (A [[ s ]]))
  : comp_cat_pred C
  := P ,, Pe ,, Pc ,, Ps.

Coercion comp_cat_pred_to_data
         {C : comp_cat}
         (P : comp_cat_pred C)
  : comp_cat_pred_data C
  := pr1 P.

Proposition comp_cat_pred_empty_ctx
            {C : comp_cat}
            (P : comp_cat_pred C)
  : comp_cat_pred_con P [].
Proof.
  exact (pr12 P).
Defined.

Proposition comp_cat_pred_ctx_ext
            {C : comp_cat}
            (P : comp_cat_pred C)
            {Γ : C}
            (pΓ : comp_cat_pred_con P Γ)
            {A : ty Γ}
            (pA : comp_cat_pred_ty P pΓ A)
  : comp_cat_pred_con P (Γ & A).
Proof.
  exact (pr122 P Γ A pΓ pA).
Defined.

Proposition comp_cat_pred_subst_ty
            {C : comp_cat}
            (P : comp_cat_pred C)
            {Γ₁ Γ₂ : C}
            {A : ty Γ₂}
            (s : Γ₁ --> Γ₂)
            (p₁ : comp_cat_pred_con P Γ₁)
            (p₂ : comp_cat_pred_con P Γ₂)
            (q : comp_cat_pred_ty P p₂ A)
  : comp_cat_pred_ty P p₁ (A [[ s ]]).
Proof.
  exact (pr222 P Γ₁ Γ₂ A s p₁ p₂ q).
Defined.

(** * 2. The full subcomprehension category for a predicate *)
Section SubCompCat.
  Context {C : comp_cat}
          (P : comp_cat_pred C).

  Definition full_sub_comp_cat_ctx
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact (full_subcat C (comp_cat_pred_con P)).
    - abstract
        (use (is_univalent_full_subcat
                _
                (univalent_category_is_univalent C)) ;
         intros ;
         apply propproperty).
  Defined.

  Definition full_sub_comp_cat_ty_disp_cat
    : disp_cat full_sub_comp_cat_ctx
    := full_sub_disp_cat
         (disp_cat_of_types C)
         (comp_cat_pred_con P)
         (λ Γ p A, comp_cat_pred_ty P p A).

  Proposition is_univalent_disp_full_sub_comp_cat_ty_disp_cat
    : is_univalent_disp full_sub_comp_cat_ty_disp_cat.
  Proof.
    apply is_univalent_full_sub_disp_cat.
    - apply disp_univalent_category_is_univalent_disp.
    - intros.
      apply propproperty.
  Qed.

  Definition full_sub_comp_cat_ty
    : disp_univalent_category full_sub_comp_cat_ctx.
  Proof.
    use make_disp_univalent_category.
    - exact full_sub_comp_cat_ty_disp_cat.
    - exact is_univalent_disp_full_sub_comp_cat_ty_disp_cat.
  Defined.

  Definition full_sub_cat_with_terminal_disp_cat
    : cat_with_terminal_disp_cat.
  Proof.
    use make_cat_with_terminal_disp_cat.
    - exact full_sub_comp_cat_ctx.
    - use full_subcat_terminal.
      + exact [].
      + exact (comp_cat_pred_empty_ctx P).
    - exact full_sub_comp_cat_ty.
  Defined.

  Definition full_sub_cat_with_terminal_cleaving
    : cat_with_terminal_cleaving.
  Proof.
    use make_cat_with_terminal_cleaving.
    - exact full_sub_cat_with_terminal_disp_cat.
    - use cleaving_full_sub_disp_cat.
      + exact (cleaving_of_types C).
      + exact (λ Γ₁ Γ₂ s A pΓ₁ pΓ₂ pA, comp_cat_pred_subst_ty P s pΓ₂ pΓ₁ pA).
  Defined.

  Definition full_sub_comp_cat_comprehension
    : comprehension_functor full_sub_cat_with_terminal_cleaving.
  Proof.
    use make_comprehension_functor.
    - use (full_sub_disp_cat_comprehension _ _ _ (comp_cat_comprehension C)).
      intros Γ A pΓ pA ; cbn.
      exact (comp_cat_pred_ctx_ext P pΓ pA).
    - use is_cartesian_full_sub_disp_cat_comprehension.
      + exact (cleaving_of_types C).
      + intros Γ₁ Γ₂ s A pΓ₁ pΓ₂ pA.
        exact (comp_cat_pred_subst_ty P s pΓ₂ pΓ₁ pA).
      + exact (cartesian_disp_functor_is_cartesian (comp_cat_comprehension C)).
  Defined.

  Definition full_sub_comp_cat
    : comp_cat.
  Proof.
    use make_comp_cat.
    - exact full_sub_cat_with_terminal_cleaving.
    - exact full_sub_comp_cat_comprehension.
  Defined.
End SubCompCat.

Definition full_sub_full_comp_cat
           {C : full_comp_cat}
           (P : comp_cat_pred C)
  : full_comp_cat.
Proof.
  use make_full_comp_cat.
  - exact (full_sub_comp_cat P).
  - apply disp_functor_ff_full_sub_disp_cat_comprehension.
    apply full_comp_cat_comprehension_fully_faithful.
Defined.

(** * 3. Predicates on DFL full comprehension categories *)
Definition contains_unit_comp_cat_pred
           (C : dfl_full_comp_cat)
           (P : comp_cat_pred C)
  : UU
  := ∏ (Γ : C)
       (p : comp_cat_pred_con P Γ),
     comp_cat_pred_ty
       P
       p
       (dfl_full_comp_cat_unit Γ).

Definition contains_binprod_comp_cat_pred
           (C : dfl_full_comp_cat)
           (P : comp_cat_pred C)
  : UU
  := ∏ (Γ : C)
       (pΓ : comp_cat_pred_con P Γ)
       (A B : ty Γ),
     comp_cat_pred_ty P pΓ A
     → comp_cat_pred_ty P pΓ B
     → comp_cat_pred_ty
         P pΓ
         (BinProductObject
            _
            (binprod_in_fib (fiberwise_binproducts_dfl_full_comp_cat C) A B)).

Definition contains_equalizer_comp_cat_pred
           (C : dfl_full_comp_cat)
           (P : comp_cat_pred C)
  : UU
  := ∏ (Γ : C)
       (pΓ : comp_cat_pred_con P Γ)
       (A B : ty Γ)
       (ff gg : A -->[ identity _ ] B),
     comp_cat_pred_ty P pΓ A
     → comp_cat_pred_ty P pΓ B
     → comp_cat_pred_ty
         P pΓ
         (EqualizerObject
            (equalizer_in_fib
               (fiberwise_equalizers_dfl_full_comp_cat C)
               ff gg)).

Definition contains_democracy_comp_cat_pred
           (C : dfl_full_comp_cat)
           (P : comp_cat_pred C)
  : UU
  := ∏ (Γ : C)
       (pΓ : comp_cat_pred_con P Γ),
     comp_cat_pred_ty
       P
       (comp_cat_pred_empty_ctx P)
       (pr1 (is_democratic_dfl_full_comp_cat C Γ)).

Definition contains_sigma_comp_cat_pred
           (C : dfl_full_comp_cat)
           (P : comp_cat_pred C)
  : UU
  := ∏ (Γ : C)
       (pΓ : comp_cat_pred_con P Γ)
       (A : ty Γ)
       (pA : comp_cat_pred_ty P pΓ A)
       (B : ty (Γ & A)),
     comp_cat_pred_ty P (comp_cat_pred_ctx_ext P pΓ pA) B
     → comp_cat_pred_ty P pΓ (dfl_sigma_type A B).

Definition contains_pi_comp_cat_pred
           {C : comp_cat}
           (pi : comp_cat_dependent_prod C)
           (P : comp_cat_pred C)
  : UU
  := ∏ (Γ : C)
       (pΓ : comp_cat_pred_con P Γ)
       (A : ty Γ)
       (pA : comp_cat_pred_ty P pΓ A)
       (B : ty (Γ & A)),
     comp_cat_pred_ty P (comp_cat_pred_ctx_ext P pΓ pA) B
     → comp_cat_pred_ty P pΓ (dep_prod_cc pi A B).

Definition dfl_full_comp_cat_pred
           (C : dfl_full_comp_cat)
  : UU
  := ∑ (P : comp_cat_pred C),
     contains_unit_comp_cat_pred C P
     ×
     contains_binprod_comp_cat_pred C P
     ×
     contains_equalizer_comp_cat_pred C P
     ×
     contains_democracy_comp_cat_pred C P
     ×
     contains_sigma_comp_cat_pred C P.

Definition make_dfl_full_comp_cat_pred
           {C : dfl_full_comp_cat}
           (P : comp_cat_pred C)
           (Pu : contains_unit_comp_cat_pred C P)
           (Pp : contains_binprod_comp_cat_pred C P)
           (Pe : contains_equalizer_comp_cat_pred C P)
           (Pd : contains_democracy_comp_cat_pred C P)
           (Ps : contains_sigma_comp_cat_pred C P)
  : dfl_full_comp_cat_pred C
  := P ,, Pu ,, Pp ,, Pe ,, Pd ,, Ps.

Coercion dfl_full_comp_cat_pred_to_pred
         {C : dfl_full_comp_cat}
         (P : dfl_full_comp_cat_pred C)
  : comp_cat_pred (pr11 C)
  := pr1 P.

Proposition dfl_full_comp_cat_pred_unit
            {C : dfl_full_comp_cat}
            (P : dfl_full_comp_cat_pred C)
            {Γ : C}
            (p : comp_cat_pred_con P Γ)
  : comp_cat_pred_ty
      P
      p
      (dfl_full_comp_cat_unit Γ).
Proof.
  exact (pr12 P Γ p).
Defined.

Proposition dfl_full_comp_cat_pred_prod
            {C : dfl_full_comp_cat}
            (P : dfl_full_comp_cat_pred C)
            {Γ : C}
            (pΓ : comp_cat_pred_con P Γ)
            {A B : ty Γ}
            (pA : comp_cat_pred_ty P pΓ A)
            (pB : comp_cat_pred_ty P pΓ B)
  : comp_cat_pred_ty
      P pΓ
      (BinProductObject
         _
         (binprod_in_fib (fiberwise_binproducts_dfl_full_comp_cat C) A B)).
Proof.
  exact (pr122 P Γ pΓ A B pA pB).
Defined.

Proposition dfl_full_comp_cat_pred_equalizer
            {C : dfl_full_comp_cat}
            (P : dfl_full_comp_cat_pred C)
            {Γ : C}
            (pΓ : comp_cat_pred_con P Γ)
            {A B : ty Γ}
            (ff gg : A -->[ identity _ ] B)
            (pA : comp_cat_pred_ty P pΓ A)
            (pB : comp_cat_pred_ty P pΓ B)
  : comp_cat_pred_ty
      P pΓ
      (EqualizerObject
         (equalizer_in_fib
            (fiberwise_equalizers_dfl_full_comp_cat C)
            ff gg)).
Proof.
  exact (pr1 (pr222 P) Γ pΓ A B ff gg pA pB).
Defined.

Proposition dfl_full_comp_cat_pred_democracy
            {C : dfl_full_comp_cat}
            (P : dfl_full_comp_cat_pred C)
            {Γ : C}
            (pΓ : comp_cat_pred_con P Γ)
  : comp_cat_pred_ty
      P
      (comp_cat_pred_empty_ctx P)
      (pr1 (is_democratic_dfl_full_comp_cat C Γ)).
Proof.
  exact (pr12 (pr222 P) Γ pΓ).
Defined.

Proposition dfl_full_comp_cat_pred_sigma
            {C : dfl_full_comp_cat}
            (P : dfl_full_comp_cat_pred C)
            {Γ : C}
            (pΓ : comp_cat_pred_con P Γ)
            {A : ty Γ}
            (pA : comp_cat_pred_ty P pΓ A)
            {B : ty (Γ & A)}
            (pB : comp_cat_pred_ty P (comp_cat_pred_ctx_ext P pΓ pA) B)
  : comp_cat_pred_ty P pΓ (dfl_sigma_type A B).
Proof.
  exact (pr22 (pr222 P) Γ pΓ A pA B pB).
Defined.

(** * 4. Full subcomprehension categories of DFL full comprehension categories *)
Section SubDFLFullCompCat.
  Context {C : dfl_full_comp_cat}
          (P : dfl_full_comp_cat_pred C).

  Definition is_democratic_full_sub_full_comp_cat
    : is_democratic (full_sub_full_comp_cat P).
  Proof.
    intros Γ.
    simple refine (_ ,, _).
    - simple refine (_ ,, _).
      + exact (pr1 (is_democratic_dfl_full_comp_cat C (pr1 Γ))).
      + exact (dfl_full_comp_cat_pred_democracy P (pr2 Γ)).
    - use z_iso_full_subcat.
      exact (pr2 (is_democratic_dfl_full_comp_cat C (pr1 Γ))).
  Defined.

  Definition fiberwise_terminal_full_sub_full_comp_cat
    : fiberwise_terminal (cleaving_of_types (full_sub_full_comp_cat P)).
  Proof.
    use full_sub_disp_cat_fiberwise_terminal.
    - exact (fiberwise_terminal_dfl_full_comp_cat C).
    - intros Γ pΓ.
      exact (dfl_full_comp_cat_pred_unit P pΓ).
  Defined.

  Definition fiberwise_binproducts_full_sub_full_comp_cat
    : fiberwise_binproducts (cleaving_of_types (full_sub_full_comp_cat P)).
  Proof.
    use full_sub_disp_cat_fiberwise_binproducts.
    - exact (fiberwise_binproducts_dfl_full_comp_cat C).
    - intros Γ pΓ A B pA pB.
      exact (dfl_full_comp_cat_pred_prod P pΓ pA pB).
  Defined.

  Definition fiberwise_equalizers_full_sub_full_comp_cat
    : fiberwise_equalizers (cleaving_of_types (full_sub_full_comp_cat P)).
  Proof.
    use full_sub_disp_cat_fiberwise_equalizers.
    - exact (fiberwise_equalizers_dfl_full_comp_cat C).
    - intros Γ pΓ A B pA pB ff gg.
      exact (dfl_full_comp_cat_pred_equalizer P pΓ ff gg pA pB).
  Defined.

  Section DependentSum.
    Context {Γ : full_sub_full_comp_cat P}
            (A : ty Γ).

    Let sub : (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ}]
              ⟶
              (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ & A}]
      := fiber_functor_from_cleaving
           (disp_cat_of_types (full_sub_full_comp_cat P))
           (cleaving_of_types (full_sub_full_comp_cat P))
           (π A).

    Let sum : dependent_sum (cleaving_of_types C) (π (pr1 A))
      := pr11 (strong_dependent_sum_dfl_full_comp_cat C) (pr1 Γ) (pr1 A).

    Definition full_sub_full_comp_cat_dep_sum_data
      : functor_data
          (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ & A}]
          (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ}].
    Proof.
      use make_functor_data.
      - simple refine (λ B, _ ,, _).
        + exact (dfl_sigma_type (pr1 A) (pr1 B)).
        + use dfl_full_comp_cat_pred_sigma.
          * exact (pr2 A).
          * exact (pr2 B).
      - exact (λ B₁ B₂ f, #(left_adjoint sum) f).
    Defined.

    Proposition full_sub_full_comp_cat_dep_sum_laws
      : is_functor full_sub_full_comp_cat_dep_sum_data.
    Proof.
      split.
      - intro B.
        exact (functor_id (left_adjoint sum) (pr1 B)).
      - intros B₁ B₂ B₃ f g.
        rewrite !(comp_full_sub_disp_cat_fib
                    (disp_cat_of_types C)
                    (comp_cat_pred_con P)
                    (λ Γ p A, comp_cat_pred_ty P p A)).
        exact (functor_comp (left_adjoint sum) f g).
    Qed.

    Definition full_sub_full_comp_cat_dep_sum_adjoint
      : (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ & A}]
        ⟶
        (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ}].
    Proof.
      use make_functor.
      - exact full_sub_full_comp_cat_dep_sum_data.
      - exact full_sub_full_comp_cat_dep_sum_laws.
    Defined.

    Definition full_sub_full_comp_cat_dep_sum_unit
      : functor_identity _
        ⟹
        full_sub_full_comp_cat_dep_sum_adjoint ∙ sub.
    Proof.
      use make_nat_trans.
      - exact (λ B,
               dep_sum_unit_cc
                 (strong_dependent_sum_dfl_full_comp_cat C)
                 (pr1 A)
                 (pr1 B)).
      - abstract
          (intros B₁ B₂ f ;
           rewrite !(comp_full_sub_disp_cat_fib
                       (disp_cat_of_types C)
                       (comp_cat_pred_con P)
                       (λ Γ p A, comp_cat_pred_ty P p A)) ;
           refine (nat_trans_ax (unit_from_right_adjoint sum) _ _ f @ !_) ;
           apply maponpaths ;
           apply (full_sub_disp_cat_fiber_functor_from_cleaving
                    (disp_cat_of_types C)
                    (comp_cat_pred_con P)
                    (λ Γ p A, comp_cat_pred_ty P p A)
                    (cleaving_of_types C))).
    Defined.

    Definition full_sub_full_comp_cat_dep_sum_counit
      : sub ∙ full_sub_full_comp_cat_dep_sum_adjoint
        ⟹
        functor_identity _.
    Proof.
      use make_nat_trans.
      - exact (λ B,
               dep_sum_counit_cc
                 (strong_dependent_sum_dfl_full_comp_cat C)
                 (pr1 A)
                 (pr1 B)).
      - abstract
          (intros B₁ B₂ f ;
           rewrite !(comp_full_sub_disp_cat_fib
                       (disp_cat_of_types C)
                       (comp_cat_pred_con P)
                       (λ Γ p A, comp_cat_pred_ty P p A)) ;
           refine (_ @ nat_trans_ax (counit_from_right_adjoint sum) _ _ f) ;
           apply maponpaths_2 ;
           apply (maponpaths (#(left_adjoint sum))) ;
           exact (full_sub_disp_cat_fiber_functor_from_cleaving
                    (disp_cat_of_types C)
                    (comp_cat_pred_con P)
                    (λ Γ p A, comp_cat_pred_ty P p A)
                    (cleaving_of_types C)
                    _
                    (π A)
                    f)).
    Defined.

    Proposition full_sub_full_comp_cat_dep_sum_adjunction
      : form_adjunction
          full_sub_full_comp_cat_dep_sum_adjoint
          sub
          full_sub_full_comp_cat_dep_sum_unit
          full_sub_full_comp_cat_dep_sum_counit.
    Proof.
      split.
      - intros B.
        etrans.
        {
          apply (comp_full_sub_disp_cat_fib
                   (disp_cat_of_types C)
                   (comp_cat_pred_con P)
                   (λ Γ p A, comp_cat_pred_ty P p A)).
        }
        exact (pr122 sum (pr1 B)).
      - intros B.
        etrans.
        {
          apply (comp_full_sub_disp_cat_fib
                   (disp_cat_of_types C)
                   (comp_cat_pred_con P)
                   (λ Γ p A, comp_cat_pred_ty P p A)).
        }
        refine (_ @ pr222 sum (pr1 B)).
        apply maponpaths.
        apply (full_sub_disp_cat_fiber_functor_from_cleaving
                 (disp_cat_of_types C)
                 (comp_cat_pred_con P)
                 (λ Γ p A, comp_cat_pred_ty P p A)
                 (cleaving_of_types C)).
    Qed.

    Definition full_sub_full_comp_cat_dep_sum_adjoints
      : are_adjoints
          full_sub_full_comp_cat_dep_sum_adjoint
          sub.
    Proof.
      use make_are_adjoints.
      - exact full_sub_full_comp_cat_dep_sum_unit.
      - exact full_sub_full_comp_cat_dep_sum_counit.
      - exact full_sub_full_comp_cat_dep_sum_adjunction.
    Defined.

    Definition full_sub_full_comp_cat_dep_sum
      : dependent_sum (cleaving_of_types (full_sub_full_comp_cat P)) (π A)
      := full_sub_full_comp_cat_dep_sum_adjoint
         ,,
         full_sub_full_comp_cat_dep_sum_adjoints.
  End DependentSum.

  Definition dependent_sums_full_sub_full_comp_cat_stable
             {Γ₁ Γ₂ : full_sub_full_comp_cat P}
             (A : ty Γ₂)
             (s : Γ₁ --> Γ₂)
    : left_beck_chevalley
        _
        (π A) s (π (A [[ s ]])) _
        (comprehension_functor_mor_comm
           (comp_cat_comprehension _)
           (cleaving_of_types _ _ _ s A))
        (full_sub_full_comp_cat_dep_sum A)
        (full_sub_full_comp_cat_dep_sum (A [[ s ]])).
  Proof.
    intros B.
    use is_z_isomorphism_fiber_full_sub_disp_cat.
    pose (pr21 (strong_dependent_sum_dfl_full_comp_cat C)
                  _ _ _ _ _ _
                  (maponpaths
                     pr1
                     (comprehension_functor_mor_comm
                        (comp_cat_comprehension (full_sub_full_comp_cat P))
                        (cleaving_of_types (full_sub_full_comp_cat P) Γ₂ Γ₁ s A))))
      as H.
    refine (is_z_isomorphism_path _ (H _ (pr1 B))).
    - rewrite !left_beck_chevalley_nat_trans_ob.
      rewrite !(comp_full_sub_disp_cat_fib
                  (disp_cat_of_types C)
                  (comp_cat_pred_con P)
                  (λ Γ p A, comp_cat_pred_ty P p A)).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply (full_sub_disp_cat_fiber_functor_from_cleaving
                 (disp_cat_of_types C)
                 (comp_cat_pred_con P)
                 (λ Γ p A, comp_cat_pred_ty P p A)
                 (cleaving_of_types C)).
      }
      do 2 apply maponpaths.
      apply (comm_nat_z_iso_full_sub_disp_cat
               (disp_cat_of_types C)
               (comp_cat_pred_con P)
               (λ Γ p A, comp_cat_pred_ty P p A)
               (cleaving_of_types C)).
    - use (isPullback_mor_paths _ _ _ _ _ _ (comp_cat_is_pullback _ _)) ; apply idpath.
  Qed.

  Definition dependent_sums_full_sub_full_comp_cat
    : comp_cat_dependent_sum (full_sub_full_comp_cat P).
  Proof.
    use make_comp_cat_dependent_sum_from_chosen.
    use make_comp_cat_dependent_sum_chosen.
    - exact (λ Γ A, full_sub_full_comp_cat_dep_sum A).
    - exact (λ Γ₁ Γ₂ A s, dependent_sums_full_sub_full_comp_cat_stable A s).
  Defined.

  Definition strong_dependent_sums_full_sub_full_comp_cat
    : strong_dependent_sums (full_sub_full_comp_cat P).
  Proof.
    use make_strong_dependent_sums.
    - exact dependent_sums_full_sub_full_comp_cat.
    - intros Γ A B.
      use is_z_isomorphism_full_subcat.
      apply (strong_dependent_sums_iso
               (strong_dependent_sum_dfl_full_comp_cat C)).
  Defined.

  Definition full_sub_dfl_full_comp_cat
    : dfl_full_comp_cat.
  Proof.
    use make_dfl_full_comp_cat.
    - exact (full_sub_full_comp_cat P).
    - exact is_democratic_full_sub_full_comp_cat.
    - exact fiberwise_terminal_full_sub_full_comp_cat.
    - intro Γ.
      use is_z_isomorphism_full_subcat.
      apply dfl_full_comp_cat_extend_unit.
    - exact fiberwise_binproducts_full_sub_full_comp_cat.
    - exact fiberwise_equalizers_full_sub_full_comp_cat.
    - exact strong_dependent_sums_full_sub_full_comp_cat.
  Defined.
End SubDFLFullCompCat.

(** * 5. ∏-types in the full subcomprehension categories *)
Definition dfl_full_pi_comp_cat_pred
           (C : dfl_full_comp_cat)
           (pi : comp_cat_dependent_prod C)
  : UU
  := ∑ (P : dfl_full_comp_cat_pred C), contains_pi_comp_cat_pred pi P.

Definition make_dfl_full_pi_comp_cat_pred
           (C : dfl_full_comp_cat)
           (pi : comp_cat_dependent_prod C)
           (P : dfl_full_comp_cat_pred C)
           (Ppi : contains_pi_comp_cat_pred pi P)
  : dfl_full_pi_comp_cat_pred C pi
  := P ,, Ppi.

Coercion dfl_full_pi_comp_cat_pred_to_dfl_full_comp_cat_pred
         {C : dfl_full_comp_cat}
         {pi : comp_cat_dependent_prod C}
         (P : dfl_full_pi_comp_cat_pred C pi)
  : dfl_full_comp_cat_pred C
  := pr1 P.

Proposition dfl_full_comp_cat_pred_pi
            {C : dfl_full_comp_cat}
            {pi : comp_cat_dependent_prod C}
            (P : dfl_full_pi_comp_cat_pred C pi)
            {Γ : C}
            (pΓ : comp_cat_pred_con P Γ)
            {A : ty Γ}
            (pA : comp_cat_pred_ty P pΓ A)
            {B : ty (Γ & A)}
            (pB : comp_cat_pred_ty P (comp_cat_pred_ctx_ext P pΓ pA) B)
  : comp_cat_pred_ty P pΓ (dep_prod_cc pi A B).
Proof.
  exact (pr2 P Γ pΓ A pA B pB).
Defined.

Section SubDFLFullCompCatPi.
  Context {C : dfl_full_comp_cat}
          {pi : comp_cat_dependent_prod C}
          (P : dfl_full_pi_comp_cat_pred C pi).

  Section DependentProd.
    Context {Γ : full_sub_full_comp_cat P}
            (A : ty Γ).

    Let sub : (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ}]
              ⟶
              (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ & A}]
      := fiber_functor_from_cleaving
           (disp_cat_of_types (full_sub_full_comp_cat P))
           (cleaving_of_types (full_sub_full_comp_cat P))
           (π A).

    Let prod : dependent_product (cleaving_of_types C) (π (pr1 A))
      := pr1 pi (pr1 Γ) (pr1 A).

    Definition full_sub_full_comp_cat_dep_prod_data
      : functor_data
          (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ & A}]
          (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ}].
    Proof.
      use make_functor_data.
      - simple refine (λ B, _ ,, _).
        + exact (dep_prod_cc pi (pr1 A) (pr1 B)).
        + use dfl_full_comp_cat_pred_pi.
          * exact (pr2 A).
          * exact (pr2 B).
      - exact (λ B₁ B₂ f, #(Adjunctions.Core.right_adjoint prod) f).
    Defined.

    Proposition full_sub_full_comp_cat_dep_prod_laws
      : is_functor full_sub_full_comp_cat_dep_prod_data.
    Proof.
      split.
      - intro B.
        exact (functor_id (right_adjoint prod) (pr1 B)).
      - intros B₁ B₂ B₃ f g.
        rewrite !(comp_full_sub_disp_cat_fib
                    (disp_cat_of_types C)
                    (comp_cat_pred_con P)
                    (λ Γ p A, comp_cat_pred_ty P p A)).
        exact (functor_comp (right_adjoint prod) f g).
    Qed.

    Definition full_sub_full_comp_cat_dep_prod_adjoint
      : (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ & A}]
        ⟶
        (disp_cat_of_types (full_sub_full_comp_cat P))[{Γ}].
    Proof.
      use make_functor.
      - exact full_sub_full_comp_cat_dep_prod_data.
      - exact full_sub_full_comp_cat_dep_prod_laws.
    Defined.

    Definition full_sub_full_comp_cat_dep_prod_unit
      : functor_identity _
        ⟹
        sub ∙ full_sub_full_comp_cat_dep_prod_adjoint.
    Proof.
      use make_nat_trans.
      - exact (λ B, dep_prod_unit_cc pi (pr1 A) (pr1 B)).
      - abstract
          (intros B₁ B₂ f ;
           rewrite !(comp_full_sub_disp_cat_fib
                       (disp_cat_of_types C)
                       (comp_cat_pred_con P)
                       (λ Γ p A, comp_cat_pred_ty P p A)) ;
           refine (nat_trans_ax (unit_from_left_adjoint prod) _ _ f @ !_) ;
           apply maponpaths ;
           refine (maponpaths (#(right_adjoint prod)) _) ;
           exact (full_sub_disp_cat_fiber_functor_from_cleaving
                    (disp_cat_of_types C)
                    (comp_cat_pred_con P)
                    (λ Γ p A, comp_cat_pred_ty P p A)
                    (cleaving_of_types C)
                    _
                    (π A)
                    f)).
    Defined.

    Definition full_sub_full_comp_cat_dep_prod_counit
      : full_sub_full_comp_cat_dep_prod_adjoint ∙ sub
        ⟹
        functor_identity _.
    Proof.
      use make_nat_trans.
      - exact (λ B, dep_prod_counit_cc pi (pr1 A) (pr1 B)).
      - abstract
          (intros B₁ B₂ f ;
           rewrite !(comp_full_sub_disp_cat_fib
                       (disp_cat_of_types C)
                       (comp_cat_pred_con P)
                       (λ Γ p A, comp_cat_pred_ty P p A)) ;
           refine (_ @ nat_trans_ax (counit_from_left_adjoint prod) _ _ f) ;
           apply maponpaths_2 ;
           exact (full_sub_disp_cat_fiber_functor_from_cleaving
                    (disp_cat_of_types C)
                    (comp_cat_pred_con P)
                    (λ Γ p A, comp_cat_pred_ty P p A)
                    (cleaving_of_types C)
                    _
                    (π A)
                    _)).
    Defined.

    Proposition full_sub_full_comp_cat_dep_prod_adjunction
      : form_adjunction
          sub
          full_sub_full_comp_cat_dep_prod_adjoint
          full_sub_full_comp_cat_dep_prod_unit
          full_sub_full_comp_cat_dep_prod_counit.
    Proof.
      split.
      - intros B.
        etrans.
        {
          apply (comp_full_sub_disp_cat_fib
                   (disp_cat_of_types C)
                   (comp_cat_pred_con P)
                   (λ Γ p A, comp_cat_pred_ty P p A)).
        }
        refine (_ @ pr122 prod (pr1 B)).
        apply maponpaths_2.
        apply (full_sub_disp_cat_fiber_functor_from_cleaving
                 (disp_cat_of_types C)
                 (comp_cat_pred_con P)
                 (λ Γ p A, comp_cat_pred_ty P p A)
                 (cleaving_of_types C)).
      - intros B.
        etrans.
        {
          apply (comp_full_sub_disp_cat_fib
                   (disp_cat_of_types C)
                   (comp_cat_pred_con P)
                   (λ Γ p A, comp_cat_pred_ty P p A)).
        }
        exact (pr222 prod (pr1 B)).
    Qed.

    Definition full_sub_full_comp_cat_dep_prod_adjoints
      : are_adjoints
          sub
          full_sub_full_comp_cat_dep_prod_adjoint.
    Proof.
      use make_are_adjoints.
      - exact full_sub_full_comp_cat_dep_prod_unit.
      - exact full_sub_full_comp_cat_dep_prod_counit.
      - exact full_sub_full_comp_cat_dep_prod_adjunction.
    Defined.

    Definition full_sub_full_comp_cat_dep_product
      : dependent_product (cleaving_of_types (full_sub_full_comp_cat P)) (π A)
      := full_sub_full_comp_cat_dep_prod_adjoint
         ,,
         full_sub_full_comp_cat_dep_prod_adjoints.
  End DependentProd.

  Definition dependent_products_full_sub_full_comp_cat_stable
             {Γ₁ Γ₂ : full_sub_full_comp_cat P}
             (A : ty Γ₂)
             (s : Γ₁ --> Γ₂)
    : right_beck_chevalley
        _
        (π A) s (π (A [[ s ]])) _
        (comprehension_functor_mor_comm
           (comp_cat_comprehension _)
           (cleaving_of_types _ _ _ s A))
        (full_sub_full_comp_cat_dep_product A)
        (full_sub_full_comp_cat_dep_product (A [[ s ]])).
  Proof.
    intros B.
    use is_z_isomorphism_fiber_full_sub_disp_cat.
    pose (pr2 pi _ _ _ _ _ _
                 (maponpaths
                    pr1
                    (comprehension_functor_mor_comm
                       (comp_cat_comprehension (full_sub_full_comp_cat P))
                       (cleaving_of_types (full_sub_full_comp_cat P) Γ₂ Γ₁ s A))))
      as H.
    refine (is_z_isomorphism_path _ (H _ (pr1 B))).
    - rewrite !right_beck_chevalley_nat_trans_ob.
      rewrite !(comp_full_sub_disp_cat_fib
                  (disp_cat_of_types C)
                  (comp_cat_pred_con P)
                  (λ Γ p A, comp_cat_pred_ty P p A)).
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply (full_sub_disp_cat_fiber_functor_from_cleaving
                 (disp_cat_of_types C)
                 (comp_cat_pred_con P)
                 (λ Γ p A, comp_cat_pred_ty P p A)
                 (cleaving_of_types C)).
      }
      apply maponpaths_2.
      apply maponpaths.
      apply (comm_nat_z_iso_inv_full_sub_disp_cat
               (disp_cat_of_types C)
               (comp_cat_pred_con P)
               (λ Γ p A, comp_cat_pred_ty P p A)
               (cleaving_of_types C)).
    - use (isPullback_mor_paths _ _ _ _ _ _ (comp_cat_is_pullback _ _)) ; apply idpath.
  Qed.

  Definition comp_cat_dependent_prod_full_sub_dfl_full_comp_cat
    : comp_cat_dependent_prod (full_sub_dfl_full_comp_cat P).
  Proof.
    use make_comp_cat_dependent_prod_from_chosen.
    use make_comp_cat_dependent_prod_chosen.
    - exact (λ Γ A, full_sub_full_comp_cat_dep_product A).
    - exact (λ Γ₁ Γ₂ A s, dependent_products_full_sub_full_comp_cat_stable A s).
  Defined.
End SubDFLFullCompCatPi.

(** * 6. The inclusion *)
Section FullSubCompCatIncl.
  Context {C : comp_cat}
          (P : comp_cat_pred C).

  Definition full_sub_comp_cat_incl_terminal_disp_cat
    : functor_with_terminal_disp_cat (full_sub_comp_cat P) C.
  Proof.
    use make_functor_with_terminal_disp_cat.
    - exact (full_subcat_incl _).
    - use preserves_terminal_full_subcat_incl.
      + exact [].
      + exact (comp_cat_pred_empty_ctx P).
    - exact (full_sub_disp_cat_incl _ _ _).
  Defined.

  Definition full_sub_comp_cat_incl_terminal_cleaving
    : functor_with_terminal_cleaving (full_sub_comp_cat P) C.
  Proof.
    use make_functor_with_terminal_cleaving.
    - exact full_sub_comp_cat_incl_terminal_disp_cat.
    - use is_cartesian_full_sub_disp_cat_incl.
      + exact (cleaving_of_types C).
      + exact (λ Γ₁ Γ₂ s A pΓ₁ pΓ₂ pA, comp_cat_pred_subst_ty P s pΓ₂ pΓ₁ pA).
  Defined.

  Definition full_sub_comp_cat_incl_comp_nat_trans
    : comprehension_nat_trans
        (comp_cat_comprehension (full_sub_comp_cat P))
        (comp_cat_comprehension C)
        full_sub_comp_cat_incl_terminal_cleaving.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, id_disp _).
    - abstract
        (intros x y f xx yy ff ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         refine (_ @ !(transportb_cod_disp _ _ _)) ;
         cbn ;
         exact (id_right _ @ !(id_left _))).
  Defined.

  Definition full_sub_comp_cat_incl
    : comp_cat_functor (full_sub_comp_cat P) C.
  Proof.
    use make_comp_cat_functor.
    - exact full_sub_comp_cat_incl_terminal_cleaving.
    - exact full_sub_comp_cat_incl_comp_nat_trans.
  Defined.
End FullSubCompCatIncl.

Definition full_sub_full_comp_cat_incl
           {C : full_comp_cat}
           (P : comp_cat_pred C)
  : full_comp_cat_functor (full_sub_full_comp_cat P) C.
Proof.
  use make_full_comp_cat_functor.
  - exact (full_sub_comp_cat_incl P).
  - intros x xx.
    apply is_z_isomorphism_identity.
Defined.

Definition full_sub_dfl_full_comp_cat_incl
           {C : dfl_full_comp_cat}
           (P : dfl_full_comp_cat_pred C)
  : dfl_full_comp_cat_functor
      (full_sub_dfl_full_comp_cat P)
      C.
Proof.
  use make_dfl_full_comp_cat_functor.
  - exact (full_sub_full_comp_cat_incl P).
  - use preserves_terminal_fiber_functor_incl.
    + exact (cleaving_of_types C).
    + exact (fiberwise_terminal_dfl_full_comp_cat C).
    + intros Γ pΓ.
      exact (dfl_full_comp_cat_pred_unit P pΓ).
  - use preserves_binproduct_fiber_functor_incl.
    + exact (cleaving_of_types C).
    + exact (fiberwise_binproducts_dfl_full_comp_cat C).
    + intros Γ pΓ A B pA pB.
      exact (dfl_full_comp_cat_pred_prod P pΓ pA pB).
  - use preserves_equalizer_fiber_functor_incl.
    + exact (cleaving_of_types C).
    + exact (fiberwise_equalizers_dfl_full_comp_cat C).
    + intros Γ pΓ A B pA pB ff gg.
      exact (dfl_full_comp_cat_pred_equalizer P pΓ ff gg pA pB).
Defined.
