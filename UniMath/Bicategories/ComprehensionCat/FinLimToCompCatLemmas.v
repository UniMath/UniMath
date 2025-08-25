(**

 Some lemmas about the comprehension category arising from a category with finite limits

 Every category with finite limits gives rise to a comprehension category. Specifically,
 let `C` be a category with finite limits. Then we have a comprehension category whose
 displayed category of types is given by the arrow category together with the codomain
 functor and whose comprehension is given by the identity functor.

 There are various operations that we have within a comprehension category. These are:
 - Coercion. if we have a morphism `A <: B` over the identity, then every term of type
   `A` gives rise to a term of type `B`.
 - Substitution of terms. If we have a term `t : tm Δ A` and a substitution `s : Γ --> Δ`,
   then we also have a term `t [[ s ]]tm : tm Γ (A [[ s ]])`.
 We also have various coherence isomorphisms. For instance, we have an isomorphism expressing
 that `A [[ identity _ ]]` is isomorphic to `A`, that `A [[ s₂ ]] [[ s₁ ]]` and
 `A [[ s₁ · s₂ ]]` are isomorphic, and that `A [[ s₁ ]]` and `A [[ s₂ ]]` are isomorphic
 whenever `s₁ = s₂`. We also have a functoriality operation saying that
 `A [[ s ]] <: B [[ s ]]` whenever `A <: B`.

 In this file, we calculate each of these operations in case our comprehension category
 arises from a category with finite limits.

 Contents
 1. Operations on comprehension categories arising from categories with finite limits
 2. Operations on functors between categories with finite limits
 3. Operations on natural transformations

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Operations on comprehension categories arising from categories with finite limits *)
Section FinLimCompCatCalculation.
  Context {C : univ_cat_with_finlim}.

  Proposition finlim_to_comp_cat_coerce_eq
              {Γ : finlim_to_comp_cat C}
              {A B : ty Γ}
              (f : A <: B)
              (t : tm Γ A)
    : (t ↑ f : _ --> _)
      =
      t · dom_mor f.
  Proof.
    apply idpath.
  Qed.

  Proposition finlim_to_comp_cat_eq_subst_ty_pullback_pr1
              {Γ Δ : finlim_to_comp_cat C}
              (A : ty Δ)
              {s₁ s₂ : Γ --> Δ}
              (p : s₁ = s₂)
    : dom_mor (eq_subst_ty A p) · PullbackPr1 _
      =
      PullbackPr1 _.
  Proof.
    induction p.
    rewrite eq_subst_ty_idpath.
    simpl.
    apply id_left.
  Qed.

  Proposition finlim_to_comp_cat_eq_subst_ty_pullback_pr2
              {Γ Δ : finlim_to_comp_cat C}
              (A : ty Δ)
              {s₁ s₂ : Γ --> Δ}
              (p : s₁ = s₂)
    : dom_mor (eq_subst_ty A p) · PullbackPr2 _
      =
      PullbackPr2 _.
  Proof.
    induction p.
    rewrite eq_subst_ty_idpath.
    simpl.
    apply id_left.
  Qed.

  Proposition finlim_to_comp_cat_comp_subst_ty_pullback_pr1
              {Γ₁ Γ₂ Γ₃ : finlim_to_comp_cat C}
              (A : ty Γ₃)
              {s₁ : Γ₁ --> Γ₂}
              (s₂ : Γ₂ --> Γ₃)
    : dom_mor (comp_subst_ty s₁ s₂ A) · PullbackPr1 _
      =
      PullbackPr1 _ · PullbackPr1 _.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportb_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_comp_subst_ty_pullback_pr2
              {Γ₁ Γ₂ Γ₃ : finlim_to_comp_cat C}
              (A : ty Γ₃)
              {s₁ : Γ₁ --> Γ₂}
              (s₂ : Γ₂ --> Γ₃)
    : dom_mor (comp_subst_ty s₁ s₂ A) · PullbackPr2 _
      =
      PullbackPr2 _.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.

  Proposition finlim_to_comp_cat_id_subst_ty_pullback_pr1
              {Γ : finlim_to_comp_cat C}
              (A : ty Γ)
    : dom_mor (id_subst_ty A) · PullbackPr1 _
      =
      identity _.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportb_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_id_subst_ty_pullback_pr2
              {Γ : finlim_to_comp_cat C}
              (A : ty Γ)
    : dom_mor (id_subst_ty A) · PullbackPr2 _
      =
      cod_mor A.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.

  Proposition finlim_to_comp_cat_coerce_subst_ty_pullback_pr1
              {Γ₁ Γ₂ : finlim_to_comp_cat C}
              {A B : ty Γ₂}
              (s : Γ₁ --> Γ₂)
              (f : A <: B)
    : dom_mor (coerce_subst_ty s f) · PullbackPr1 _
      =
      PullbackPr1 _ · dom_mor f.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_coerce_subst_ty_pullback_pr2
              {Γ₁ Γ₂ : finlim_to_comp_cat C}
              {A B : ty Γ₂}
              (s : Γ₁ --> Γ₂)
              (f : A <: B)
    : dom_mor (coerce_subst_ty s f) · PullbackPr2 _
      =
      PullbackPr2 _.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.

  Proposition finlim_to_comp_cat_subst_tm_pullback_pr1
              {Γ Δ : finlim_to_comp_cat C}
              (s : Γ --> Δ)
              {A : ty Δ}
              (t : tm Δ A)
    : t [[ s ]]tm · PullbackPr1 _
      =
      s · t.
  Proof.
    apply (PullbackArrow_PullbackPr1 (comp_cat_pullback A s)).
  Qed.

  Proposition finlim_to_comp_cat_subst_ty_coe_pr1
              {Γ Δ Δ' : finlim_to_comp_cat C}
              (s : Γ --> Δ)
              {A : ty Δ}
              {B : ty Δ'}
              (f : z_iso Δ Δ')
              (ff : z_iso_disp f A B)
    : dom_mor (subst_ty_coe s f ff) · PullbackPr1 _
      =
      PullbackPr1 _ · pr11 ff.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_subst_ty_coe_pr2
              {Γ Δ Δ' : finlim_to_comp_cat C}
              (s : Γ --> Δ)
              {A : ty Δ}
              {B : ty Δ'}
              (f : z_iso Δ Δ')
              (ff : z_iso_disp f A B)
    : dom_mor (subst_ty_coe s f ff) · PullbackPr2 _
      =
      PullbackPr2 _.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.

  Proposition finlim_to_comp_cat_comp_mor
              {Γ : finlim_to_comp_cat C}
              {A B : ty Γ}
              (s : A -->[ identity _ ] B)
    : comp_cat_comp_mor s = dom_mor s.
  Proof.
    apply idpath.
  Qed.

  Definition univ_cat_with_finlim_comprehension_functor
             {Γ Δ : C}
             {s : Γ --> Δ}
             {A : disp_codomain C Γ}
             {B : disp_codomain C Δ}
             (f : A -->[ s ] B)
    : comprehension_functor_mor (finlim_comprehension C) f
      =
      pr1 f.
  Proof.
    apply idpath.
  Qed.

  Proposition finlim_comp_cat_comp_mor_over
              {Γ Δ : finlim_to_comp_cat C}
              (s : Γ --> Δ)
              {A : ty Γ}
              {B : ty Δ}
              (f : A <: B [[ s ]])
    : comp_cat_comp_mor_over s f
      =
      dom_mor f · PullbackPr1 _.
  Proof.
    apply idpath.
  Qed.
End FinLimCompCatCalculation.

(** * 2. Operations on functors between categories with finite limits *)
Section FinLimCompCatFunctorCalculation.
  Context {C₁ C₂ : univ_cat_with_finlim}
          (F : functor_finlim C₁ C₂).

  Proposition finlim_to_comp_cat_functor_subst_ty_coe_pr1
              {Γ₁ Γ₂ : finlim_to_comp_cat C₁}
              (s : Γ₁ --> Γ₂)
              (A : ty Γ₂)
    : dom_mor (comp_cat_functor_subst_ty_coe (finlim_to_comp_cat_functor F) s A)
      · PullbackPr1 _
      =
      #F (PullbackPr1 _).
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_functor_subst_ty_coe_pr2
              {Γ₁ Γ₂ : finlim_to_comp_cat C₁}
              (s : Γ₁ --> Γ₂)
              (A : ty Γ₂)
    : dom_mor (comp_cat_functor_subst_ty_coe (finlim_to_comp_cat_functor F) s A)
      · PullbackPr2 _
      =
      #F (PullbackPr2 _).
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.

  Proposition finlim_to_comp_cat_functor_coerce
              {Γ : finlim_to_comp_cat C₁}
              {A B : ty Γ}
              (f : A <: B)
    : dom_mor (comp_cat_functor_coerce (finlim_to_comp_cat_functor F) f)
      =
      #F (dom_mor f).
  Proof.
    apply transportf_cod_disp.
  Qed.

  Proposition finlim_to_comprehension_nat_trans_mor
              {Γ : finlim_to_comp_cat C₁}
              (A : ty Γ)
    : comprehension_nat_trans_mor
        (comp_cat_functor_comprehension
           (finlim_to_comp_cat_functor F))
        A
      =
      identity _.
  Proof.
    apply idpath.
  Qed.
End FinLimCompCatFunctorCalculation.

(** * 3. Operations on natural transformations *)
Section FinLimCompCatNatTransCalculation.
  Context {C₁ C₂ : univ_cat_with_finlim}
          {F G : functor_finlim C₁ C₂}
          (τ : nat_trans_finlim F G)
          {Γ : finlim_to_dfl_comp_cat C₁}
          (A : ty Γ).

  Proposition finlim_to_comp_cat_fib_nat_trans_pr1
    : dom_mor (comp_cat_type_fib_nat_trans (finlim_to_dfl_comp_cat_nat_trans τ) A)
      · PullbackPr1 _
      =
      τ (cod_dom A).
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_fib_nat_trans_pr2
    : dom_mor (comp_cat_type_fib_nat_trans (finlim_to_dfl_comp_cat_nat_trans τ) A)
      · PullbackPr2 _
      =
      #F (cod_mor A).
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.
End FinLimCompCatNatTransCalculation.
