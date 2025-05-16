(***************************************************************************************

 Fiberwise exponentials

 In this file, we define when a fibration is fiberwise Cartesian closed. Concretely, this
 means that every fiber category is Cartesian closed and that the substitution functor
 preserves exponentials. We also give a specialized builder for the case that the
 fibration lands in partial orders. Finally, we prove that binary products distribute over
 binary coproducts for fiberwise Cartesian closed fibrations.

 Content
 1. Fiberwise exponentials
 2, Accessors
 3. Specialized builder for fibrations that land in posets
 4. Distributivity of products and coproducts

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.exponentials.

Local Open Scope cat.

(** * 1. Fiberwise exponentials *)
Definition fiberwise_exponentials
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           (PC : fiberwise_binproducts HD)
  : UU
  := ∑ (E : ∏ (x : C), Exponentials (pr1 PC x)),
     ∏ (x y : C)
       (f : x --> y),
     preserves_exponentials (E y) (E x) (preserves_binproduct_in_fib PC f).

(** * 2, Accessors *)
Definition exp_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {P : fiberwise_binproducts HD}
           (E : fiberwise_exponentials P)
           {x : C}
           (xx yy : D x)
  : D x
  := exp (pr1 E x xx) yy.

Definition eval_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {P : fiberwise_binproducts HD}
           (E : fiberwise_exponentials P)
           {x : C}
           (xx yy : D[{x}])
  : binprod_in_fib P xx (exp_in_fib E xx yy) --> yy
  := exp_eval (pr1 E x xx) yy.

Definition lam_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {P : fiberwise_binproducts HD}
           (E : fiberwise_exponentials P)
           {x : C}
           {xx yy zz : D[{x}]}
           (ff : binprod_in_fib P yy xx --> zz)
  : xx --> exp_in_fib E yy zz
  := exp_lam (pr1 E x _) ff.

Definition preserves_exponentials_in_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {P : fiberwise_binproducts HD}
           (E : fiberwise_exponentials P)
           {x y : C}
           (f : x --> y)
  : preserves_exponentials (pr1 E y) (pr1 E x) (preserves_binproduct_in_fib P f)
  := pr2 E x y f.

(** * 3. Specialized builder for fibrations that land in posets *)
Section FiberwiseExponentialsPoset.
  Context {C : category}
          {D : disp_cat C}
          {HD : cleaving D}
          (HD' : locally_propositional D)
          (P : fiberwise_binproducts HD)
          (imp : ∏ (Γ : C), D[{Γ}] → D[{Γ}] → D[{Γ}])
          (imp_e : ∏ (Γ : C) (φ ψ : D[{Γ}]),
                   binprod_in_fib P φ (imp _ φ ψ) --> ψ)
          (imp_i : ∏ (Γ : C)
                     (φ ψ χ : D[{Γ}])
                     (p : binprod_in_fib P φ χ --> ψ),
                   χ --> imp Γ φ ψ)
          (imp_sub : ∏ (Γ₁ Γ₂ : C)
                       (s : Γ₁ --> Γ₂)
                       (φ ψ : D[{Γ₂}]),
                     imp _ (pr1 (HD Γ₂ Γ₁ s φ)) (pr1 (HD Γ₂ Γ₁ s ψ))
                     -->
                     pr1 (HD Γ₂ Γ₁ s (imp _ φ ψ))).

  Definition exp_in_fiber_locally_propositional
             (Γ : C)
    : Exponentials (pr1 P Γ).
  Proof.
    intro φ.
    apply coreflections_to_is_left_adjoint.
    intro ψ.
    use make_coreflection.
    - use make_coreflection_data.
      + exact (imp _ φ ψ).
      + exact (imp_e _ φ ψ).
    - intro p.
      use make_coreflection_arrow.
      + apply imp_i.
        exact p.
      + abstract apply HD'.
      + abstract (
          intros g' Hg';
          apply HD'
        ).
  Defined.

  Definition make_fiberwise_exponentials_locally_propositional
    : fiberwise_exponentials P.
  Proof.
    simple refine (_ ,, _).
    - exact exp_in_fiber_locally_propositional.
    - abstract
        (intros Γ₁ Γ₂ s φ ψ ;
         use make_is_z_isomorphism ; [ apply imp_sub | ] ;
         split ; apply HD').
  Defined.
End FiberwiseExponentialsPoset.

(** * 4. Distributivity of products and coproducts *)
Definition preserves_bincoproduct_constprod_fib
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {P : fiberwise_binproducts HD}
           (E : fiberwise_exponentials P)
           {x : C}
           (xx : D[{x}])
  : preserves_bincoproduct (constprod_functor1 (pr1 P x) xx)
  := left_adjoint_preserves_bincoproduct _ (pr1 E x xx).

Definition distributivity_fiberwise_exponentials
           {C : category}
           {D : disp_cat C}
           {HD : cleaving D}
           {P : fiberwise_binproducts HD}
           (CP : fiberwise_bincoproducts HD)
           (E : fiberwise_exponentials P)
           {x : C}
           (xx yy zz : D[{x}])
  : z_iso
      (preserves_bincoproduct_to_bincoproduct
         (constprod_functor1 (pr1 P x) xx)
         (preserves_bincoproduct_constprod_fib E xx)
         (bincoprod_in_fib CP yy zz))
      (bincoprod_in_fib
         CP
         (BinProductObject _ (binprod_in_fib P xx yy))
         (BinProductObject _ (binprod_in_fib P xx zz))).
Proof.
  exact (preserves_bincoproduct_to_z_iso
           _
           (preserves_bincoproduct_constprod_fib E xx)
           (bincoprod_in_fib CP yy zz)
           (bincoprod_in_fib
              CP
              (BinProductObject _ (binprod_in_fib P xx yy))
              (BinProductObject _ (binprod_in_fib P xx zz)))).
Defined.
