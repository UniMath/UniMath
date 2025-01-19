(******************************************************************************************

 The domain functor of the slice category

 In this file, we define the domain functor of the slice category and we show that it is
 a left adjoint if the category has products.

 Contents
 1. The domain functor
 2. The domain functor is a left adjoint

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Limits.BinProducts.

Local Open Scope cat.

(** * 1. The domain functor *)
Definition slice_dom_data
           {C : category}
           (x : C)
  : functor_data (C/x) C.
Proof.
  use make_functor_data.
  - exact (λ zf, cod_dom zf).
  - exact (λ _ _ hp, dom_mor hp).
Defined.

Proposition slice_dom_laws
            {C : category}
            (x : C)
  : is_functor (slice_dom_data x).
Proof.
  split ; intro ; intros ; simpl.
  - apply idpath.
  - apply comp_in_cod_fib.
Qed.

Definition slice_dom
           {C : category}
           (x : C)
  : (C/x) ⟶ C.
Proof.
  use make_functor.
  - exact (slice_dom_data x).
  - exact (slice_dom_laws x).
Defined.

(** * 2. The domain functor is a left adjoint *)
Section DomainLeftAdjoint.
  Context {C : category}
          (BP : BinProducts C)
          {x z : C}
          (yf : C/x)
          (g : slice_dom x yf --> z).

  Proposition is_left_adjoint_slice_dom_unique
    : isaprop
        (∑ (f' : yf --> pr_cod_fib BP x z),
         g
         =
         # (slice_dom x) f' · BinProductPr2 C (BP x z)).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply homset_property | ].
    use eq_mor_cod_fib.
    use BinProductArrowsEq.
    - exact (mor_eq (pr1 φ₁) @ !(mor_eq (pr1 φ₂))).
    - exact (!(pr2 φ₁) @ pr2 φ₂).
  Qed.

  Definition is_left_adjoint_slice_dom_mor
    : yf --> pr_cod_fib BP x z.
  Proof.
    use make_cod_fib_mor.
    - use BinProductArrow.
      + apply cod_mor.
      + exact g.
    - abstract
        (cbn ;
         rewrite BinProductPr1Commutes ;
         apply idpath).
  Defined.

  Proposition is_left_adjoint_slice_dom_comm
    : g
      =
      dom_mor is_left_adjoint_slice_dom_mor · BinProductPr2 C (BP x z).
  Proof.
    cbn.
    rewrite BinProductPr2Commutes.
    apply idpath.
  Qed.
End DomainLeftAdjoint.

Definition is_left_adjoint_slice_dom
           {C : category}
           (BP : BinProducts C)
           (x : C)
  : is_left_adjoint (slice_dom x).
Proof.
  use left_adjoint_from_partial.
  - exact (λ z, pr_cod_fib BP x z).
  - exact (λ z, BinProductPr2 _ (BP x z)).
  - intros z yf g.
    use iscontraprop1.
    + apply is_left_adjoint_slice_dom_unique.
    + simple refine (_ ,, _).
      * exact (is_left_adjoint_slice_dom_mor BP yf g).
      * apply is_left_adjoint_slice_dom_comm.
Defined.
