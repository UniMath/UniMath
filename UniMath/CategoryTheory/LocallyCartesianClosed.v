(*********************************************************************************************

 Locally cartesian closed categories

 In this file, we define locally cartesian closed categories. There are multiple equivalent
 definitions for locally cartesian closed categories:
 1. The first definition says that a category is locally cartesian closed categories if each
    of its slice category is cartesian closed.
 2. The second definition says that a category is locally cartesian closed if the pullback
    functor has a right adjoint.
 Note that for both definitions we need to assume that the involved category has pullbacks.
 We use the second definition.

 From the perspective of dependent type theory, we can interpret these definitions. Suppose
 that `C` is a finitely complete category. In `C`, we can thus interpret dependent type
 theory with `∑`-types, product types, unit types, and extensional identity types (using the
 codomain fibration). The first definition says that `C` has function types, whereas the
 second definition says that `C` has dependent products. Using this interpretation, we can
 also understand why these two variations are equivalent: dependent functions from `X` to a
 type family `Y` over `X` are the same as ordinary functions from `X` to `∑ (x : X), Y x` for
 which the composition with the first projection is the identity.

 We use the second variation of the definition in this file, because in dependent type theory,
 usually dependent products are used as the basic type former rather than function types.

 Contents
 1. Locally cartesian closed categories
 2. The slices of locally cartesian closed categories are cartesian closed

 *********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Examples.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodDomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.

(** * 1. Locally cartesian closed categories *)
Definition is_locally_cartesian_closed
           {C : category}
           (PB : Pullbacks C)
  : UU
  := ∏ (x y : C)
       (f : x --> y),
     is_left_adjoint (cod_pb PB f).

(** * 2. The slices of locally cartesian closed categories are cartesian closed *)
Definition locally_cartesian_closed_to_exponentials_nat_trans_data
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (BP := codomain_fib_binproducts PB x)
           (yf : C/x)
  : nat_trans_data
      (cod_pb PB (cod_mor yf) ∙ comp_functor (cod_mor yf))
      (constprod_functor1 BP yf).
Proof.
  intros zg.
  use make_cod_fib_mor.
  - apply (swap_pullback_z_iso (cod_mor zg) (cod_mor yf)).
  - abstract
      (cbn ;
       unfold swap_pullback_mor ;
       rewrite !assoc ;
       rewrite PullbackArrow_PullbackPr1 ;
       apply idpath).
Defined.

Definition slice_constprod_functor1_mor
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (BP := codomain_fib_binproducts PB x)
           (yf : C/x)
           {zg₁ zg₂ : C/x}
           (hp : zg₁ --> zg₂)
  : cod_dom (constprod_functor1 BP yf zg₁)
    -->
    cod_dom (constprod_functor1 BP yf zg₂).
Proof.
  use PullbackArrow.
  - apply PullbackPr1.
  - exact (PullbackPr2 _ · dom_mor hp).
  - abstract
      (cbn ;
       refine (PullbackSqrCommutes _ @ _) ;
       rewrite !assoc' ;
       rewrite (mor_eq hp) ;
       apply idpath).
Defined.

Proposition slice_constprod_functor1_mor_eq
            {C : category}
            (PB : Pullbacks C)
            {x : C}
            (BP := codomain_fib_binproducts PB x)
            (yf : C/x)
            {zg₁ zg₂ : C/x}
            (hp : zg₁ --> zg₂)
  : dom_mor (#(constprod_functor1 BP yf) hp)
    =
    slice_constprod_functor1_mor PB yf hp.
Proof.
  unfold slice_constprod_functor1_mor.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - rewrite PullbackArrow_PullbackPr1.
    etrans.
    {
      cbn -[fiber_category].
      apply (PullbackArrow_PullbackPr1 (make_Pullback _ (pr22 (PB _ _ _ _ _)))).
    }
    rewrite id_right.
    cbn.
    apply idpath.
  - rewrite PullbackArrow_PullbackPr2.
    etrans.
    {
      cbn -[fiber_category].
      apply (PullbackArrow_PullbackPr2 (make_Pullback _ (pr22 (PB _ _ _ _ _)))).
    }
    rewrite comp_in_cod_fib.
    cbn.
    apply idpath.
Qed.

Proposition locally_cartesian_closed_to_exponentials_nat_trans_laws
            {C : category}
            (PB : Pullbacks C)
            {x : C}
            (BP := codomain_fib_binproducts PB x)
            (yf : C/x)
  : is_nat_trans
      _ _
      (locally_cartesian_closed_to_exponentials_nat_trans_data PB yf).
Proof.
  intros zg₁ zg₂ hp.
  use eq_mor_cod_fib.
  rewrite !comp_in_cod_fib.
  etrans.
  {
    cbn -[cod_pb].
    apply maponpaths_2.
    apply maponpaths.
    apply cod_fiber_functor_on_mor.
  }
  rewrite slice_constprod_functor1_mor_eq.
  cbn ; unfold swap_pullback_mor, slice_constprod_functor1_mor.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
  - rewrite !assoc'.
    rewrite !PullbackArrow_PullbackPr1.
    rewrite PullbackArrow_PullbackPr2.
    apply idpath.
  - rewrite !assoc'.
    rewrite !PullbackArrow_PullbackPr2.
    rewrite PullbackArrow_PullbackPr1.
    rewrite assoc.
    rewrite PullbackArrow_PullbackPr2.
    apply idpath.
Qed.

Definition locally_cartesian_closed_to_exponentials_nat_trans
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (BP := codomain_fib_binproducts PB x)
           (yf : C/x)
  : cod_pb PB (cod_mor yf) ∙ comp_functor (cod_mor yf)
    ⟹
    constprod_functor1 BP yf.
Proof.
  use make_nat_trans.
  - exact (locally_cartesian_closed_to_exponentials_nat_trans_data PB yf).
  - apply locally_cartesian_closed_to_exponentials_nat_trans_laws.
Defined.

Definition locally_cartesian_closed_to_exponentials_nat_z_iso
           {C : category}
           (PB : Pullbacks C)
           {x : C}
           (BP := codomain_fib_binproducts PB x)
           (yf : C/x)
  : nat_z_iso
      (cod_pb PB (cod_mor yf) ∙ comp_functor (cod_mor yf))
      (constprod_functor1 BP yf).
Proof.
  use make_nat_z_iso.
  - apply locally_cartesian_closed_to_exponentials_nat_trans.
  - intro.
    use is_z_iso_fiber_from_is_z_iso_disp.
    use is_z_iso_disp_codomain.
    exact (z_iso_is_z_isomorphism (swap_pullback_z_iso _ _ _ _)).
Defined.

Definition locally_cartesian_closed_to_exponentials
           {C : category}
           (PB : Pullbacks C)
           (HC : is_locally_cartesian_closed PB)
           (x : C)
           (BP := codomain_fib_binproducts PB x)
  : Exponentials BP.
Proof.
  intros yf.
  use is_left_adjoint_nat_z_iso.
  - exact (cod_pb PB (cod_mor yf) ∙ comp_functor (cod_mor yf)).
  - use comp_is_left_adjoint.
    + apply HC.
    + exact (is_left_adjoint_left_adjoint
               (is_right_adjoint_cod_fiber_functor PB (cod_mor yf))).
  - exact (locally_cartesian_closed_to_exponentials_nat_z_iso PB yf).
Defined.
