(***************************************************************************************

 Monomorphisms in the slice category

 Monomorphisms in the slice category can be characterized as morphisms whose underlying
 morphism is a monomorphism. In this file, we prove this characterization.

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.

Local Open Scope cat.

Definition is_monic_cod_fib
           {C : category}
           {y : C}
           {xf xg : C/y}
           (h : xf --> xg)
           (Hh : isMonic (dom_mor h))
  : isMonic h.
Proof.
  intros k φ ψ p.
  use eq_mor_cod_fib.
  use Hh.
  refine (_ @ maponpaths dom_mor p @ _).
  - rewrite comp_in_cod_fib.
    apply idpath.
  - rewrite comp_in_cod_fib.
    apply idpath.
Qed.

Definition from_is_monic_cod_fib
           {C : category}
           {y : C}
           {xf xg : C/y}
           (h : xf --> xg)
           (Hh : isMonic h)
  : isMonic (dom_mor h).
Proof.
  intros z φ ψ p.
  use (maponpaths
         dom_mor
         (Hh (make_cod_fib_ob (φ · cod_mor xf))
             (make_cod_fib_mor _ _)
             (make_cod_fib_mor _ _) _)).
  - cbn.
    apply idpath.
  - cbn.
    rewrite <- (mor_eq h).
    rewrite !assoc.
    apply maponpaths_2.
    exact (!p).
  - use eq_mor_cod_fib.
    rewrite !comp_in_cod_fib.
    cbn.
    exact p.
Qed.

Definition is_monic_cod_fib_weq
           {C : category}
           {y : C}
           {xf xg : C/y}
           (h : xf --> xg)
  : isMonic h ≃ isMonic (dom_mor h).
Proof.
  use weqimplimpl.
  - exact (from_is_monic_cod_fib h).
  - exact (is_monic_cod_fib h).
  - apply isapropisMonic.
  - apply isapropisMonic.
Defined.
