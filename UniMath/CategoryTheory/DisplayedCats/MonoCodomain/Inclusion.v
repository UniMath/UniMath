(**************************************************************************************

 The inclusion of monomorphisms into morphisms

 We construct the displayed functor over the identity from the displayed category of
 monomorphisms to the displayed category of morphisms, and we instantiate it to obtain
 fiber functors.

 Content
 1. The displayed functor
 2. The fiber functor

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

Section Inclusion.
  Context (C : category).

  (** * 1. The displayed functor *)
  Definition mono_cod_to_cod_data
    : disp_functor_data
        (functor_identity C)
        (disp_mono_codomain C)
        (disp_codomain C).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x m, pr1 m ,, pr12 m).
    - exact (λ x y mx my f ff, ff).
  Defined.

  Proposition mono_cod_to_cod_axioms
    : disp_functor_axioms mono_cod_to_cod_data.
  Proof.
    split ; intro ; intros ; use eq_cod_mor ; cbn.
    - apply idpath.
    - apply idpath.
  Qed.

  Definition mono_cod_to_cod
    : disp_functor
        (functor_identity C)
        (disp_mono_codomain C)
        (disp_codomain C)
    := mono_cod_to_cod_data
       ,,
       mono_cod_to_cod_axioms.
End Inclusion.

(** * 2. The fiber functor *)
Definition mono_cod_to_cod_fib
           {C : category}
           (x : C)
  : (C /m x) ⟶ (C / x)
  := fiber_functor (mono_cod_to_cod C) x.

Proposition mono_cod_fiber_functor_on_mor
            {C : category}
            (HC : Pullbacks C)
            {x y : C}
            (f : x --> y)
            {zg₁ zg₂ : C /m y}
            (gp : zg₁ --> zg₂)
  : #(mono_cod_pb HC f) gp
    =
    #(cod_pb HC f) (#(mono_cod_to_cod_fib _) gp).
Proof.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  rewrite cod_fiber_functor_on_mor.
  use (MorphismsIntoPullbackEqual
         (isPullback_Pullback (HC y (pr1 zg₂) x (pr2 zg₂) f))) ; cbn.
  - rewrite !PullbackArrow_PullbackPr1.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (HC y (pr1 zg₂) x (pr2 zg₂) f)).
    }
    rewrite transportf_mono_cod_disp.
    cbn.
    apply idpath.
  - rewrite !PullbackArrow_PullbackPr2.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (HC y (pr1 zg₂) x (pr2 zg₂) f)).
    }
    apply id_right.
Qed.
