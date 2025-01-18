(**************************************************************************************

 The fiber of the displayed category of monomorphisms

 Given a category `C` and an object `x`, we have a displayed category of monomorphisms
 into `x`. In this file, we study the fibers of this displayed category. We show that
 the fiber of every object `y` is a preorder. Note that the underlying type of this
 preorder is not necessarily a set.

 Content
 1. Accessors for the fiber of the codomain of monomorphisms
 2. Builders for the fiber of the codomain of monomorphisms
 3. Standard objects and morphisms in the codomain of monomorphisms

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

Definition mono_cod_slice
           {C : category}
           (x : C)
  : category
  := (disp_mono_codomain C)[{x}].

Notation "C '/m' x" := (@mono_cod_slice C x) (at level 40) : cat.

Proposition is_univalent_mono_cod_slice
            {C : univalent_category}
            (x : C)
  : is_univalent (C /m x).
Proof.
  use is_univalent_fiber.
  apply disp_univalent_disp_mono_codomain.
Qed.

Definition mono_cod_pb
           {C : category}
           (HC : Pullbacks C)
           {x y : C}
           (f : x --> y)
           (HD := mono_cod_disp_cleaving HC)
  : (C /m y) ⟶ (C /m x)
  := fiber_functor_from_cleaving _ HD f.

Section MonoCodomainFiber.
  Context {C : category}.

  (** * 1. Accessors for the fiber of the codomain of monomorphisms *)
  Definition mono_cod_dom
             {y : C}
             (f : C /m y)
    : C
    := pr11 f.

  Definition mono_cod_mor
             {y : C}
             (f : C /m y)
    : Monic C (mono_cod_dom f) y
    := make_Monic _ _ (pr2 f).

  Definition mono_dom_mor
             {y : C}
             {f₁ f₂ : C /m y}
             (g : f₁ --> f₂)
    : mono_cod_dom f₁ --> mono_cod_dom f₂
    := pr11 g.

  Proposition mono_mor_eq
              {y : C}
              {f₁ f₂ : C /m y}
              (g : f₁ --> f₂)
    : mono_dom_mor g · mono_cod_mor f₂ = mono_cod_mor f₁.
  Proof.
    exact (pr21 g @ id_right _).
  Qed.

  Proposition eq_mor_mono_cod_fib
              {y : C}
              {f₁ f₂ : C /m y}
              (g₁ g₂ : f₁ --> f₂)
    : g₁ = g₂.
  Proof.
    apply locally_propositional_mono_cod_disp_cat.
  Qed.

  (** * 2. Builders for the fiber of the codomain of monomorphisms *)
  Definition make_mono_cod_fib_ob
             {x y : C}
             (f : Monic C x y)
    : C /m y
    := (x ,, pr1 f) ,, pr2 f.

  Definition make_mono_cod_fib_mor
             {x : C}
             {f₁ f₂ : C /m x}
             (g : mono_cod_dom f₁ --> mono_cod_dom f₂)
             (p : g · mono_cod_mor f₂ = mono_cod_mor f₁)
    : f₁ --> f₂.
  Proof.
    refine ((g ,, _) ,, tt).
    exact (p @ !(id_right _)).
  Defined.

  (** * 3. Standard objects and morphisms in the codomain of monomorphisms *)
  Definition mono_cod_fib_id
             (x : C)
    : C /m x
    := make_mono_cod_fib_ob (identity_Monic C).

  Definition mor_to_mono_cod_fib_id
             {x : C}
             (f : C /m x)
    : f --> mono_cod_fib_id x.
  Proof.
    simple refine (make_mono_cod_fib_mor _ _).
    - exact (mono_cod_mor f).
    - abstract
        (cbn ;
         apply id_right).
  Defined.

  Definition mono_cod_fib_comp
             {x y : C}
             (f : Monic C x y)
             (g : C /m x)
    : C /m y
    := make_mono_cod_fib_ob (Monic_comp _ (mono_cod_mor g) f).
End MonoCodomainFiber.
