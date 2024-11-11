(**************************************************************************************************

  Sieves

  A sieve on X is a collection of morphisms to X, that is closed under precomposition. It is
  formalized as a subobject of the Yoneda embedding of X. In other words, it consists of
  a presheaf F, together with a monomorphism F ⟹ yoneda X. Note that here, a monomorphism is a
  pointwise injective natural transformation. The `selected` morphisms from Y to X are then the
  images under this transformation of the elements of F Y.
  Now, given a morphism h: Y → X, we can use the Yoneda embedding よ(h) of h to pull back a sieve
  (F, f) on X to a sieve (G, g) on Y, given by the following diagram.
     G --------> F
     |           |
     g           f
     |           |
     v    よ(h)   v
    よ(Y) -----> よ(X)
  This works because pullback preserves monomorphisms. Note that G Z consists of all morphisms Z → Y
  such that postcomposition with h gives an element of F Z.
  This file defines sieves, together with accessors for the functor and natural transformation, as
  well as pullback of sieves. It also defines `selected morphisms` (consisting of an object Y,
  together with an element y : F Y) with a constructor and some accessors.

  Contents
  1. Sieves [sieve]
  2. Pullback of sieves [sieve_pullback]
  3. Selected morphisms [sieve_selected_morphism]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

Section Sieves.

  Context {C : category}.

(** * 1. Sieves *)

  Definition sieve (c : C) : UU :=
    Subobjectscategory (yoneda C c).

  Section Accessors.

    Context {c : C}.

    Definition sieve_functor (S : sieve c)
      : C^op ⟶ HSET
      := Subobject_dom S.

    Definition sieve_nat_trans (S : sieve c) :
      sieve_functor S ⟹ yoneda_objects C c
      := Subobject_mor S.

  End Accessors.

(** * 2. Pullback of sieves *)

  Definition sieve_pullback
    {X Y : C}
    (f : Y --> X)
    (S : sieve X)
    : sieve Y
    := PullbackSubobject Pullbacks_PreShv S (# (yoneda C) f).

(** * 3. Selected morphisms *)

  Section SelectedMorphisms.

    Context {c : C}.

    Definition sieve_selected_morphism
      (S : sieve c)
      := ∑ (d : C), (sieve_functor S d : hSet).

    Definition make_sieve_selected_morphism
      {S : sieve c}
      (d : C)
      (f : (sieve_functor S d : hSet))
      : sieve_selected_morphism S
      := d ,, f.

    Section Accessors.

      Context {S : sieve c}.
      Context (f : sieve_selected_morphism S).

      Definition sieve_selected_morphism_domain
        : C
        := pr1 f.

      Definition sieve_selected_morphism_preimage
        : (sieve_functor S sieve_selected_morphism_domain : hSet)
        := pr2 f.

      Definition sieve_selected_morphism_morphism
        : C⟦sieve_selected_morphism_domain, c⟧
        := sieve_nat_trans S _ sieve_selected_morphism_preimage.

      Definition sieve_selected_morphism_compose
        {d : C}
        (g : C⟦d, sieve_selected_morphism_domain⟧)
        : sieve_selected_morphism S
        := d ,, # (sieve_functor S) g (pr2 f).

    End Accessors.

  End SelectedMorphisms.

  Definition maximal_sieve
    (X : C)
    : sieve X
    := Subobjectscategory_ob
      (identity (yoneda C X))
      (identity_isMonic _).

End Sieves.

Coercion sieve_selected_morphism_morphism : sieve_selected_morphism >-> precategory_morphisms.
