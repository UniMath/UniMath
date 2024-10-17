Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.yoneda.

Local Open Scope cat.

Section Sieves.

  Context {C : category}.

  (** A sieve on c is a subobject of the yoneda functor. *)
  Definition sieve (c : C) : UU :=
    Subobjectscategory (yoneda C c).

  Context {c : C}.

  Definition sieve_functor (S : sieve c)
    : C^op ⟶ HSET
    := Subobject_dom S.

  Definition sieve_nat_trans (S : sieve c) :
    sieve_functor S ⟹ yoneda_objects C c
    := Subobject_mor S.

  Definition sieve_selected_morphism (S : sieve c)
    := ∑ (d : C), (sieve_functor S d : hSet).

  Context {S : sieve c}.

  Definition make_sieve_selected_morphism
    (d : C)
    (f : (sieve_functor S d : hSet))
    : sieve_selected_morphism S
    := d ,, f.

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

End Sieves.

Coercion sieve_selected_morphism_morphism : sieve_selected_morphism >-> precategory_morphisms.
