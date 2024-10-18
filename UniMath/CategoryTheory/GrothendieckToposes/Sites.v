(**************************************************************************************************

  Grothendieck Sites

  A Grothendieck site is a category with a Grothendieck topology. This marks, for every X, some
  sieves on X (collections of morphisms into X) as `covering sieves`. This file defines sites and
  covering sieves for a site, together with constructors and accessors.

  Contents
  1. Sites [site]
  2. Covering sieves [covering_sieve]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Topologies.

Local Open Scope cat.

(** * 1. Sites *)

Definition site
  : UU
  := ∑ C, Grothendieck_topology C.

Definition make_site
  (C : category)
  (GT : Grothendieck_topology C)
  : site
  := C ,, GT.

Coercion site_category
  (C : site)
  : category
  := pr1 C.

Section Accessors.

  Context (C : site).

  Definition site_topology
    : Grothendieck_topology C
    := pr2 C.

  Definition site_maximal_sieve
    (X : C)
    : site_topology X (maximal_sieve X)
    := Grothendieck_topology_maximal_sieve _ _.

  Definition site_stability
    {X Y : C}
    (f : Y --> X)
    {S : sieve X}
    (H : site_topology X S)
    : site_topology Y (sieve_pullback f S)
    := Grothendieck_topology_stability _ _ _ _ _ H.

  Definition site_transitivity
    {X : C}
    {S : sieve X}
    (H : ∏ (Y : C) (f : Y --> X), site_topology Y (sieve_pullback f S))
    : site_topology X S
    := Grothendieck_topology_transitivity _ _ _ H.

End Accessors.

(** * 2. Covering sieves *)

Section CoveringSieves.

  Context {C : site}.
  Context {X : C}.

  Definition covering_sieve
    : UU
    := site_topology C X.

  Definition make_covering_sieve
    (S : sieve X)
    (H : site_topology C X S)
    : covering_sieve
    := make_carrier _ S H.

  Coercion covering_sieve_sieve
    (S : covering_sieve)
    : sieve X
    := pr1carrier _ S.

  Definition covering_sieve_is_covering
    (S : covering_sieve)
    : site_topology C X S
    := pr2 S.

End CoveringSieves.

Arguments covering_sieve : clear implicits.
Arguments covering_sieve {C}.
