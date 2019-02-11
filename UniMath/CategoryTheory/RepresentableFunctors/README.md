Representable Functors
======================

In this subdirectory is a unified approach to the notions of category theory
satisfying universal properties via representable functors.  The idea is that
uniqueness up to isomorphism of two objects satisfying the same universal
property should always be drawn as a direct corollary of the uniqueness of
representations of a representable functor.

These files were originally in the Ktheory package and were written by Dan
Grayson.

Overview of contents
====================

## Precategories.v

easy lemmas about precategories, could be moved up

## Representation.v

Representation.Data is a representation of a functor C ==> Set.  This is used
in other files for defining various limits and colimits.

## Magma.v

Construction of the product of a family of sets with a binary operation (magmas).

## Monoid.v

The zero monoid is a zero object.  Construction of monoids by generators and
relations.  Construction of free monoids.  Construction of a product of
monoids.

## AbelianMonoid.v

The zero abelian monoid is a zero object.  Construction of abelian monoids by
generators and relations.  Construction of free abelian monoids.  Construction
of a product of abelian monoids.  Forthcoming: the sum of a finite family of
elements.

## Group.v

The zero group is a zero object.  Construction of groups by generators and
relations.  Construction of free groups.  Construction of a product of groups.

## GroupAction.v

Generalities about groups G acting on sets, including the structure identity
principle.  Definition of torsor.  Definition of BG and its covering space EG.
Proof (using univalence) that the loop space of BG is G.

## AbelianGroup.v

The zero abelian group is a zero object.  Construction of abelian groups by
generators and relations.  Construction of free abelian groups.  Construction
of products and sums of abelian groups.  The category of abelian groups, with
abstract products and sums.  This will be the basis for our first example of an
exact category in the sense of Quillen.
