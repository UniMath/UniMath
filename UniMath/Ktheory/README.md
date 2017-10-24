Ktheory
=======

Author: Daniel R. Grayson <dan@math.uiuc.edu>

This package aims to formalize theorems of higher algebraic K-theory.

We start by introducing the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

We are working toward definitions of "additive category" and "abelian
category" as properties of a category, rather than as an added structure.
That is the approach of Mac Lane in sections 18, 19, and 21 of
[Duality for groups](http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.bams/1183515045),
Bull. Amer. Math. Soc., Volume 56, Number 6 (1950), 485-516.

For the definition of the notion of exact category, the following reference
might be useful: 
      Bühler, Theo, Exact categories, Expo. Math. 28 (2010), no. 1, 1–69.

Acknowledgments
===============

I thank the Oswald Veblen Fund and the Bell Companies Fellowship for supporting
my stay at the Institute for Advanced Study in Fall, 2013, and in Spring, 2014,
where I started writing this code.

I thank The Ambrose Monell Foundation for supporting my stay at the Institute
for Advanced Study in Fall, 2015, where I continued working on this code.

I thank the Oswald Veblen Fund and the Friends of the Institute for Advanced
Study for supporting my stay at the Institute for Advanced Study in Spring,
2017, where I continued working on this code.

Overview of contents
====================

## Integers.v

more lemmas about integers; could be added to Foundations

## Tactics.v

a few tactics for helping with proofs

## Utilities.v

lemmas about paths, hlevel, and logic

## Equivalences.v

the proof that an equivalence, defined as a pair of maps with a pair of
homotopies and an adjointness relation, is invertible.

## Interval.v

the (easy) proof that squashing a two-element set yields an interval

## Precategories.v

easy lemmas about precategories, could be moved to RezkCompletion

## Primitive.v

terminal and initial objects in categories, directly

## ZeroObject.v

Zero objects and zero maps in precategories.

## StandardCategories.v

simple examples of categories, including the path groupoid of a type of h-level
3, and the discrete category with n objects

## Elements.v

Elements.cat is the category of elements associated to a functor C ==> Set.

## Representation.v

Representation.Data is a representation of a functor C ==> Set.  This is used
in other files for defining various limits and colimits.

## Sets.v

products of sets

## FiniteSet.v

FiniteSet.Data is the type of finite sets

## TerminalObject.v

initial and terminal objects, this time, by representability of functors

## HomFamily.v

Given a family of objects in a precategory, construct the product of the
functors the objects represent.  (Representing it will amount to finding the
product of the objects.)

## Product.v

Product.type : the product of a family of objects in a precategory.

## Sum.v

Product.type : the sum (coproduct) of a family of objects in a precategory.

## RawMatrix.v

The matrix of a map from a sum to a product in a precategory.

## DirectSum.v

Definition of direct sum of a family of objects in a precategory indexed by a
decidable set.  (Decidability is needed to construct the identity matrix.)

## Kernel.v

Definition of kernels and cokernels of maps in precategories that have a zero
object.

## Magma.v

Construction of the product of a family of sets with a binary operation (magmas).

## QuotientSet.v

Some lemmas about quotient sets.  Could be moved to Foundations.

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

## MetricTree.v

Definition of a metric tree as a set with a metric on it and another property.
The definition is incomplete, in the sense that if edges are added connecting
pairs of points at distance 1, one may not get a tree; example: 4 equally
spaced points on a circle.  Nevertheless, the definition includes enough to
support "tree induction".

## Nat.v

Various lemmas about natural numbers that could be moved to Foundations.
Proof that "nat" is a metric tree.

## Halfline.v

Construction of the "half line" by squashing nat.  A Map from it to another
type is determined by a sequence of points connected by paths.  The techniques
are a warm-up for the construction of the circle.

## GroupAction.v

Generalities about groups G acting on sets, including the structure identity
principle.  Definition of torsor.  Definition of BG and its covering space EG.
Proof (using univalence) that the loop space of BG is G.

## AffineLine.v

We show that the propositional truncation of a ℤ-torsor, where ℤ is the
additive group of the integers, behaves like an affine line.  It's a
contractible type, but maps from it to another type Y are determined by
specifying where the points of T should go, and where the paths joining
consecutive points of T should go.  This forms the basis for the construction
of the circle as a quotient of the affine line.

## Circle.v

Construction of the circle as Bℤ.  A map from it to another type is determined
by a point and a loop.  Forthcoming: the dependent version.

## AbelianGroup.v

The zero abelian group is a zero object.  Construction of abelian groups by
generators and relations.  Construction of free abelian groups.  Construction
of products and sums of abelian groups.  The category of abelian groups, with
abstract products and sums.  This will be the basis for our first example of an
exact category in the sense of Quillen.
