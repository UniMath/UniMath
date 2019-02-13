Synthetic Homotopy Theory
=========================

In this package we collect a few results about synthetic homotopy theory.  The
main one is the construction of the circle as the type of torsors over the
group of integers and the proof of its induction principle.

The files were written by Daniel Grayson.

Overview of contents
====================

## Halfline.v

Construction of the "half line" by squashing nat.  A Map from it to another
type is determined by a sequence of points connected by paths.  The techniques
are a warm-up for the construction of the circle.

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
