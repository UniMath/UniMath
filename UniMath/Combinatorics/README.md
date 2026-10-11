Combinatorics
============

This package treats various combinatorial notions not depending on algebra.

Overview of contents
====================

## MetricTree.v

Definition of a metric tree as a set with a metric on it and another property.
The definition is incomplete, in the sense that if edges are added connecting
pairs of points at distance 1, one may not get a tree; example: 4 equally
spaced points on a circle.  Nevertheless, the definition includes enough to
support "tree induction".

