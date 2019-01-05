(** * Prelude for category theory *)

(** This re-exports modules that are very frequently needed when doing any kind of
    category theory. This is a matter of taste, but supported empirically by the
    number of files in this package that import these modules individually.
*)

Require Export UniMath.CategoryTheory.Core.Categories.
Require Export UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.Isos.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.
Require Export UniMath.CategoryTheory.Core.Univalence.