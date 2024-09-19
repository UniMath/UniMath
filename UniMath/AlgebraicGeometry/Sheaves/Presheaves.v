Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.Topology.Topology.

Require Import UniMath.AlgebraicGeometry.CategoryOfOpens.

Local Open Scope cat.

Definition presheaf
  (C : category)
  (X : TopologicalSpace)
  : UU
  := (opens_cat X)^op ⟶ C.

Coercion presheaf_to_functor
  {C : category}
  {X : TopologicalSpace}
  (P : presheaf C X)
  : (opens_cat X)^op ⟶ C
  := P.

Definition presheaf_morphism
  {C : category}
  {X : TopologicalSpace}
  (P Q : presheaf C X)
  : UU
  := P ⟹ Q.

Coercion presheaf_morphism_to_nat_trans
  {C : category}
  {X : TopologicalSpace}
  {P Q : presheaf C X}
  (f : presheaf_morphism P Q)
  : P ⟹ Q
  := f.

Definition presheaf_pushforward
  {C : category}
  {X Y : TopologicalSpace}
  (f : continuous_function X Y)
  (P : presheaf C X)
  : presheaf C Y
  := (functor_opp (opens_cat $ f) ∙ P).

Notation "f _* P" := (presheaf_pushforward f P) (at level 100).
