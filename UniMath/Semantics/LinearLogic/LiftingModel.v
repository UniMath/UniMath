(****************************************************************************

 Linear category from the lifting operation on posets

 We construct an example of a linear category coming from lifting posets.

 ****************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.PointedPosetStrict.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SmashProductMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Examples.PosetsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Examples.LiftPoset.
Require Import UniMath.Semantics.LinearLogic.LinearCategory.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Definition lifting_linear_category_data
  : linear_category_data.
Proof.
  use make_linear_category_data.
  - exact pointed_poset_sym_mon_closed_cat.
  - exact lift_poset_symmetric_monoidal_comonad.
  - exact lift_poset_comult.
  - exact lift_poset_counit.
Defined.

Proposition lifting_linear_category_laws
  : linear_category_laws lifting_linear_category_data.
Proof.
  repeat split.
  - intros X Y f.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
  - intros X Y f.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | t ].
    + cbn ; apply idpath.
    + induction t.
      cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    intro x ; cbn in x.
    induction x as [ x | ].
    + cbn ; apply idpath.
    + cbn ; apply idpath.
Qed.

Definition lifting_linear_category
  : linear_category.
Proof.
  use make_linear_category.
  - exact lifting_linear_category_data.
  - exact lifting_linear_category_laws.
Defined.
