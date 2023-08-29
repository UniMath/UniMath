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
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Definition lifting_linear_category_data
  : linear_category_data.
Proof.
  use make_linear_category_data.
  - exact pointed_poset_sym_mon_closed_cat.
  - exact lift_poset_symmetric_monoidal_comonad.
  - exact (λ X, lift_poset_comult X).
  - exact (λ X, lift_poset_counit X).
Defined.

Proposition lifting_linear_category_laws
  : linear_category_laws lifting_linear_category_data.
Proof.
  repeat split.
  - intros X Y f.
    exact (nat_trans_ax lift_poset_comult X Y f).
  - intros X Y f.
    refine (nat_trans_ax lift_poset_counit X Y f @ _).
    apply id_right.
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
    rewrite <-tensor_mor_left. rewrite <-tensor_mor_right.
    apply pathsinv0, (comonoid_to_law_assoc _ (lift_commutative_comonoid X)).
  - intros X.
    rewrite <-tensor_mor_right.
    etrans.
    2: { apply (comonoid_to_law_unit_left _ (lift_commutative_comonoid X)). }
    apply idpath.
  - intros X.
    apply (commutative_comonoid_is_commutative _ (lift_commutative_comonoid X)).
  - intros X Y.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ x y ].
    induction x as [ x | ], y as [ y | ] ; simpl ; apply idpath.
  - use eq_mor_hset_struct.
    intro x.
    induction x as [ | ].
    + cbn.
      apply idpath.
    + use iscompsetquotpr ; cbn.
      refine (hinhpr (inr _)).
      split.
      * unfold product_point_coordinate ; cbn.
        exact (inl (idpath _)).
      * unfold product_point_coordinate ; cbn.
        exact (inr (idpath _)).
  - intros X Y.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ x y ].
    induction x as [ x | ], y as [ y | ] ; cbn.
    + apply idpath.
    + apply idpath.
    + apply idpath.
    + apply idpath.
  - use eq_mor_hset_struct.
    intro x.
    induction x as [ | ] ; cbn.
    + apply idpath.
    + apply idpath.
Qed.

Definition lifting_linear_category
  : linear_category.
Proof.
  use make_linear_category.
  - exact lifting_linear_category_data.
  - exact lifting_linear_category_laws.
Defined.
