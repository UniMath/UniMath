(*
   In this file, we show how the (symmetric monoidal) category of commutative comonoids, over a symmetric monoidal category, is cartesian.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.

Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Symmetric.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.MonoidalCartesianBuilder.

Local Open Scope cat.
Import MonoidalNotations.
Import ComonoidNotations.

Section CartesianMonoidalCategoryOfCommutativeComonoids.

  Context (V : sym_monoidal_cat).

  Lemma diagonal_is_comonoid_mor_counit
    (m : comonoid V)
    : is_comonoid_mor_counit V m (tensor_of_comonoids V m m) δ_{m}.
  Proof.
    unfold is_comonoid_mor_counit.
    cbn.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite ! assoc'.
    etrans. {
      apply maponpaths.
      apply maponpaths.
      exact (monoidal_leftunitornat V _ _ ε_{m}).
    }
    refine (_ @ id_left _).
    rewrite ! assoc.
    apply maponpaths_2.
    exact (comonoid_to_law_unit_left _ m).
  Qed.

  Lemma aug_is_comonoid_mor_comult
    (m : comonoid V)
    : is_comonoid_mor_comult V m (comonoid_disp_unit V) ε_{m}.
  Proof.
    refine (assoc _ _ _ @ _).
    etrans. {
      apply maponpaths_2.
      apply comonoid_laws_unit_left'.
    }
    apply monoidal_leftunitorinvnat.
  Qed.

  Definition commutative_comonoid_to_comonoid_of_comonoids_data
    (m : commutative_comonoid V)
    : comonoid_data (symmetric_cat_commutative_comonoids V).
  Proof.
    exists m.
    refine (_ ,, _).
    - refine (δ_{m} ,, (_ ,, tt) ,, tt).
      abstract (split ; cbn;
      [ refine (! commutative_symmetric_braiding_after_4_copies V m @ _);
        apply maponpaths;
        cbn;
        unfold dialgebra_disp_tensor_op;
        apply maponpaths_2;
        apply pathsinv0, id_left
      | refine (id_right _ @ ! diagonal_is_comonoid_mor_counit m @ _);
        apply maponpaths;
        unfold dialgebra_disp_tensor_op;
          cbn;
        apply maponpaths_2;
        apply pathsinv0, id_left]).
    - refine (ε_{m} ,, (_ ,, tt) ,, tt).
      abstract (split ; cbn;
                [ refine (aug_is_comonoid_mor_comult m @ _);
                  apply maponpaths;
                  apply pathsinv0, id_left
                | refine (_ @ assoc' _ _ _);
                  apply pathsinv0, id_right]).
  Defined.

  Lemma commutative_comonoid_to_comonoid_of_comonoids_laws
    (m : commutative_comonoid V)
    : comonoid_laws (symmetric_cat_commutative_comonoids V)
        (commutative_comonoid_to_comonoid_of_comonoids_data m).
  Proof.
    repeat split ;
      (use subtypePath ;
       [intro ; apply is_locally_propositional_commutative_comonoid
       | apply (pr12 m)]).
  Qed.

  Definition commutative_comonoid_to_comonoid_of_comonoids
    (m : commutative_comonoid V)
    : comonoid (symmetric_cat_commutative_comonoids V).
  Proof.
    exists m.
    exists (pr2 (commutative_comonoid_to_comonoid_of_comonoids_data m)).
    exact (commutative_comonoid_to_comonoid_of_comonoids_laws m).
  Defined.

  Definition comonoid_mor_is_comonoid_mor
    {x y : commutative_comonoid V} (f : _⟦x,y⟧)
    : comonoid_mor_struct (symmetric_cat_commutative_comonoids V)
        (x,, pr2 (commutative_comonoid_to_comonoid_of_comonoids x))
        (y,, pr2 (commutative_comonoid_to_comonoid_of_comonoids y)) f.
  Proof.
    apply make_is_comonoid_mor.
    - use subtypePath.
      + intro ; apply is_locally_propositional_commutative_comonoid.
      + apply (pr2 f).
    - use subtypePath.
      + intro ; apply is_locally_propositional_commutative_comonoid.
      + exact (pr2 (pr112 f)).
  Qed.

  Definition cartesian_monoidal_cat_of_comm_comonoids
    : is_cartesian (symmetric_cat_commutative_comonoids V).
  Proof.
    use symm_monoidal_is_cartesian_from_comonoid.
    - exact (λ m, pr2 (commutative_comonoid_to_comonoid_of_comonoids m)).
    - exact (λ _ _ f, comonoid_mor_is_comonoid_mor f).
    - use subtypePath.
      + intro ; apply is_locally_propositional_commutative_comonoid.
      + apply id_right.
    - intros mx my.
      use subtypePath.
      + intro ; apply is_locally_propositional_commutative_comonoid.
      + cbn.
        unfold dialgebra_disp_tensor_op.
        cbn.
        now rewrite id_left.
  Qed.

End CartesianMonoidalCategoryOfCommutativeComonoids.
