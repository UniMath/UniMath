(**
In this file, the monoidal category of comonoids internal to a symmetric monoidal category is defined.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Sigma.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
Require Import UniMath.CategoryTheory.Monoidal.Examples.DiagonalFunctor.
Require Import UniMath.CategoryTheory.Monoidal.Examples.ConstantFunctor.

Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.

Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalDialgebras.
(* Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalDialgebras. *)

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.

Local Open Scope cat.

Import MonoidalNotations.
Import ComonoidNotations.

Section MonoidalCategoryOfComonoids.

  Context (V : sym_monoidal_cat).

  Notation "x ⊗ y" := (x ⊗_{V} y).
  Notation "x ⊗l f" := (x ⊗^{V}_{l} f) (at level 31).
  Notation "f ⊗r y" := (f ⊗^{V}_{r} y) (at level 31).
  Notation "f ⊗⊗ g" := (f ⊗^{V} g) (at level 31).

  Let I : V := monoidal_unit V.
  Let lu : leftunitor_data V (monoidal_unit V) := monoidal_leftunitordata V.
  Let ru : rightunitor_data V (monoidal_unit V) := monoidal_rightunitordata V.
  Let α : associator_data V := monoidal_associatordata V.
  Let luinv : leftunitorinv_data V (monoidal_unit V) := monoidal_leftunitorinvdata V.
  Let ruinv : rightunitorinv_data V (monoidal_unit V) := monoidal_rightunitorinvdata V.
  Let αinv : associatorinv_data V := monoidal_associatorinvdata V.
  Let σ := pr12 V.

  Let V_comult
      := dialgebra_disp_monoidal (identity_fmonoidal V) (diag_functor_fmonoidal V).

  Definition V_counit
    : disp_monoidal (dialgebra_disp_cat (functor_identity V) (constant_functor _ _ I_{V})) V.
  Proof.
    use (dialgebra_disp_monoidal (identity_fmonoidal V)
           (constant_functor_fmonoidal V (unit_monoid V) _ _)).
    - refine (_ ,, _).
      apply (monoidal_leftunitorisolaw V).
    - apply identity_is_z_iso.
  Defined.

  Definition disp_monoidal_comonoids_data
    : disp_monoidal (Category.disp_cat_of_comonoids_data V) V.
  Proof.
    use dirprod_disp_cat_monoidal.
    - exact V_comult.
    - exact V_counit.
    - apply is_locally_propositional_dialgebra_disp_cat.
    - apply is_locally_propositional_dialgebra_disp_cat.
  Defined.

  Definition disp_monoidal_comonoids_comonoid_law_unit
    : comonoid_laws V I_{ total_monoidal disp_monoidal_comonoids_data}.
  Proof.
    refine (_ ,, _ ,, _).
    - unfold comonoid_laws_unit_left.
      cbn.
      unfold dialgebra_disp_unit.
      rewrite ! id_left.
      rewrite (bifunctor_rightid V).
      rewrite id_right.
      apply monoidal_leftunitorisolaw.
    - unfold comonoid_laws_unit_right.
      cbn.
      unfold dialgebra_disp_unit.
      rewrite ! id_left.
      rewrite (bifunctor_leftid V).
      rewrite id_right.
      unfold fmonoidal_preservesunit.
      cbn.
      unfold diag_preserves_unit.
      rewrite <- unitors_coincide_on_unit.
      apply monoidal_leftunitorisolaw.
    - unfold comonoid_laws_assoc.
      cbn.
      unfold dialgebra_disp_unit.
      cbn.
      unfold diag_preserves_unit.
      rewrite ! id_left.
      rewrite assoc'.
      apply maponpaths.
      apply lunitorinv_preserves_leftwhiskering_with_unit.
  Qed.

  Definition disp_monoidal_comonoids_laws
    : disp_monoidal
        (comonoid_laws_disp_cat V)
        (total_monoidal disp_monoidal_comonoids_data).
  Proof.
    apply disp_monoidal_fullsub.
    - exact disp_monoidal_comonoids_comonoid_law_unit.
    - intros x y mx my.
      repeat split.
      + refine (_ @ tensor_of_comonoids_laws_unit_left V (pr1 x ,, pr2 x ,,mx) (pr1 y ,, pr2 y ,, my)).
        cbn.
        unfold dialgebra_disp_tensor_op.
        apply maponpaths_2.
        cbn.
        now do 2 rewrite id_left.
      + refine (_ @ tensor_of_comonoids_laws_unit_right V (pr1 x ,, pr2 x ,,mx) (pr1 y ,, pr2 y ,, my)).
        apply maponpaths_2.
        cbn.
        unfold dialgebra_disp_tensor_op.
        cbn.
        now do 2 rewrite id_left.
      + refine (_ @ tensor_of_comonoids_laws_assoc V (pr1 x ,, pr2 x ,,mx) (pr1 y ,, pr2 y ,, my) @ _).
        * apply maponpaths_2.
          cbn.
          unfold dialgebra_disp_tensor_op.
          cbn.
          now rewrite id_left.
        * cbn.
          unfold dialgebra_disp_tensor_op.
          cbn.
          now rewrite id_left.
  Defined.

  Definition disp_monoidal_comonoids
    : disp_monoidal (disp_cat_of_comonoids V) V.
  Proof.
    use sigma_disp_cat_monoidal.
    - exact disp_monoidal_comonoids_data.
    - exact disp_monoidal_comonoids_laws.
    - apply locally_propositional_comonoid_laws_disp_cat.
  Defined.

  Definition disp_monoidal_commutative_comonoids_laws
    : disp_monoidal (commutative_comonoids_laws_disp_cat V) (total_monoidal disp_monoidal_comonoids).
  Proof.
    apply disp_monoidal_fullsub.
    - refine (_ @ id_right _).
      apply maponpaths.
      apply sym_mon_braiding_id.
    - cbn.
      intros x y mx my.

      transparent assert (m : (commutative_comonoid V)).
      {
        refine (_ ,, _ ,, _).
        exact mx.
      }
      transparent assert (n : (commutative_comonoid V)).
      {
        refine (_ ,, _ ,, _).
        exact my.
      }


      refine (_ @ tensor_of_comm_comonoids V m n @ _).
      + apply maponpaths_2.
        unfold dialgebra_disp_tensor_op.
        cbn.
        now rewrite id_left.
      + cbn.
        unfold dialgebra_disp_tensor_op.
        cbn.
        now rewrite id_left.
  Defined.

  Definition disp_monoidal_commutative_comonoids
    : disp_monoidal (disp_cat_of_commutative_comonoids V) V.
  Proof.
    use sigma_disp_cat_monoidal.
    - exact disp_monoidal_comonoids.
    - exact disp_monoidal_commutative_comonoids_laws.
    - intro ; intros.
      apply isapropunit.
  Defined.

  Definition monoidal_cat_comonoids
    : monoidal_cat.
  Proof.
    exists (comonoid_category V).
    exact (total_monoidal disp_monoidal_comonoids).
  Defined.

  Definition monoidal_cat_of_commutative_comonoids
    : monoidal_cat.
  Proof.
    exists (commutative_comonoid_category V).
    use total_monoidal.
    - exact V.
    - exact disp_monoidal_commutative_comonoids.
  Defined.

End MonoidalCategoryOfComonoids.
