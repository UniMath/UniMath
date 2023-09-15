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

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.

Import MonoidalNotations.
Import ComonoidNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section MonoidalCategoryOfComonoids.

  Context (V : sym_monoidal_cat).

  Let V_comult : disp_monoidal (dialgebra_disp_cat _ _) V
      := dialgebra_disp_monoidal (identity_fmonoidal V) (diag_functor_fmonoidal_lax V).

  Let V_counit
      : disp_monoidal (dialgebra_disp_cat (functor_identity V) (constant_functor _ _ I_{V})) V
      := dialgebra_disp_monoidal (identity_fmonoidal V) (constantly_unit_functor_fmonoidal V).

  Definition disp_monoidal_comonoids_data
    : disp_monoidal (disp_cat_of_comonoids_data V) V.
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
      rewrite mon_runitor_I_mon_lunitor_I.
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
    - intros [x1 x2] [y1 y2] mx my.
      repeat split.
      + refine (_ @ tensor_of_comonoids_laws_unit_left V (x1 ,, x2 ,, mx) (y1 ,, y2 ,, my)).
        cbn.
        unfold dialgebra_disp_tensor_op.
        apply maponpaths_2.
        cbn.
        now do 2 rewrite id_left.
      + refine (_ @ tensor_of_comonoids_laws_unit_right V (x1 ,, x2 ,, mx) (y1 ,, y2 ,, my)).
        apply maponpaths_2.
        cbn.
        unfold dialgebra_disp_tensor_op.
        cbn.
        now do 2 rewrite id_left.
      + refine (_ @ tensor_of_comonoids_laws_assoc V (x1 ,, x2 ,, mx) (y1 ,, y2 ,, my) @ _).
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
    - abstract (
          refine (_ @ id_right _);
          apply maponpaths;
          apply sym_mon_braiding_id).
    - abstract (
          intros [x1 x2] [y1 y2] mx my;
          refine (_ @ tensor_of_comm_comonoids V (x1 ,, x2 ,, mx) (y1 ,, y2 ,, my) @ _);
          [ apply maponpaths_2;
            cbn;
            unfold dialgebra_disp_tensor_op;
            cbn;
            now rewrite id_left
          | cbn;
            unfold dialgebra_disp_tensor_op;
            cbn;
            now rewrite id_left]).
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
