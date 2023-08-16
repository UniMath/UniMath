(**
In this file, the symmetric monoidal category of comonoids internal to a symmetric monoidal category is defined.
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
Require Import UniMath.CategoryTheory.Monoidal.Examples.SymmetricMonoidalDialgebras.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Tensor.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Monoidal.

Local Open Scope cat.

Import MonoidalNotations.
Import ComonoidNotations.

Section SymmetricMonoidalCategoryOfComonoids.

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

  Definition disp_symmetric_comonoids_data
    : disp_symmetric (disp_monoidal_comonoids_data V) (pr2 V).
  Proof.
    use dirprod_disp_cat_symmetric_monoidal.
    - use dialgebra_disp_symmetric_monoidal.
      + exact (pr2 V).
      + apply is_symmetric_monoidal_identity.
      + apply diag_functor_is_symmetric.
    - use dialgebra_disp_symmetric_monoidal.
      + exact (pr2 V).
      + apply is_symmetric_monoidal_identity.
      + apply constant_functor_is_symmetric.
        refine (sym_mon_braiding_lunitor _ _ @ _).
        apply pathsinv0.
        apply unitors_coincide_on_unit.
  Defined.

  Definition disp_symmetric_comonoids
    : disp_symmetric (disp_monoidal_comonoids V) (pr2 V).
  Proof.
    use (sigma_disp_cat_monoidal_symmetric).
    - exact disp_symmetric_comonoids_data.
    - apply disp_symmetric_fullsub.
  Defined.

  Definition symmetric_cat_comonoids
    : sym_monoidal_cat.
  Proof.
    exists (monoidal_cat_comonoids V).
    exact (total_symmetric _ disp_symmetric_comonoids).
  Defined.

  Definition disp_symmetric_commutative_comonoids
    : disp_symmetric (disp_monoidal_commutative_comonoids V) (pr2 V).
  Proof.
    use (sigma_disp_cat_monoidal_symmetric).
    - exact disp_symmetric_comonoids.
    - apply disp_symmetric_fullsub.
  Defined.

  Definition symmetric_cat_commutative_comonoids
    : sym_monoidal_cat.
  Proof.
    Check disp_monoidal_commutative_comonoids.
    exists (monoidal_cat_of_commutative_comonoids V).
    exact (total_symmetric _ disp_symmetric_commutative_comonoids).
  Defined.

End SymmetricMonoidalCategoryOfComonoids.
