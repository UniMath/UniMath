(** In this file, the category of comonoids internal to a monoidal category is defined

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Comonoids.

Local Open Scope cat.

Import MonoidalNotations.

Section Category_of_Comonoids.

  Context {C : category} (M : monoidal C).

  Definition comonoid_disp_cat : disp_cat C.
  Proof.
    use disp_struct.
    - exact (λ x, comonoid M x).
    - exact (λ x y mx my f, is_comonoid_mor M mx my f).
    - intro ; intros ; apply isaprop_is_comonoid_mor.
    - intro ; intro ; apply id_is_comonoid_mor.
    - intros x y z f g xx yy zz pf pg.
      exact (comp_is_comonoid_mor M pf pg).
  Defined.

  Definition category_of_comonoids_in_monoidal_cat : category
    := total_category comonoid_disp_cat.

  Let COMON : category := category_of_comonoids_in_monoidal_cat.

  Definition comonoid_carrier
             (X : COMON)
    : ob C := pr1 X.

  Definition comonoid_struct (X : COMON)
    : comonoid M (comonoid_carrier X)
    := pr2 X.

  Definition comonoid_comultiplication (X : COMON)
    : C⟦comonoid_carrier X, comonoid_carrier X ⊗_{ M} comonoid_carrier X⟧
    := comonoid_data_comultiplication M (comonoid_struct X).

  Definition comonoid_counit (X : COMON)
    : C⟦comonoid_carrier X, I_{M}⟧
    := comonoid_data_counit M (comonoid_struct X).

  Definition comonoid_left_counit_law (X : COMON)
    : comonoid_laws_unit_left M (comonoid_struct X)
    := comonoid_to_unit_left_law M (comonoid_struct X).

  Definition comonoid_right_counit_law (X : COMON)
    : comonoid_laws_unit_right M (comonoid_struct X)
    := comonoid_to_unit_right_law M (comonoid_struct X).

  Definition comonoid_assoc_law (X : COMON)
    : comonoid_laws_assoc M (comonoid_struct X)
    := comonoid_to_assoc_law M (comonoid_struct X).

End Category_of_Comonoids.

Section Category_of_commutative_comonoids.

  Context {C : category} {M : monoidal C} (S : symmetric M).

  Definition commutative_comonoids_disp_cat
    : disp_cat (category_of_comonoids_in_monoidal_cat M)
    := disp_full_sub
         (category_of_comonoids_in_monoidal_cat M)
         (λ x, is_commutative S (pr2 x)).

  Definition commutative_comonoids_disp_cat_over_base
    : disp_cat C.
  Proof.
    use sigma_disp_cat.
    - exact (comonoid_disp_cat M).
    - exact commutative_comonoids_disp_cat.
  Defined.

  Definition category_of_comm_comonoids_in_monoidal_cat
    : category
    := total_category commutative_comonoids_disp_cat_over_base.

End Category_of_commutative_comonoids.

Section Aux.

  Lemma comonoid_disp_cat_locally_propositional
        {C : category} (M : monoidal C)
  : locally_propositional (comonoid_disp_cat M).
  Proof.
    intro ; intros ; apply isaprop_is_comonoid_mor.
  Qed.

  Lemma comm_comonoid_disp_cat_locally_propositional
        {C : category} {M : monoidal C} (S : symmetric M)
  : locally_propositional (commutative_comonoids_disp_cat S).
  Proof.
    intro ; intros ; apply isapropunit.
  Qed.

End Aux.
