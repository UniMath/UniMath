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

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Comonoids.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsCategory.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsMonoidalCategory.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.MonoidalCartesianBuilder.

Local Open Scope cat.
Import MonoidalNotations.
Import ComonoidNotations.

Section CartesianMonoidalCategoryOfCommutativeComonoids.

  Context {C : category} {M : monoidal C} (S : symmetric M).

  Lemma diagonal_is_comonoid_mor_mult
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : is_comonoid_mor_mult M m (tensor_of_comonoids S m m) μ_{m}.
  Proof.
    apply (! commutative_symmetric_braiding_after_4_copies S c).
  Qed.

  Lemma diagonal_is_comonoid_mor_unit
    {x : C} (m : comonoid M x)
    : is_comonoid_mor_unit M m (tensor_of_comonoids S m m) (pr11 m).
  Proof.
    refine (_@ cancel_postcomposition _ _ (pr21 m) (pr12 m) @ id_left _).
    rewrite ! assoc'.
    apply maponpaths.
    rewrite <- (monoidal_leftunitornat M _ _ (pr21 m)).
    now rewrite ! assoc.
  Qed.

  Lemma diagonal_is_comonoid_mor
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : is_comonoid_mor M m (tensor_of_comonoids S m m) (pr11 m).
  Proof.
    exists (diagonal_is_comonoid_mor_mult c).
    exact (diagonal_is_comonoid_mor_unit m).
  Qed.

  Lemma aug_is_comonoid_mor_mult
    {x : C} (m : comonoid M x)
    : is_comonoid_mor_mult M m comonoid_disp_unit (pr21 m).
  Proof.
    refine (assoc _ _ _ @ _).
    etrans. {
      apply maponpaths_2.
      apply comonoid_laws_unit_left'.
    }
    apply (monoidal_leftunitorinvnat M).
  Qed.

  Lemma aug_is_comonoid_mor
    {x : C} (m : comonoid M x)
    : is_comonoid_mor M m comonoid_disp_unit (pr21 m).
  Proof.
    exists (aug_is_comonoid_mor_mult m).
    apply id_right.
  Qed.

  Definition commutative_comonoid_to_comonoid_of_comonoids_data
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : comonoid_data (monoidal_cat_of_comm_comonoids S) (x,,m,,c).
  Proof.
    refine (_ ,, _).
    - refine (pr11 m ,, _ ,, tt).
      exact (diagonal_is_comonoid_mor c).
    - refine (pr21 m ,, _ ,, tt).
      exact (aug_is_comonoid_mor m).
  Defined.

  Lemma commutative_comonoid_to_comonoid_of_comonoids_laws
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : comonoid_laws (monoidal_cat_of_comm_comonoids S)
        (commutative_comonoid_to_comonoid_of_comonoids_data c).
  Proof.
    repeat split.
    - use subtypePath.
      + intro ; simpl ; apply isapropdirprod ;
          [apply isaprop_is_comonoid_mor | apply isapropunit].
      + apply m.
    - use subtypePath.
      + intro ; simpl ; apply isapropdirprod ;
          [apply isaprop_is_comonoid_mor | apply isapropunit].
      + apply m.
    - use subtypePath.
      + intro ; simpl ; apply isapropdirprod ;
          [apply isaprop_is_comonoid_mor | apply isapropunit].
      + apply m.
  Qed.

  Definition commutative_comonoid_to_comonoid_of_comonoids
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : comonoid (monoidal_cat_of_comm_comonoids S) (x,,m,,c).
  Proof.
    exists (commutative_comonoid_to_comonoid_of_comonoids_data c).
    exact (commutative_comonoid_to_comonoid_of_comonoids_laws c).
  Defined.

  Lemma comonoid_mor_is_comonoid_mor_mult
    {mx my : category_of_comm_comonoids_in_monoidal_cat S}
    (f : category_of_comm_comonoids_in_monoidal_cat S ⟦mx, my⟧)
    : is_comonoid_mor_mult (monoidal_cat_of_comm_comonoids S)
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 mx))
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 my))
        f.
  Proof.
    use subtypePath.
    { intro ; simpl ; apply isapropdirprod ;
          [apply isaprop_is_comonoid_mor | apply isapropunit]. }
    induction f as [f [mf tf]].
    exact (pr1 mf).
  Qed.

  Lemma comonoid_mor_is_comonoid_mor_unit
    {mx my : category_of_comm_comonoids_in_monoidal_cat S}
    (f : category_of_comm_comonoids_in_monoidal_cat S ⟦mx, my⟧)
    : is_comonoid_mor_unit (monoidal_cat_of_comm_comonoids S)
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 mx))
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 my))
        f.
  Proof.
    use subtypePath.
    { intro ; simpl ; apply isapropdirprod ;
        [apply isaprop_is_comonoid_mor | apply isapropunit]. }
    induction f as [f [mf tf]].
    exact (pr2 mf).
  Qed.

  Lemma comonoid_mor_is_comonoid_mor
    {mx my : category_of_comm_comonoids_in_monoidal_cat S}
    (f : category_of_comm_comonoids_in_monoidal_cat S ⟦mx, my⟧)
    : is_comonoid_mor (monoidal_cat_of_comm_comonoids S)
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 mx))
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 my))
        f.
  Proof.
    split.
    - exact (comonoid_mor_is_comonoid_mor_mult f).
    - exact (comonoid_mor_is_comonoid_mor_unit f).
  Qed.

  Definition cartesian_monoidal_cat_of_comm_comonoids
    : is_cartesian (_ ,, monoidal_cat_of_comm_comonoids S).
  Proof.
    use symm_monoidal_is_cartesian_from_comonoid.
    - apply symmetric_monoidal_cat_of_comm_comonoids.
    - exact (λ m, commutative_comonoid_to_comonoid_of_comonoids (pr22 m)).
    - exact (λ _ _ f, comonoid_mor_is_comonoid_mor f).
    - use subtypePath.
      {
        intro ; simpl ; apply isapropdirprod ;
          [apply isaprop_is_comonoid_mor | apply isapropunit].
      }
      apply idpath.
    - intros mx my.
      use subtypePath.
      {
        intro ; simpl ; apply isapropdirprod ;
          [apply isaprop_is_comonoid_mor | apply isapropunit].
      }
      apply idpath.
  Qed.

End CartesianMonoidalCategoryOfCommutativeComonoids.
