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

Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Comonoids.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.ComonoidsCategoryAsDialg.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.MonoidalCartesianBuilder.

Local Open Scope cat.
Import MonoidalNotations.
Import ComonoidNotations.

Section CartesianMonoidalCategoryOfCommutativeComonoids.

  Context {C : category} {M : monoidal C} (S : symmetric M).
  Let V : sym_monoidal_cat := (C,,M),,S.

  Lemma diagonal_is_comonoid_mor_mult
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : is_comonoid_mor_mult M m (tensor_of_comonoids V m m) μ_{m}.
  Proof.
    apply (! commutative_symmetric_braiding_after_4_copies S c).
  Qed.

  Lemma diagonal_is_comonoid_mor_unit
    {x : C} (m : comonoid M x)
    : is_comonoid_mor_unit M m (tensor_of_comonoids V m m) (pr11 m).
  Proof.
    refine (_@ cancel_postcomposition _ _ (pr21 m) (pr12 m) @ id_left _).
    rewrite ! assoc'.
    apply maponpaths.
    rewrite <- (monoidal_leftunitornat M _ _ (pr21 m)).
    now rewrite ! assoc.
  Qed.

  Lemma diagonal_is_comonoid_mor
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : is_comonoid_mor M m (tensor_of_comonoids V m m) (pr11 m).
  Proof.
    exists (diagonal_is_comonoid_mor_mult c).
    exact (diagonal_is_comonoid_mor_unit m).
  Qed.

  Lemma aug_is_comonoid_mor_mult
    {x : C} (m : comonoid M x)
    : is_comonoid_mor_mult M m (comonoid_disp_unit V) (pr21 m).
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
    : is_comonoid_mor M m (comonoid_disp_unit V) (pr21 m).
  Proof.
    exists (aug_is_comonoid_mor_mult m).
    apply id_right.
  Qed.

  Definition commutative_comonoid_to_comonoid_of_comonoids_data
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : comonoid_data (sym_monoidal_cat_commutative_comonoids V) (x,,m,,c).
  Proof.
    refine (_ ,, _).
    - refine (pr11 m ,, (_ ,, tt) ,, tt).
      split ; cbn.
      + refine (diagonal_is_comonoid_mor_mult c @ _).
        apply maponpaths.
        cbn.
        unfold MonoidalDialgebras.dialgebra_disp_tensor_op.
        apply maponpaths_2.
        apply pathsinv0, id_left.
      + refine (_ @ ! diagonal_is_comonoid_mor_unit m @ _).
        * apply id_right.
        * cbn.
          apply maponpaths.
          unfold MonoidalDialgebras.dialgebra_disp_tensor_op.
          cbn.
          apply maponpaths_2.
          apply pathsinv0, id_left.
    - refine (pr21 m ,, (_ ,, tt) ,, tt).
      split ; cbn.
      + refine (aug_is_comonoid_mor_mult m @ _).
        apply maponpaths.
        apply pathsinv0, id_left.
      + refine (_ @ assoc' _ _ _).
        apply pathsinv0, id_right.
  Defined.

  Lemma commutative_comonoid_to_comonoid_of_comonoids_laws
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : comonoid_laws (sym_monoidal_cat_commutative_comonoids V)
        (commutative_comonoid_to_comonoid_of_comonoids_data c).
  Proof.
    repeat split ;
      (use subtypePath ;
       [intro ; apply cat_commutative_comonoids_is_locally_propositional
       | apply m]).
  Qed.

  Definition commutative_comonoid_to_comonoid_of_comonoids
    {x : C} {m : comonoid M x} (c : is_commutative S m)
    : comonoid (sym_monoidal_cat_commutative_comonoids V) (x,,m,,c).
  Proof.
    exists (commutative_comonoid_to_comonoid_of_comonoids_data c).
    exact (commutative_comonoid_to_comonoid_of_comonoids_laws c).
  Defined.

  Lemma comonoid_mor_is_comonoid_mor_mult
    {mx my : sym_monoidal_cat_commutative_comonoids V}
    (f : ((sym_monoidal_cat_commutative_comonoids V))⟦mx, my⟧)
    : is_comonoid_mor_mult (sym_monoidal_cat_commutative_comonoids V)
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 mx))
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 my))
        f.
  Proof.
    use subtypePath.
    - intro ; apply cat_commutative_comonoids_is_locally_propositional.
    - apply (pr2 f).
  Qed.

  Lemma comonoid_mor_is_comonoid_mor_unit
    {mx my : sym_monoidal_cat_commutative_comonoids V}
    (f : (sym_monoidal_cat_commutative_comonoids V)⟦mx, my⟧)
    : is_comonoid_mor_unit (sym_monoidal_cat_commutative_comonoids V)
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 mx))
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 my))
        f.
  Proof.
    use subtypePath.
    - intro ; apply cat_commutative_comonoids_is_locally_propositional.
    - refine (! pr2 (pr112 f) @ _).
      apply id_right.
  Qed.

  Lemma comonoid_mor_is_comonoid_mor
    {mx my : sym_monoidal_cat_commutative_comonoids V}
    (f : (sym_monoidal_cat_commutative_comonoids V)⟦mx, my⟧)
    : is_comonoid_mor (sym_monoidal_cat_commutative_comonoids V)
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 mx))
        (commutative_comonoid_to_comonoid_of_comonoids (pr22 my))
        f.
  Proof.
    split.
    - exact (comonoid_mor_is_comonoid_mor_mult f).
    - exact (comonoid_mor_is_comonoid_mor_unit f).
  Qed.

  Definition cartesian_monoidal_cat_of_comm_comonoids
    : is_cartesian (sym_monoidal_cat_commutative_comonoids V).
  Proof.
    use symm_monoidal_is_cartesian_from_comonoid.
    - exact (λ m, commutative_comonoid_to_comonoid_of_comonoids (pr22 m)).
    - exact (λ _ _ f, comonoid_mor_is_comonoid_mor f).
    - use subtypePath.
      + intro ; apply cat_commutative_comonoids_is_locally_propositional.
      + apply id_right.
    - intros mx my.
      use subtypePath.
      + intro ; apply cat_commutative_comonoids_is_locally_propositional.
      + cbn.
        unfold MonoidalDialgebras.dialgebra_disp_tensor_op.
        cbn.
        now rewrite id_left.
  Qed.

End CartesianMonoidalCategoryOfCommutativeComonoids.
