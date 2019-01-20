(** * Dependent product functor *)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.exponentials.

Require Import UniMath.CategoryTheory.Slice.Core.
Require Import UniMath.CategoryTheory.Slice.Limits.

Local Open Scope cat.

(** If the base change functor has a right adjoint, called dependent product, then C / c has
    exponentials. The formal proof is inspired by Proposition 2.1 from:
    https://ncatlab.org/nlab/show/locally+cartesian+closed+category#in_category_theory
*)
Section dependent_product.

  Local Notation "C / X" := (slice_precat C X (pr2 C)).

  Context {C : category} {PC : Pullbacks C}.
  Context (H : ∏ {c c' : C} (g : C⟦c,c'⟧), is_left_adjoint (base_change_functor (homset_property C) PC g)).

  Let dependent_product_functor {c c' : C} (g : C⟦c,c'⟧) :
    functor (C / c) (C / c') := right_adjoint (H c c' g).

  Let BPC c : BinProducts (C / c) :=
    @BinProducts_slice_precat C (homset_property C) PC c.

  Lemma const_prod_functor1_slicecat c (Af : C / c) :
    constprod_functor1 (BPC c) Af =
    functor_composite (base_change_functor (homset_property C) PC (pr2 Af))
                      (slicecat_functor (homset_property C) (pr2 Af)).
  Proof.
  apply functor_eq; try apply has_homsets_slice_precat.
  use functor_data_eq.
  - intro x; apply idpath.
  - intros x y f; apply (eq_mor_slicecat (homset_property C)); simpl.
    apply PullbackArrowUnique.
    + rewrite PullbackArrow_PullbackPr1, id_right; apply idpath.
    + rewrite PullbackArrow_PullbackPr2; apply idpath.
  Defined.

  Lemma dependent_product_to_exponentials c : Exponentials (BPC c).
  Proof.
  intros Af.
  use tpair.
  + apply (functor_composite (base_change_functor (homset_property C) PC (pr2 Af))
                            (dependent_product_functor (pr2 Af))).
  + rewrite const_prod_functor1_slicecat.
    apply are_adjoints_functor_composite.
    - apply (pr2 (H _ _ _)).
    - apply are_adjoints_slicecat_functor_base_change.
  Defined.

End dependent_product.