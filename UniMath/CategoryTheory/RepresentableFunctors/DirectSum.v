(** *** direct sums

    Recall that X is a family of objects in a category, and the map from the
    sum to the product is an isomorphism, then the sum is called a direct sum. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import
        UniMath.Foundations.Sets
        UniMath.Combinatorics.FiniteSets
        UniMath.CategoryTheory.RepresentableFunctors.Representation
        UniMath.CategoryTheory.RepresentableFunctors.Precategories.
Require UniMath.CategoryTheory.RepresentableFunctors.RawMatrix.
Local Open Scope cat.

Definition identity_matrix {C:category} (h:ZeroMaps C)
           {I} (d:I -> ob C) (dec : isdeceq I) : ∏ i j, Hom C (d j) (d i).
Proof.
  intros. induction (dec i j) as [ eq | ne ].
  { induction eq. apply identity. }
  { apply h. }
Defined.

Definition identity_map {C:category} (h:ZeroMaps C)
           {I} {d:I -> ob C} (dec : isdeceq I)
           (B:Sum d) (D:Product d)
      : Hom C (universalObject B) (universalObject D).
Proof.
  intros. apply RawMatrix.from_matrix. apply identity_matrix.
  - assumption.
  - assumption.
Defined.

(* Record DirectSum {C:category} (h:ZeroMaps C) I (dec : isdeceq I) (c : I -> ob C) := *)
(*   make_DirectSum { *)
(*       ds : C; *)
(*       ds_pr : ∏ i, Hom C ds (c i); *)
(*       ds_in : ∏ i, Hom C (c i) ds; *)
(*       ds_id : ∏ i j, ds_pr i ∘ ds_in j = identity_matrix h c dec i j; *)
(*       ds_isprod : ∏ c, isweq (λ f : Hom C c ds, λ i, ds_pr i ∘ f); *)
(*       ds_issum  : ∏ c, isweq (λ f : Hom C ds c, λ i, f ∘ ds_in i) }. *)

Section A.

Context {C:category} (h:ZeroMaps C) I (dec : isdeceq I) (c : I -> ob C).

Definition DirectSum : Type := (*  *)
  ∑
    (ds : C)
    (ds_pr : ∏ i, Hom C ds (c i))
    (ds_in : ∏ i, Hom C (c i) ds)
    (ds_id : ∏ i j, ds_pr i ∘ ds_in j = identity_matrix h c dec i j)
    (ds_isprod : ∏ c, isweq (λ f : Hom C c ds, λ i, ds_pr i ∘ f)),
  (* ds_issum : *) ∏ c, isweq (λ f : Hom C ds c, λ i, f ∘ ds_in i).
Definition ds (x:DirectSum) := pr1 x.
Definition ds_pr (x:DirectSum) := pr12 x.
Definition ds_in (x:DirectSum) := pr122 x.
Definition ds_id (x:DirectSum) := pr122 (pr2 x).
Definition ds_isprod (x:DirectSum) := pr122 (pr22 x).
Definition ds_issum (x:DirectSum) := pr222 (pr22 x).
Definition make_DirectSum ds ds_pr ds_in ds_id ds_isprod ds_issum : DirectSum
  := ds,, ds_pr,, ds_in,, ds_id,, ds_isprod,, ds_issum.

End A.

Definition toDirectSum {C:category} (h:ZeroMaps C) {I} (dec : isdeceq I) (d:I -> ob C)
           (B:Sum d) (D:Product d)
           (is: is_iso (identity_map h dec B D)) : DirectSum h I dec d.
Proof.
  intros. set (id := identity_map h dec B D).
  refine (make_DirectSum h I dec d (universalObject D)
                         (λ i, pr_ D i)
                         (λ i, id ∘ in_ B i) _ _ _).
  { intros. exact (RawMatrix.from_matrix_entry_assoc D B (identity_matrix h d dec) i j). }
  { intros. exact (pr2 (universalProperty D c)). }
  { intros.
    assert (b : (λ (f : Hom C (universalObject D) c) (i : I), (f ∘ id) ∘ in_ B i)
             = (λ (f : Hom C (universalObject D) c) (i : I), f ∘ (id ∘ in_ B i))).
    { apply funextsec; intros f. apply funextsec; intros i. apply assoc. }
    destruct b.
    exact (twooutof3c (λ f, f ∘ id)
                      (λ g i, g ∘ in_ B i)
                      (iso_comp_right_isweq (id,,is) c)
                      (pr2 (universalProperty B c))). }
Defined.
Definition FiniteDirectSums (C:category) :=
             ∑ h : ZeroMaps C,
             ∏ I : FiniteSet,
             ∏ d : I -> ob C,
               DirectSum h I (isfinite_isdeceq I (pr2 I)) d.
