Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.limits.products.

Require Import UniMath.AlgebraicTheories.AlgebraicBase.
Require Import UniMath.AlgebraicTheories.AlgebraicTheory.
Require Import UniMath.AlgebraicTheories.AbstractClone.
Require Import UniMath.AlgebraicTheories.AbstractCloneAlgebraicTheory.

Local Open Scope cat.

Section EndomorphismAlgebraicTheory.

  Context {C : category}.
  Variable (finite_products: ∏ (n : nat), Products (stn n) C).
  Variable (X : C).

  (* Helper definitions *)
  Local Definition power_function (n : nat) : Product (stn n) C _ := finite_products n (λ _, X).

  Local Definition power_function_set (n : nat) : ob C := pr11 (power_function n).

  Local Definition power_function_projection (n : nat) (i : stn n) : C ⟦ power_function_set n, X ⟧ := pr21 (power_function n) i.

  Local Definition power_function_is_product (n : nat) : isProduct _ C _ (power_function_set n) _ := pr2 (power_function n).

  Local Definition full_induced_map {Y : C} {n : nat} (projections : stn n → C ⟦ Y, X ⟧) : (∑ fap: C⟦Y, power_function_set n⟧, ∏ i, fap · (power_function_projection n i) = projections i) := (pr1 (power_function_is_product _ _ projections)).

  Local Definition induced_map {Y : C} {n : nat} (projections : stn n → C ⟦ Y, X ⟧) : C⟦Y, power_function_set n⟧ := (pr1 (full_induced_map projections)).

  Local Definition induced_map_commutes {Y : C} {n : nat} (projections : stn n → C ⟦ Y, X ⟧) (i : stn n) : (induced_map projections) · (power_function_projection n i) = projections i := (pr2 (full_induced_map projections) i).

  Local Definition induced_map_equals {Y : C} {n : nat} (g : C⟦Y, power_function_set n⟧) : g = induced_map (λ i, (power_function_projection n i) ∘ g).
  Proof.
    pose (postprojections := (λ i, g · (power_function_projection n i))).
    pose (map_is_unique := pr2 (power_function_is_product _ _ postprojections)).
    exact (maponpaths pr1 (map_is_unique (g ,, (λ _, idpath _)))).
  Defined.

  (* Construct an algebraic theory as an abstract clone *)
  Definition endomorphism_clone_data : abstract_clone_data.
  Proof.
    use make_abstract_clone_data.
    - use make_algebraic_base.
      + intro n.
        use make_hSet.
        * exact (C⟦power_function_set n, X⟧).
        * apply C. 
      + intros.
        exact (X0 ∘ (induced_map X1)).
    - apply power_function_projection.
  Defined.

  Definition endomorphism_is_clone : is_abstract_clone endomorphism_clone_data.
  Proof.
    use make_is_abstract_clone.
    - intro.
      intros.
      apply induced_map_commutes.
    - intro.
      intros.
      rewrite <- id_left.
      apply (maponpaths (λ x, x · _)).
      rewrite (induced_map_equals (identity _)).
      apply maponpaths.
      apply funextfun.
      intro.
      symmetry.
      apply id_left.
    - intro.
      intros.
      simpl.
      rewrite (pr122 (C : precategory)).
      apply (maponpaths (λ f, f · f_l)).
      rewrite (induced_map_equals (_ · _)).
      apply maponpaths, funextfun.
      intro.
      rewrite (pr222 (C : precategory)).
      apply maponpaths.
      apply full_induced_map.
  Qed.

  Definition endomorphism_theory : algebraic_theory.
  Proof.
    apply (pr1weq algebraic_theory_weq_abstract_clone).
    exact (make_abstract_clone endomorphism_clone_data endomorphism_is_clone).
  Defined.

End EndomorphismAlgebraicTheory.