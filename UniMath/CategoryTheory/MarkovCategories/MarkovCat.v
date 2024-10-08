(*********************************************
Markov Categories

This file contains the basic definitions of the theory of Markov categories.

Table of Contents
1. Definition of Markov categories
2. Projections

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(** 1. Definition of Markov categories **)

Definition markov_category_data : UU
  := ∑ (C : sym_monoidal_cat),
     is_semicartesian C
     ×
     ∏ (x : C), x --> x ⊗ x.

Coercion markov_category_data_to_sym_monoidal_cat
         (C : markov_category_data)
  : sym_monoidal_cat
  := pr1 C.

Proposition is_semicartesian_markov_category
            (C : markov_category_data)
  : is_semicartesian C.
Proof.
  exact (pr12 C).
Defined.

Definition copy
           {C : markov_category_data}
           (x : C)
  : x --> x ⊗ x
  := pr22 C x.

Definition del
           {C : markov_category_data}
           (x : C)
  : x --> I_{C}
  := semi_cart_to_unit (is_semicartesian_markov_category C) x.

Proposition markov_category_unit_eq
            {C : markov_category_data}
            {x : C}
            (f g : x --> I_{C})
  : f = g.
Proof.
  apply semi_cart_to_unit_eq.
  apply is_semicartesian_markov_category.
Qed.

Definition markov_category_laws
           (C : markov_category_data)
  : UU
  := (∏ (x : C),
      copy x · (identity _ #⊗ copy x)
      =
      copy x · (copy x #⊗ identity _) · mon_lassociator _ _ _)
     ×
     (∏ (x : C),
      copy x · (identity _ #⊗ del x) · mon_runitor _
      =
      identity _)
     ×
     (∏ (x : C),
      copy x · (del x #⊗ identity _) · mon_lunitor _
      =
      identity _)
     ×
     (∏ (x : C),
      copy x · sym_mon_braiding _ _ _
      =
      copy x)
     ×
     (∏ (x y : C),
      (copy x #⊗ copy y)
      · inner_swap _ _ _ _ _
      =
      copy (x ⊗ y)).

Definition markov_category
  : UU
  := ∑ (C : markov_category_data),
     markov_category_laws C.


(** 2. Projections **)

Coercion markov_category_to_data
         (C : markov_category)
  : markov_category_data
  := pr1 C.

Section MarkovCategoryLaws.
  Context (C : markov_category).

  Proposition copy_assoc'
              (x : C)
    : copy x · (identity _ #⊗ copy x)
      =
      copy x · (copy x #⊗ identity _) · mon_lassociator _ _ _.
  Proof.
    exact (pr12 C x).
  Defined.

  Proposition copy_assoc (x : C)
    : copy x · (copy x #⊗ identity _)
      =
      copy x · (identity _ #⊗ copy x) · mon_rassociator _ _ _.
  Proof.
    rewrite copy_assoc'.
    rewrite !assoc'.
    rewrite mon_lassociator_rassociator.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition copy_del_r
              (x : C)
    : copy x · (identity _ #⊗ del x) · mon_runitor _
      =
      identity _.
  Proof.
    exact (pr122 C x).
  Defined.

  Proposition copy_del_l
              (x : C)
    : copy x · (del x #⊗ identity _) · mon_lunitor _
      =
      identity _.
  Proof.
    exact (pr1 (pr222 C) x).
  Defined.

  Proposition copy_comm
              (x : C)
    : copy x · sym_mon_braiding _ _ _
      =
      copy x.
  Proof.
    exact (pr12 (pr222 C) x).
  Defined.

  Proposition copy_tensor
              (x y : C)
    : (copy x #⊗ copy y)
      · inner_swap _ _ _ _ _
      =
      copy (x ⊗ y).
  Proof.
    exact (pr22 (pr222 C) x y).
  Defined.

  Proposition copy_I_mon_rinvunitor :
    copy (I_{C}) = mon_rinvunitor (I_{C}).
  Proof.
     use cancel_z_iso.
    - apply I_{C}.
    - use make_z_iso.
      + apply mon_runitor.
      + apply mon_rinvunitor.
      + split.
        * apply mon_runitor_rinvunitor.
        * apply mon_rinvunitor_runitor.
    - cbn.
      apply markov_category_unit_eq.
  Qed.

  Proposition copy_I_mon_linvunitor :
    copy (I_{C}) = mon_linvunitor (I_{C}).
  Proof.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    apply copy_I_mon_rinvunitor.
  Qed.

  Proposition del_natural
            {x y : C}
            (f : x --> y)
  : f · del y = del x.
  Proof.
    apply markov_category_unit_eq.
  Qed.
  
End MarkovCategoryLaws.

