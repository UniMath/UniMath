(**************************************************************************************************

  Algebraic Theories 2

  The category-theoretic definition of algebraic theories is nice to work with, but unnecessarily
  complicated for constructing the objects directly. This file provides a way to define algebraic
  theories in a simpler way.

  Contents
  1. A type containing the minimal data needed to construct an algebraic theory [algebraic_theory']

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

(** * 1. A type containing the minimal data needed to construct an algebraic theory *)

Definition algebraic_theory'_data :=
  ∑ (C : nat → hSet),
    (∏ n, stn n → C n) ×
    (∏ m n, C m → (stn m → C n) → C n).

Definition make_algebraic_theory'_data
  (C : nat → hSet)
  (pr : ∏ n, stn n → C n)
  (comp : ∏ m n, C m → (stn m → C n) → C n)
  : algebraic_theory'_data.
Proof.
  exact (C ,, pr ,, comp).
Defined.

Definition algebraic_theory'_data_to_function (C : algebraic_theory'_data) : nat → hSet := pr1 C.
Coercion algebraic_theory'_data_to_function : algebraic_theory'_data >-> Funclass.

Definition pr' {C : algebraic_theory'_data} {n}
  : stn n → C n
  := pr12 C n.

Definition comp' {C : algebraic_theory'_data} {m n}
  : C m → (stn m → C n) → C n
  := pr22 C m n.

Definition comp_project_component (C : algebraic_theory'_data) : UU := ∏
  (m n : nat)
  (i : stn m)
  (f : stn m → C n),
    comp' (pr' i) f = f i.

Definition comp_identity_projections (C : algebraic_theory'_data) : UU := ∏
  (n : nat)
  (f : C n),
    comp' f (λ i, pr' i) = f.

Definition comp_is_assoc (C : algebraic_theory'_data) : UU := ∏
  (l m n : nat)
  (f_l : C l)
  (f_m : stn l → C m)
  (f_n : stn m → C n),
    comp' (comp' f_l f_m) f_n = comp' f_l (λ t_l, comp' (f_m t_l) f_n).

Definition is_algebraic_theory' (C : algebraic_theory'_data) :=
  (comp_project_component C) ×
  (comp_identity_projections C) ×
  (comp_is_assoc C).

Definition make_is_algebraic_theory'
  (C : algebraic_theory'_data)
  (H1 : comp_project_component C)
  (H2 : comp_identity_projections C)
  (H3 : comp_is_assoc C)
  : is_algebraic_theory' C
  := (H1 ,, H2 ,, H3).

Definition algebraic_theory' := ∑ C, is_algebraic_theory' C.

Coercion algebraic_theory'_data_from_algebraic_theory'
  (C : algebraic_theory')
  : algebraic_theory'_data
  := pr1 C.

Definition algebraic_theory'_comp_project_component (C : algebraic_theory')
  : comp_project_component C
  := pr12 C.

Definition algebraic_theory'_comp_identity_projections (C : algebraic_theory')
  : comp_identity_projections C
  := pr122 C.

Definition algebraic_theory'_comp_is_assoc (C : algebraic_theory')
  : comp_is_assoc C
  := pr222 C.

