Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.

Local Open Scope algebraic_theory.

Definition abstract_clone_data := ∑ (B: algebraic_base),
  (∏ n, stn n → B n).

Definition make_abstract_clone_data
  (C : algebraic_base)
  (pr : ∏ {n}, stn n → C n)
  : abstract_clone_data.
Proof.
  exact (C ,, pr).
Defined.

Coercion algebraic_base_from_abstract_clone (C : abstract_clone_data) : algebraic_base := pr1 C.

Definition clone_pr {C : abstract_clone_data} {n}
  : stn n → C n
  := pr2 C n.

(* Define the unitality property of the algebraic theory *)
Definition comp_project_component (C : abstract_clone_data) : UU := ∏
  (m n : nat)
  (i : stn m)
  (f : stn m → C n),
    (clone_pr i) • f = f i.

(* Define the compatibility of the projection function with composition *)
Definition comp_identity_projections (C : abstract_clone_data) : UU := ∏
  (n : nat)
  (f : C n),
    f • (λ i, clone_pr i) = f.

(* Define the associativity property of the algebraic theory *)
Definition comp_is_assoc (C : abstract_clone_data) : UU := ∏
  (l m n : nat)
  (f_l : C l)
  (f_m : stn l → C m)
  (f_n : stn m → C n),
    (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

Definition is_abstract_clone (C : abstract_clone_data) :=
  (comp_project_component C) ×
  (comp_identity_projections C) ×
  (comp_is_assoc C).

Definition make_is_abstract_clone
  (C : abstract_clone_data)
  (H1 : comp_project_component C)
  (H2 : comp_identity_projections C)
  (H3 : comp_is_assoc C)
  : is_abstract_clone C
  := (H1 ,, H2 ,, H3).

Definition abstract_clone := ∑ C, is_abstract_clone C.

Definition make_abstract_clone
  (T : abstract_clone_data)
  (H : is_abstract_clone T)
  : abstract_clone
  := (T ,, H).

Coercion abstract_clone_data_from_abstract_clone (C : abstract_clone) : abstract_clone_data := pr1 C.

Definition abstract_clone_comp_project_component (C : abstract_clone)
  : comp_project_component C
  := pr12 C.

Definition abstract_clone_comp_identity_projections (C : abstract_clone)
  : comp_identity_projections C
  := pr122 C.

Definition abstract_clone_comp_is_assoc (C : abstract_clone)
  : comp_is_assoc C
  := pr222 C.
