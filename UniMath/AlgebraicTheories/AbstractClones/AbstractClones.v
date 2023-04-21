Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Local Open Scope cat.

Definition abstract_clone_data :=
  ∑ (C : nat → hSet),
    (∏ n, stn n → C n) ×
    (∏ m n, C m → (stn m → C n) → C n).

Definition make_abstract_clone_data
  (C : nat → hSet)
  (pr : ∏ n, stn n → C n)
  (comp : ∏ m n, C m → (stn m → C n) → C n)
  : abstract_clone_data.
Proof.
  exact (C ,, pr ,, comp).
Defined.

Definition abstract_clone_data_to_function (C : abstract_clone_data) : nat → hSet := pr1 C.
Coercion abstract_clone_data_to_function : abstract_clone_data >-> Funclass.

Definition clone_pr {C : abstract_clone_data} {n}
  : stn n → C n
  := pr12 C n.

Definition clone_comp {C : abstract_clone_data} {m n}
  : C m → (stn m → C n) → C n
  := pr22 C m n.

(* Define the unitality property of the algebraic theory *)
Definition comp_project_component (C : abstract_clone_data) : UU := ∏
  (m n : nat)
  (i : stn m)
  (f : stn m → C n),
    clone_comp (clone_pr i) f = f i.

(* Define the compatibility of the projection function with composition *)
Definition comp_identity_projections (C : abstract_clone_data) : UU := ∏
  (n : nat)
  (f : C n),
    clone_comp f (λ i, clone_pr i) = f.

(* Define the associativity property of the algebraic theory *)
Definition comp_is_assoc (C : abstract_clone_data) : UU := ∏
  (l m n : nat)
  (f_l : C l)
  (f_m : stn l → C m)
  (f_n : stn m → C n),
    clone_comp (clone_comp f_l f_m) f_n = clone_comp f_l (λ t_l, clone_comp (f_m t_l) f_n).

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

Definition abstract_clone_to_functor_data (C : abstract_clone)
  : functor_data finite_set_skeleton_category HSET.
Proof.
  use make_functor_data.
  - exact C.
  - exact (λ _ _ a f, clone_comp f (λ i, clone_pr (a i))).
Defined.

Lemma abstract_clone_to_is_functor (C : abstract_clone)
  : is_functor (abstract_clone_to_functor_data C).
Proof.
  apply tpair.
  - intro.
    apply funextfun.
    intro.
    apply abstract_clone_comp_identity_projections.
  - do 5 intro.
    apply funextfun.
    intro.
    rewrite (abstract_clone_comp_is_assoc _ _ _ _ _ _ _ : (_ · (# (abstract_clone_to_functor_data C) g)) _ = _).
    apply (maponpaths (clone_comp x)), funextfun.
    intro.
    symmetry.
    apply abstract_clone_comp_project_component.
Qed.

Definition abstract_clone_to_algebraic_theory_data (C : abstract_clone)
  : algebraic_theory_data.
Proof.
  use make_algebraic_theory_data.
  - exact (make_functor _ (abstract_clone_to_is_functor C)).
  - exact (clone_pr firstelement).
  - exact (λ _ _, clone_comp).
Defined.

Lemma abstract_clone_to_is_algebraic_theory (C : abstract_clone)
  : is_algebraic_theory (abstract_clone_to_algebraic_theory_data C).
Proof.
  use make_is_algebraic_theory.
  - apply abstract_clone_comp_is_assoc.
  - do 2 intro.
    apply abstract_clone_comp_project_component.
  - do 2 intro.
    rewrite <- abstract_clone_comp_identity_projections.
    apply maponpaths, funextfun.
    intro.
    apply abstract_clone_comp_project_component.
  - do 6 intro.
    simpl.
    rewrite (abstract_clone_comp_is_assoc C).
    apply maponpaths, funextfun.
    intro.
    apply abstract_clone_comp_project_component.
Qed.

Definition make_algebraic_theory' (C : abstract_clone)
  : algebraic_theory
  := make_algebraic_theory _ (abstract_clone_to_is_algebraic_theory C).
