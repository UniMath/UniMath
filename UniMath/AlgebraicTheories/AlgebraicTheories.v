(**************************************************************************************************

  Algebraic Theories

  These objects are known by many names: algebraic theories, abstract clones, cartesian operads
  and Lawvere theories. This file defines them and gives constructors, accessors and related
  definitions and lemmas.

  Contents
  1. The definition of algebraic theories [algebraic_theory]
  2. Some useful properties and definitions

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.Combinatorics.Tuples.

Declare Scope algebraic_theories.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of algebraic theories *)

Definition algebraic_theory_data : UU := algebraic_theory_data_cat.

Definition algebraic_theory_data_to_function
  (T : algebraic_theory_data)
  : nat → hSet
  := pr1 T.

Coercion algebraic_theory_data_to_function : algebraic_theory_data >-> Funclass.

Definition pr
  {T : algebraic_theory_data}
  {n : nat}
  (i : stn n)
  : T n
  := pr12 T n i.

Definition comp
  {T : algebraic_theory_data}
  {m n : nat}
  (f : T m)
  (g : stn m → T n)
  : T n
  := pr22 T m n f g.

Notation "f • g" :=
  (comp f g)
  (at level 35) : algebraic_theories.

Definition algebraic_theory : UU := algebraic_theory_cat.

Coercion algebraic_theory_to_algebraic_theory_data (T : algebraic_theory)
  : algebraic_theory_data
  := pr1 T.

Definition make_algebraic_theory_data
  (T : nat → hSet)
  (pr : ∏ n (i : stn n), T n)
  (comp : ∏ m n, T m → (stn m → T n) → T n)
  : algebraic_theory_data
  := T ,, pr ,, comp.

Definition make_is_algebraic_theory
  (T : algebraic_theory_data)
  (H1 : comp_comp_ax T)
  (H2 : pr_comp_ax T)
  (H3 : comp_pr_ax T)
  : is_algebraic_theory T
  := H1 ,, H2 ,, H3.

Definition make_algebraic_theory
  (T : algebraic_theory_data)
  (H : is_algebraic_theory T)
  : algebraic_theory
  := T ,, H.

Definition comp_comp
  (T : algebraic_theory)
  {l m n : nat}
  (f_l : T l)
  (f_m : stn l → T m)
  (f_n : stn m → T n)
  : (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n)
  := pr12 T l m n f_l f_m f_n.

Definition pr_comp
  (T : algebraic_theory)
  {m n : nat}
  (i : stn m)
  (f : stn m → T n)
  : (pr i) • f = f i
  := pr122 T m n i f.

Definition comp_pr
  (T : algebraic_theory)
  {n : nat}
  (f : T n)
  : f • pr = f
  := pr222 T n f.

(** * 2. Some useful properties and definitions *)

Definition lift_constant {T : algebraic_theory_data} (n : nat) (f : (T 0 : hSet))
  : (T n : hSet)
  := f • (weqvecfun _ vnil).
