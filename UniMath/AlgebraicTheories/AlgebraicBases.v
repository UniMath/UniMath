Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Declare Scope algebraic_theory.

Definition algebraic_base := ∑ (B: nat → hSet), (∏ m n, B m → (stn m → B n) → B n).

Definition function_from_algebraic_base (B : algebraic_base) : (nat → hSet) := pr1 B.
Coercion function_from_algebraic_base : algebraic_base >-> Funclass.

Definition comp {B : algebraic_base} {m n : nat} : (B m → (stn m → B n) → B n) := pr2 B m n.

Notation "f • g" :=
  (comp f g)
  (at level 50) : algebraic_theory.

Definition make_algebraic_base (B : nat → hSet) (comp : ∏ m n, B m → (stn m → B n) → B n) : algebraic_base := (B ,, comp).