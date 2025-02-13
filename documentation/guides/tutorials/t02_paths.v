Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Lemma path_inv_transitivity
  (X : UU)
  (x y z : X)
  (p : x = y)
  (q : y = z)
  : z = x.
Proof.
  symmetry.       (* This turns the goal into x = z *)
  transitivity y. (* This splits the goal into x = y and y = z *)
  - exact p.
  - exact q.
Qed.

Definition path_inv_transitivity'
  (X : UU)
  (x y z : X)
  (p : x = y)
  (q : y = z)
  : z = x
  := !(p @ q).

Lemma postcompose_path_path
  (X : UU)
  (x y z : X)
  (p q : x = y)
  (r : y = z)
  (H : p = q)
  : p @ r = q @ r.
Proof.
  apply (maponpaths (λ e, e @ r)).
  exact H.
Defined.

Lemma compose_path_path
  (X : UU)
  (x y z : X)
  (p q : x = y)
  (r s : y = z)
  (H1 : p = q)
  (H2 : r = s)
  : p @ r = q @ s.
Proof.
  apply maponpaths_12.
  - exact H1.
  - exact H2.
Defined.

Lemma isaprop_function_to_unit
  (X : UU)
  (f g : X → unit)
  : f = g.
Proof.
  apply funextfun.        (* This changes the goal to ∏ x, f x = g x *)
  intro x.
  induction (f x), (g x). (* This replaces f x and g x by tt *)
  reflexivity.
Qed.

Lemma function_value_path
  (X : UU)
  (f : X → unit)
  (x : X)
  : f x = tt.
Proof.
  apply (eqtohomot (g := λ _, tt)). (* This changes the goal to f = (λ _, tt) *)
  apply (isaprop_function_to_unit).
Qed.

Lemma function_value_path'
  (X : UU)
  (f : X → unit)
  (x : X)
  : f x = tt.
Proof.
  induction (f x).
  reflexivity.
Qed.

Lemma isaprop_unit_pair
  (x y : unit × unit)
  : x = y.
Proof.
  apply dirprodeq.              (* This splits up the goal into pr1 x = pr1 y and pr2 x = pr2 y *)
  - induction (pr1 x), (pr1 y).
    reflexivity.
  - induction (pr2 x), (pr2 y).
    reflexivity.
Qed.

Definition combine_dependent_sum_paths
  (X : UU)
  (Y : X → UU)
  (x x' : X)
  (y : Y x)
  (y' : Y x')
  (H : ∑ (Hx : x = x'), transportf Y Hx y = y')
  : (x ,, y) = (x' ,, y').
Proof.
  induction H as [Hx Hy].
  use total2_paths_f.
  - exact Hx.
  - exact Hy.
Defined.

Definition split_dependent_sum_paths
  (X : UU)
  (Y : X → UU)
  (x x' : X)
  (y : Y x)
  (y' : Y x')
  (H : (x ,, y) = (x' ,, y'))
  : ∑ (H : x = x'), transportf Y H y = y'.
Proof.
  use tpair.
  - exact (base_paths (x ,, y) (x' ,, y') H).
  - exact (fiber_paths H).
Defined.

Lemma isaprop_iscontr
  (X : hSet)
  (x x' : ∑ (x : X), (∏ y, y = x))
  : x = x'.
Proof.
  apply subtypePath.      (* This splits the goal into `isPredicate is_even` and `pr1 m = pr1 m'` *)
  - intro y.              (* This changes the goal to `isaprop (∏ y', y' = y)` *)
    apply impred_isaprop. (* This uses a lemma to swap the `isaprop` with the `∏ y'` *)
    intro y'.
    apply setproperty.    (* This uses the fact that `X` is a set, so that `y' = y` is a proposition *)
  - apply (pr2 x').
Qed.

Definition isaprop_empty_product (P : empty -> UU)
  (f g : (∏ x, P x))
  : f = g.
Proof.
  apply funextsec.
  intro x.
  induction x.
Qed.
