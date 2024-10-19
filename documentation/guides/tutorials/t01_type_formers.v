Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Definition constant_function
  (X Y : UU)
  (y : Y)
  : X → Y.
Proof.
  intro x. (* This adds x : X to the context and transforms the goal from X → Y to Y *)
  exact y.
Defined.

Definition apply_function
  (X Y : UU)
  (f : X → Y)
  (x : X)
  : Y.
Proof.
  apply f. (* This turns the goal from Y into X *)
  exact x.
Defined.

Definition apply_function'
  (X Y : UU)
  (f : X → Y)
  (x : X)
  : Y
  := f x.

Definition neg
  (b : bool)
  : bool.
Proof.
  use (bool_rect _ _ _ b). (* This branches the proof into a branch for when b is true, and a branch for when b is false *)
  - exact false. (* The value for when b is true *)
  - exact true. (* The value for when b is false *)
Defined.

Lemma t_is_tt
  (x : unit)
  : x = tt.
Proof.
  use (unit_rect (λ y, y = tt) _ x). (* This changes the goal from x = tt to tt = tt *)
  reflexivity. (* This solves any goal of the form a = a *)
Qed.

Lemma true_is_false
  (e : ∅)
  : true = false.
Proof.
  use (empty_rect _ e). (* This immediately solves any goal *)
Qed.

Definition neg'
  (b : bool)
  : bool.
Proof.
  induction b. (* This branches the proof into a branch for when b is true, and a branch for when b is false *)
  - exact false. (* The value for when b is true *)
  - exact true. (* The value for when b is false *)
Defined.

Lemma t_is_tt'
  (x : unit)
  : x = tt.
Proof.
  induction x. (* This changes the goal from x = tt to tt = tt *)
  reflexivity. (* This solves any goal of the form a = a *)
Qed.

Lemma true_is_false'
  (e : ∅)
  : true = false.
Proof.
  induction e. (* This immediately solves any goal *)
Qed.

Definition dirprod_pr1'
  (X Y : UU)
  (p : X × Y)
  : X.
Proof.
  induction p as [x y]. (* The [x y] part tells coq what names we want to give to the two parts *)
  exact x.
Defined.

Definition dirprod_pr2'
  (X Y : UU)
  (p : X × Y)
  : Y.
Proof.
  exact (dirprod_pr2 p).
Defined.

Definition double
  : nat → nat
  := nat_rect _
    O                 (* The base case *)
    (λ n x, S (S x)). (* The induction step: if `double n` gives `x`, double (n + 1) should give x + 2 *)

Lemma double_sn
  (n : nat)
  : double (S n) = S (S (double n)).
Proof.
  induction n.
  - reflexivity. (* This shows that 2 = 2 *)
  - reflexivity. (* This shows that S (S (S (S (double n)))) = S (S (S (S (double n)))) *)
Qed.
