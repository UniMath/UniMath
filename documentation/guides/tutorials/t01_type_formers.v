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

Definition quadruple
  : nat → nat
  := nat_rect _
    O                         (* The base case *)
    (λ n x, S (S (S (S x)))). (* The induction step: if `double n` gives `x`, double (n + 1) should give x + 2 *)

Lemma double_sn
  (n : nat)
  : double (double n) = quadruple n.
Proof.
  induction n as [ | n IHn ].
  - reflexivity. (* This shows that double (double 0) = quadruple 0 *)
  - simpl.       (* This simplifies double (double (S n)) to S (S (S (S (double n)))) *)
    rewrite IHn. (* This replaces (double (double n)) by quadruple n *)
    reflexivity. (* This shows that S (S (S (S (quadruple n)))) = S (S (S (S (quadruple n)))) *)
Qed.

Definition coprod_swap
  (X Y : UU)
  : X ⨿ Y → Y ⨿ X
  := coprod_rect _
    (λ x, inr x)    (* coprod_swap (inl x) = inr x *)
    (λ y, inl y).   (* coprod_swap (inr y) = inl y *)

Lemma coprod_swap_twice
  (X Y : UU)
  (u : X ⨿ Y)
  : coprod_swap Y X (coprod_swap X Y u) = u.
Proof.
  induction u as [x | y].
  - reflexivity. (* This shows that coprod_swap _ _ (coprod_swap _ _ (inl x)) = inl x *)
  - reflexivity. (* This shows that coprod_swap _ _ (coprod_swap _ _ (inr y)) = inr y *)
Qed.

Definition bool_idpath
  : bool = bool
  := idpath _.

Lemma path_symmetry
  (X : UU)
  (x y : X)
  (p : x = y)
  : y = x.
Proof.
  induction p. (* This removes y from the context and replaces it by x everywhere *)
  exact (idpath x).
Qed.

Definition equal_term
  (X : UU)
  (x : X)
  : UU
  := ∑ (y : X), y = x.

Definition identity_equal_term
  (X : UU)
  (x : X)
  : equal_term X x
  := x ,, idpath x.

Definition equal_term_term
  (X : UU)
  (x : X)
  (y : equal_term X x)
  : X.
Proof.
  induction y as [y p]. (* Gives y : X and p : x = y *)
  exact y.
Defined.

Definition equal_term_equality
  (X : UU)
  (x : X)
  (y : equal_term X x)
  : equal_term_term X x y = x
  := pr2 y.

Definition all_terms_are_equal
  (X : UU)
  (x : X)
  : UU
  := ∏ (y : X), y = x.

Definition all_terms_are_equal_unit
  : all_terms_are_equal unit tt.
Proof.
  intro t.      (* This turns the goal into t = tt *)
  induction t.  (* This replaces t by tt *)
  reflexivity.
Defined.

Lemma all_terms_are_equal_fun
  (X Y : UU)
  (x : X)
  (H : all_terms_are_equal X x)
  (f : X → Y)
  (y z : X)
  : f y = f z.
Proof.
  pose (H y) as Hy. (* This adds Hy : y = x to the context *)
  rewrite Hy.       (* This rewrites f y to f x *)
  pose (H z) as Hz. (* This adds Hz : z = x to the context *)
  rewrite Hz.       (* This rewrites f z to f x *)
  reflexivity.      (* This shows that f x = f x *)
Qed.
