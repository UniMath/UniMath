Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Definition binop
  (X : UU)
  : UU
  := X → X → X.

Definition is_assoc
  (X : UU)
  (o : binop X)
  : UU
  := ∏ x y z, o (o x y) z = o x (o y z). (* Associativity means that the order of operations in x ∘ y ∘ z does not matter *)

Definition transfer_binop
  (X Y : UU)
  (f : X ≃ Y)
  : binop Y → binop X.
Proof.
  intros o x y.         (* This changes the goal to `X` *)
  apply (invmap f).     (* This changes the goal to `Y` *)
  refine (o _ _).       (* This gives the goals `Y` and `Y` *)
  - apply f.            (* This changes the goal to `X` *)
    exact x.
  - apply f.
    exact y.
Defined.

Lemma transfer_binop_is_assoc
  (X Y : UU)
  (f : X ≃ Y)
  (o : binop Y)
  : is_assoc Y o → is_assoc X (transfer_binop X Y f o).
Proof.
  intros H x y z.
  unfold transfer_binop.
  rewrite !(homotweqinvweq f).    (* This changes f (invmap f ...) to ... as many times as possible, which is two in this case *)
  apply (maponpaths (invmap f)).  (* This changes the goal to o (o (f x) (f y)) (f z) = o (f x) (o (f y) (f z)) *)
  apply H.
Qed.

Definition coprod_swap_weq
  (X Y : UU)
  : X ⨿ Y ≃ Y ⨿ X.
Proof.
  use make_weq.
  - intro xy.                   (* This brings xy : X ⨿ Y into the context *)
    induction xy as [x | y].
    + exact (inr x).            (* We send inl x to inr x *)
    + exact (inl y).            (* We send inr y to inl y *)
  - use isweq_iso.
    + intro yx.                 (* This brings yx : Y ⨿ X into the context *)
      induction yx as [y | x].
      * exact (inr y).          (* We send inl y to inr y *)
      * exact (inl x).          (* We send inr x to inl x *)
    + intro xy.
      induction xy as [x | y];  (* This splits up the goal in a case for inl x and inr y, *)
        reflexivity.            (* Both of which are trivial *)
    + intro yx.
      induction yx as [y | x];
        reflexivity.
Defined.
