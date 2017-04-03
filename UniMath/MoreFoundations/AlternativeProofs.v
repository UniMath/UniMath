Require Export UniMath.MoreFoundations.Notations.

(** ** An alternative proof of [total2_paths_equiv] *)

Theorem total2_paths_equiv' {A : UU} (B : A -> UU) (x y : ∑ x, B x) :
  x = y  ≃  x ╝ y.
Proof.
  simple refine (weqtotaltofib _ _ _ _ _).
  - intros z p. exists (maponpaths pr1 p). induction p. reflexivity.
  - apply isweqcontrcontr.
    + apply iscontrcoconusfromt.
    + exists (x ,, idpath _ ,, idpath _).
      intro w. induction w as [w p], w as [a b], p as [p q], x as [a' b'], (p:a' = a), (q:b' = b).
      reflexivity.
Defined.

Lemma total2_paths_equiv'_compute {A : UU} (B : A -> UU) (x y : ∑ x, B x) :
  pr1weq (total2_paths_equiv' B x y) = (λ (r : x = y), base_paths _ _ r ,, fiber_paths r).
Proof.
  reflexivity.
Defined.
