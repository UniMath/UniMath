(** an elementary direct construction of the monoidal category

    one can also instantiate the construction of cartesian monoidal categories
    [UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.SET_cartesian_monoidal] *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Require Import UniMath.CategoryTheory.categories.HSET.All.

Local Open Scope cat.


Section SetIsCartesianMonoidal.

  Definition SET_cart_tensor_data : bifunctor_data SET SET SET.
  Proof.
    repeat (use tpair).
    - intros x y.
      exact (((pr1 x × pr1 y),, isaset_dirprod (pr2 x) (pr2 y))).
    - intros x y1 y2 g a.
      exact (pr1 a,, g (pr2 a)).
    - intros y x1 x2 f b.
      exact (f (pr1 b),, pr2 b).
  Defined.

  Lemma SET_cart_tensor_laws : is_bifunctor SET_cart_tensor_data.
  Proof.
    repeat split.
  Qed.

  Definition SET_cart_tensor : tensor SET := (SET_cart_tensor_data,, SET_cart_tensor_laws).
  Definition SET_cart_monoidal_data : monoidal_data SET.
  Proof.
    use make_monoidal_data.
    - exact (SET_cart_tensor).
    - exact (unit,, isasetunit).
    - exact (λ _ y, pr2 y).
    - exact (λ _ y, (tt,, y)).
    - exact (λ _ y, pr1 y).
    - exact (λ _ y, (y,, tt)).
    - intros x y z a.
      induction a as [[xx yy] zz].
      exact (xx,, (yy,,zz)).
    - intros x y z a.
      induction a as [xx [yy zz]].
      exact ((xx,, yy),,zz).
  Defined.

  Lemma SET_cart_monoidal_laws : monoidal_laws SET_cart_monoidal_data.
  Proof.
    repeat split.
    - apply funextsec; intro a; induction a as [t a]; induction t; apply idpath.
    - apply funextsec; intro a; induction a as [a t]; induction t; apply idpath.
  Qed.


  Definition SET_cart_monoidal : monoidal SET
    := (SET_cart_monoidal_data,, SET_cart_monoidal_laws).

End SetIsCartesianMonoidal.
