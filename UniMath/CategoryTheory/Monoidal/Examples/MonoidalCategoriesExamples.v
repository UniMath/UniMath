Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.


(*
A monoidal monad is a monad in the bicategory of monoidal categories. More explicitely:
A monoidal monad is a monad whose underlying (endo)functor is lax monoidal such that the unit and multiplication are monoidal transformations.
*)
Section MonoidalMonad.

  Context {C : category}
          {M : monoidal C}
          {T : Monad C}.

  Definition MoMonadFunctor (M : monoidal C) (T : Monad C) : UU := fmonoidal M M T.

  (* Definition MonadFunctor : UU := MoMonadFunctor × MoMonadMult × MoMonadUnit. *)

End MonoidalMonad.

(*
Given a monoidal monad, its Kleisli category naturally carries a monoidal structure,
if the (underlying functor of the) monoidal monad is strong (resp. strict), then
is the projection functor strong (resp. strict) monoidal.
 *)

Section MonoidalAlgebras.

  Context {C : category}
          {M : monoidal C}
          {T : Monad C}
          {TM : MoMonadFunctor M T}.

  Local Notation "pt_{ T }" := (fmonoidal_preservestensordata (TM : fmonoidal M M (pr11 T))) (at level 31).

  Context {pts : preserves_tensor_strongly (pt_{T})}.

  Definition tensor_of_algebras (x y : Algebra_data T) : Algebra_data T.
    (* := (((pr1 x) ⊗_{M} (pr1 y)),, (pr1 (pts (pr1 x) (pr1 y)) · (pr2 x ⊗^{M} pr2 y))). *)
  Proof.
    use tpair.
    - exact ((pr1 x) ⊗_{M} (pr1 y)).
    - exact (pr1 (pts (pr1 x) (pr1 y)) · (pr2 x ⊗^{M} pr2 y)).
  Defined.

  Definition MonadAlg_tensor_data : bifunctor_data (MonadAlg T) (MonadAlg T) (MonadAlg T).
  Proof.
    repeat (use tpair).
    - intros x y.
      use tpair.
      + exact (tensor_of_algebras (pr1 x) (pr1 y)).
      + use tpair.
        * cbn in *.






End MonoidalAlgebras.





Section MonoidalKleisliCat.

  Context {C : category}
          {M : monoidal C}
          {T : Monad C}
          {TM : MoMonadFunctor M T}.

  Local Notation "μ_{ x }" := (pr2 (pr11 T) x).
  Local Notation "η_{ x }" := ((pr21 T) x).

  Local Notation "pt_{ T }" := (fmonoidal_preservestensordata (TM : fmonoidal M M (pr11 T))) (at level 31).
  Local Notation "pt_{ x , y }" := (fmonoidal_preservestensordata (TM : fmonoidal M M (pr11 T)) x y) (at level 31).
  Local Notation pu := (fmonoidal_preservesunit (TM : fmonoidal M M (pr11 T))).

  Local Notation "K_{ T }" := (Kleisli_cat_monad T).
  Local Notation "π_{ T }" := (Right_Kleisli_functor T).


  Local Notation "F_{ T }" := (pr1 (pr11 T)). (* Underlying functor of monad *)

  Definition Kleisli_cat_tensor_data : bifunctor_data K_{T} K_{T} K_{T}.
  Proof.
    repeat (use tpair).
    - intros x y.
      exact (x ⊗_{M} y).
    - intros x y1 y2 g.
      exact (((identity x) ⊗^{M} g) · pt_{x,y2}).
    - intros y x1 x2 f.
      exact ((f ⊗^{M} (identity y)) · pt_{x2,y}).
  Defined.

  Definition Kleisli_cat_tensor_laws : is_bifunctor Kleisli_cat_tensor_data.
  Proof.
    repeat (use tpair).
    - intros x y.
      admit.
    - intros x y.
      admit.
    - intros x1 x2 x3 x4 f g.
      admit.
    - intros x1 x2 x3 x4 f g.
      admit.
    - intros x1 x2 y1 y2 f g.
      admit.
  Admitted.

  Definition Kleisli_cat_tensor : tensor K_{T} := (Kleisli_cat_tensor_data,, Kleisli_cat_tensor_laws).

  Definition Kleisli_cat_monoidal_data : monoidal_data K_{T}.
  Proof.
    use make_monoidal_data.
    - exact (Kleisli_cat_tensor).
    - exact (I_{M}).
    - exact (λ x, lu^{M}_{x} · η_{x}).
    - exact (λ x, ru^{M}_{x} · η_{x}).
    - exact (λ x y z, α^{M}_{x,y,z} · η_{x ⊗_{M} (y ⊗_{M} z)}).
  Defined.

  Definition Kleisli_cat_monoidal_laws : monoidal_laws Kleisli_cat_monoidal_data.
  Proof.
    repeat (use tpair).
  Admitted.

  Definition Kleisli_cat_monoidal : monoidal K_{T}
    := (Kleisli_cat_monoidal_data,, Kleisli_cat_monoidal_laws).

  Definition Kleisli_cat_projection_preserves_tensor_data
    : preserves_tensordata Kleisli_cat_monoidal M π_{T}
    := λ x y, pt_{x,y}.

  Definition Kleisli_cat_projection_preserves_unit
    : preserves_unit Kleisli_cat_monoidal M π_{T} := pu.

  Definition Kleisli_cat_projection_fmonoidal_data
    : fmonoidal_data Kleisli_cat_monoidal M π_{T}
    := (Kleisli_cat_projection_preserves_tensor_data,, Kleisli_cat_projection_preserves_unit).

  Definition Kleisli_cat_projection_laxlaws
    : fmonoidal_laxlaws Kleisli_cat_projection_fmonoidal_data.
  Proof.
    repeat (use tpair).
  Admitted.

  Definition Kleisli_cat_projection_lax
    : fmonoidal_lax Kleisli_cat_monoidal M π_{T}
    := (Kleisli_cat_projection_fmonoidal_data,, Kleisli_cat_projection_laxlaws).

  Check pt_{T}.

  Definition Kleisli_cat_projection_preserves_tensor_strict
             (pts : preserves_tensor_strictly (pt_{T}))
    : preserves_tensor_strictly Kleisli_cat_projection_preserves_tensor_data.
  Proof.
    intros x y.
    use tpair.
    - apply pts.
    - apply pts.
  Qed.

  Definition Kleisli_cat_projection_preserves_unit_strict
             (pus : preserves_unit_strictly (pu))
    : preserves_unit_strictly Kleisli_cat_projection_preserves_unit.
  Proof.
    use tpair.
    - apply pus.
    - apply pus.
  Qed.
